
ply-image: ply-image.c ply-frame-buffer.c Makefile
	$(CC) $(CFLAGS) -Wl,-Bstatic `pkg-config --cflags libpng`  ply-image.c ply-frame-buffer.c -o ply-image  -lm `pkg-config --libs libpng` -lm -lz -Wl,-Bdynamic -lc $(LDFLAGS)
	
clean:
	rm -f ply-image *~ gmon.out
	
install: ply-image
	mkdir -p $(DESTDIR)/usr/bin	
	mkdir -p $(DESTDIR)/usr/share/plymouth
	cp ply-image $(DESTDIR)/usr/bin
	cp splash.png $(DESTDIR)/usr/share/plymouth/splash.png
	
