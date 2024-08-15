CC = g++
FLAGS = --std=c++11
EXEC = solver

all:
	@echo "Compiling solver"
	$(CC) $(FLAGS) solver.cpp -o $(EXEC)
	@echo "Done."

clean:
	@echo "Cleaning up..."
	rm $(EXEC)
	@echo "Done."
