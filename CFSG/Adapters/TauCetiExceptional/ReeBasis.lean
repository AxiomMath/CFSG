module

public import TauCeti.Algebra.Lie.G2.ShortRoot.AdmissibleLattice
public import CFSG.Quasithin.Background.G2URoots

public section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

@[expose] def tcE : Fin 2 ⊕ Fin 2 → Matrix (Fin 7) (Fin 7) ℤ
  | .inl i => TauCeti.G2ShortRoot.raisingMatrix i
  | .inr i => TauCeti.G2ShortRoot.loweringMatrix i

@[expose] def tcE2 : Fin 2 ⊕ Fin 2 → Matrix (Fin 7) (Fin 7) ℤ
  | .inl i => ![Matrix.single 2 4 1, 0] i
  | .inr i => ![Matrix.single 4 2 1, 0] i

theorem rootMatrix_eq_tcE (k : Fin 2 ⊕ Fin 2) : TauCeti.G2ShortRoot.rootMatrix k = tcE k := by
  rcases k with i | i
  · exact TauCeti.G2ShortRoot.rootMatrix_inl i
  · exact TauCeti.G2ShortRoot.rootMatrix_inr i

theorem rootDividedSquareMatrix_eq_tcE2 (k : Fin 2 ⊕ Fin 2) :
    TauCeti.G2ShortRoot.rootDividedSquareMatrix k = tcE2 k := by
  rcases k with i | i
  · exact TauCeti.G2ShortRoot.rootDividedSquareMatrix_inl i
  · exact TauCeti.G2ShortRoot.rootDividedSquareMatrix_inr i

@[expose] def nodeMap : Fin 2 → Fin Tag.G2.rank :=
  ![ix 1, ix 0]

@[expose] def basisMat : Fin 14 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 0, 0, 0, 0, -1, 0;
       0, 0, 0, 0, 0, 0, -1;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, -1;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, -2, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, -1;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, -2, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, -1;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0],
    !![0, -1, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, -2, 0, 0, 0;
       0, 0, 0, 0, -1, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, -1;
       0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, -1, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0],
    !![1, 0, 0, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0;
       0, 0, 2, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, -2, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, -1],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, -1, 0, 0;
       0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 2, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 2, 0, 0, 0;
       0, 0, 0, 0, -1, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0;
       0, 0, -1, 0, 0, 0, 0;
       0, 0, 0, 2, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, -1, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0]]

@[expose] def coordW : Fin 14 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![-Matrix.single 0 5 1, Matrix.single 0 4 1, Matrix.single 1 4 1, Matrix.single 0 2 1,
    -Matrix.single 0 1 1, Matrix.single 1 2 1, -Matrix.single 0 0 1 - Matrix.single 1 1 1,
    Matrix.single 0 0 1, -Matrix.single 2 1 1, Matrix.single 1 0 1, Matrix.single 2 0 1,
    Matrix.single 3 0 1, Matrix.single 4 0 1, Matrix.single 5 0 1]

@[expose] def coord {R : Type*} [CommRing R] (s : Fin 14) (Y : Matrix (Fin 7) (Fin 7) R) : R :=
  ∑ r, ∑ c, (coordW s r c : R) * Y r c

theorem coord_basisMat : ∀ s t : Fin 14, coord s (basisMat t) = if s = t then 1 else 0 := by
  decide +kernel

variable {R : Type*} [CommRing R]

abbrev basisMatR (R : Type*) [CommRing R] (t : Fin 14) : Matrix (Fin 7) (Fin 7) R :=
  (basisMat t).map (Int.cast : ℤ → R)

theorem coord_add (s : Fin 14) (Y Z : Matrix (Fin 7) (Fin 7) R) :
    coord s (Y + Z) = coord s Y + coord s Z := by
  simp only [coord, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem coord_smul (s : Fin 14) (a : R) (Y : Matrix (Fin 7) (Fin 7) R) :
    coord s (a • Y) = a * coord s Y := by
  simp only [coord, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun c _ => by ring

theorem coord_sum {ι : Type*} (S : Finset ι) (s : Fin 14) (Y : ι → Matrix (Fin 7) (Fin 7) R) :
    coord s (∑ i ∈ S, Y i) = ∑ i ∈ S, coord s (Y i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coord]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coord_add, ih]

theorem map_coord {S : Type*} [CommRing S] (f : R →+* S) (s : Fin 14)
    (Y : Matrix (Fin 7) (Fin 7) R) : f (coord s Y) = coord s (Y.map f) := by
  simp only [coord, map_sum, map_mul, map_intCast, Matrix.map_apply]

theorem coord_basisMatR (s t : Fin 14) :
    coord s (basisMatR R t) = if s = t then 1 else 0 := by
  change coord s ((basisMat t).map (Int.castRingHom R)) = _
  rw [← map_coord (Int.castRingHom R), coord_basisMat]
  split_ifs <;> simp

theorem coord_sum_smul_basisMatR (a : Fin 14 → R) (s : Fin 14) :
    coord s (∑ t, a t • basisMatR R t) = a s := by
  rw [coord_sum]
  simp only [coord_smul, coord_basisMatR, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

@[expose] def InSpan (Y : Matrix (Fin 7) (Fin 7) R) : Prop :=
  ∃ a : Fin 14 → R, Y = ∑ t, a t • basisMatR R t

theorem InSpan.eq_sum {Y : Matrix (Fin 7) (Fin 7) R} (h : InSpan Y) :
    Y = ∑ t, coord t Y • basisMatR R t := by
  obtain ⟨a, rfl⟩ := h
  simp only [coord_sum_smul_basisMatR]

theorem inSpan_iff {Y : Matrix (Fin 7) (Fin 7) R} :
    InSpan Y ↔ Y = ∑ t, coord t Y • basisMatR R t :=
  ⟨InSpan.eq_sum, fun h => ⟨_, h⟩⟩

theorem inSpan_basisMatR (t : Fin 14) : InSpan (basisMatR R t) :=
  ⟨fun u => if u = t then 1 else 0, by simp [ite_smul]⟩

end CFSG.TauCetiBridge.Ree
