module

import all CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6UnitaryFourDefs
public import Mathlib.Tactic.Polynomial.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module Matrix CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section General

variable {R : Type*} [CommRing R]

@[expose] def pairFst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

@[expose] def pairSnd : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

@[expose] def ext2 (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun p q => A (pairFst p) (pairFst q) * A (pairSnd p) (pairSnd q) -
    A (pairFst p) (pairSnd q) * A (pairSnd p) (pairFst q)

@[expose] def wedgePairing : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]

@[expose] def pfSigned (x : Fin 6 → R) : R := x 0 * x 5 - x 1 * x 4 + x 2 * x 3

theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) : A.det =
    A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) +
      A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1)) -
    A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0) +
      A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)) +
    A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) - A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0) +
      A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) -
    A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1) - A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0) +
      A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.succ]
  ring

theorem ext2_mul (A B : Matrix (Fin 4) (Fin 4) R) : ext2 (A * B) = ext2 A * ext2 B := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [ext2, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six, pairFst, pairSnd] <;> ring

theorem ext2_one : ext2 (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [ext2, pairFst, pairSnd, Matrix.one_apply]

theorem ext2_transpose (A : Matrix (Fin 4) (Fin 4) R) : ext2 Aᵀ = (ext2 A)ᵀ := by
  ext p q
  simp only [ext2, Matrix.of_apply, Matrix.transpose_apply]
  ring

theorem ext2_map {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R) :
    ext2 (A.map f) = (ext2 A).map f := by
  ext p q
  simp [ext2, map_sub, map_mul]

theorem gram_ext2 (A : Matrix (Fin 4) (Fin 4) R) :
    (ext2 A)ᵀ * wedgePairing * ext2 A = A.det • wedgePairing := by
  rw [det_fin_four]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [ext2, wedgePairing, Matrix.mul_apply, Fin.sum_univ_six, pairFst, pairSnd] <;> ring

theorem pfSigned_ext2 (A : Matrix (Fin 4) (Fin 4) R) (x : Fin 6 → R) :
    pfSigned (ext2 A *ᵥ x) = A.det * pfSigned x := by
  rw [det_fin_four]
  simp only [pfSigned, ext2, Matrix.mulVec, dotProduct, Fin.sum_univ_six, Matrix.of_apply,
    pairFst, pairSnd]
  simp
  ring

end General

theorem wedge_eq (u v : V) :
    wedge u v = fun p => u (pairFst p) * v (pairSnd p) - u (pairSnd p) * v (pairFst p) := by
  funext p
  fin_cases p <;> rfl

theorem ext2_mulVec_wedge (A : Matrix (Fin 4) (Fin 4) K) (u v : V) :
    ext2 A *ᵥ wedge u v = wedge (A *ᵥ u) (A *ᵥ v) := by
  rw [wedge_eq, wedge_eq]
  funext p
  fin_cases p <;>
    simp [ext2, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_six, pairFst,
      pairSnd] <;> ring

theorem neg_K (a : K) : -a = a := by revert a; decide

theorem Pf_eq_pfSigned (x : W) : Pf x = pfSigned x := by
  rw [Pf, pfSigned, sub_eq_add_neg, neg_K]

theorem Pf_ext2 (A : Matrix (Fin 4) (Fin 4) K) (x : W) : Pf (ext2 A *ᵥ x) = A.det * Pf x := by
  rw [Pf_eq_pfSigned, Pf_eq_pfSigned, pfSigned_ext2]

@[expose] def barHom : K →+* K where
  toFun := bar
  map_one' := bar_one
  map_mul' := bar_mul
  map_zero' := bar_zero
  map_add' := bar_add

theorem barHom_apply (a : K) : barHom a = bar a := rfl

@[expose] def hermJ : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if (i : ℕ) + j = 3 then 1 else 0

theorem herm_eq_dotProduct (v w : V) : herm v w = v ⬝ᵥ (hermJ *ᵥ fun i => bar (w i)) := by
  simp [herm, hermJ, dotProduct, Matrix.mulVec, Fin.sum_univ_four]

@[expose] def swapMatrix : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun p q => if q = Equiv.swap (2 : Fin 6) 3 p then 1 else 0

theorem T_eq_mulVec (x : W) : T x = swapMatrix *ᵥ fun p => bar (x p) := by
  funext p
  fin_cases p <;> simp [T_apply, swapMatrix, Matrix.mulVec, dotProduct, Equiv.swap_apply_def]

theorem ext2_hermJ : ext2 hermJ = wedgePairing * swapMatrix := by decide

theorem wedgePairing_mul_self : (wedgePairing : Matrix (Fin 6) (Fin 6) K) * wedgePairing = 1 := by
  decide

@[expose] def SU : Subgroup (GL (Fin 4) K) where
  carrier := {g | (g : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
    ∀ v w, herm ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ v) ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ w) =
      herm v w}
  mul_mem' {g g'} hg hg' := by
    refine ⟨?_, fun v w => ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hg.1, hg'.1, one_mul]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg.2, hg'.2]
  one_mem' := ⟨by simp, fun v w => by simp⟩
  inv_mem' {g} hg := by
    have hinv : ∀ v, (g : Matrix (Fin 4) (Fin 4) K) *ᵥ (((g⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) *ᵥ v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    refine ⟨?_, fun v w => ?_⟩
    · have h := Matrix.det_mul (g : Matrix (Fin 4) (Fin 4) K) ((g⁻¹ : GL (Fin 4) K) : _)
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, hg.1, one_mul] at h
      exact h.symm
    · rw [← hg.2, hinv, hinv]

theorem mem_SU {g : GL (Fin 4) K} : g ∈ SU ↔ (g : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
    ∀ v w, herm ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ v) ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ w) =
      herm v w :=
  Iff.rfl

theorem single_bar (a : Fin 4) : (fun i => bar ((Pi.single a 1 : V) i)) = Pi.single a 1 := by
  funext i
  by_cases h : i = a
  · subst h
    simp [bar_one]
  · simp [h, bar_zero]

theorem transpose_mul_hermJ_mul {g : Matrix (Fin 4) (Fin 4) K}
    (hg : ∀ v w, herm (g *ᵥ v) (g *ᵥ w) = herm v w) : gᵀ * hermJ * g.map bar = hermJ := by
  have hbar : ∀ w : V, (fun i => bar ((g *ᵥ w) i)) = g.map bar *ᵥ fun i => bar (w i) :=
    fun w => funext fun i => RingHom.map_mulVec barHom g w i
  have key : ∀ v w, herm (g *ᵥ v) (g *ᵥ w) =
      v ⬝ᵥ ((gᵀ * hermJ * g.map bar) *ᵥ fun i => bar (w i)) := by
    intro v w
    rw [herm_eq_dotProduct, hbar, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
  ext a b
  have h := hg (Pi.single a 1) (Pi.single b 1)
  rw [key, herm_eq_dotProduct, single_bar] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

abbrev ext2GL (g : GL (Fin 4) K) : Matrix (Fin 6) (Fin 6) K := ext2 (g : Matrix (Fin 4) (Fin 4) K)

theorem ext2GL_inv_mul (g : GL (Fin 4) K) : ext2GL g⁻¹ * ext2GL g = 1 := by
  rw [ext2GL, ext2GL, ← ext2_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ext2_one]

theorem ext2GL_mul_inv (g : GL (Fin 4) K) : ext2GL g * ext2GL g⁻¹ = 1 := by
  rw [ext2GL, ext2GL, ← ext2_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ext2_one]

theorem ext2GL_injective (g : GL (Fin 4) K) : Function.Injective (ext2GL g *ᵥ ·) := by
  intro x y h
  have := congrArg (ext2GL g⁻¹ *ᵥ ·) h
  simp only [Matrix.mulVec_mulVec, ext2GL_inv_mul, Matrix.one_mulVec] at this
  exact this

theorem swap_mul_map_bar {g : GL (Fin 4) K} (hg : g ∈ SU) :
    swapMatrix * (ext2GL g).map bar = ext2GL g * swapMatrix := by
  set G := ext2GL g
  have h1 : Gᵀ * wedgePairing * G = wedgePairing := by
    rw [gram_ext2, hg.1, one_smul]
  have h2 : Gᵀ * (wedgePairing * swapMatrix) * G.map bar = wedgePairing * swapMatrix := by
    have := congrArg ext2 (transpose_mul_hermJ_mul hg.2)
    rwa [ext2_mul, ext2_mul, ext2_transpose, ext2_hermJ,
      show ext2 ((g : Matrix (Fin 4) (Fin 4) K).map bar) = G.map bar from ext2_map barHom _] at this
  have hinvl : (wedgePairing * (ext2GL g⁻¹)ᵀ) * (Gᵀ * wedgePairing) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (ext2GL g⁻¹)ᵀ, ← Matrix.transpose_mul,
      ext2GL_mul_inv, Matrix.transpose_one, Matrix.one_mul, wedgePairing_mul_self]
  have h3 : (Gᵀ * wedgePairing) * (swapMatrix * G.map bar) =
      (Gᵀ * wedgePairing) * (G * swapMatrix) := by
    calc (Gᵀ * wedgePairing) * (swapMatrix * G.map bar)
        = Gᵀ * (wedgePairing * swapMatrix) * G.map bar := by simp only [Matrix.mul_assoc]
      _ = wedgePairing * swapMatrix := h2
      _ = (Gᵀ * wedgePairing * G) * swapMatrix := by rw [h1]
      _ = (Gᵀ * wedgePairing) * (G * swapMatrix) := by simp only [Matrix.mul_assoc]
  calc swapMatrix * G.map bar
      = ((wedgePairing * (ext2GL g⁻¹)ᵀ) * (Gᵀ * wedgePairing)) * (swapMatrix * G.map bar) := by
        rw [hinvl, Matrix.one_mul]
    _ = (wedgePairing * (ext2GL g⁻¹)ᵀ) * ((Gᵀ * wedgePairing) * (G * swapMatrix)) := by
        rw [Matrix.mul_assoc, h3]
    _ = G * swapMatrix := by rw [← Matrix.mul_assoc, hinvl, Matrix.one_mul]

theorem T_ext2 {g : GL (Fin 4) K} (hg : g ∈ SU) (x : W) :
    T (ext2GL g *ᵥ x) = ext2GL g *ᵥ T x := by
  rw [T_eq_mulVec, T_eq_mulVec, Matrix.mulVec_mulVec, ← swap_mul_map_bar hg,
    ← Matrix.mulVec_mulVec]
  congr 1
  funext p
  exact RingHom.map_mulVec barHom (ext2GL g) x p

theorem Pf_ext2GL {g : GL (Fin 4) K} (hg : g ∈ SU) (x : W) : Pf (ext2GL g *ᵥ x) = Pf x := by
  rw [Pf_ext2, hg.1, one_mul]

theorem ext2GL_mem_W₀ {g : GL (Fin 4) K} (hg : g ∈ SU) {x : W} (hx : x ∈ W₀) :
    ext2GL g *ᵥ x ∈ W₀ := by
  rw [mem_W₀] at hx ⊢
  rw [T_ext2 hg, hx]

end CFSG.LieType.Chevalley.C2E6Overlap
