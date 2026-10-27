module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aGroup
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

section Invol

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem exists_basis_of_square_zero (N : Matrix (Fin 3) (Fin 3) F) (hN : N * N = 0)
    (hN0 : N ≠ 0) :
    ∃ v w x : Fin 3 → F, N *ᵥ w = v ∧ N *ᵥ v = 0 ∧ N *ᵥ x = 0 ∧
      LinearIndependent F ![v, w, x] := by
  let L : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := Matrix.mulVecLin N
  have hL : ∀ u, L u = N *ᵥ u := fun u => rfl
  have hL2 : ∀ u, L (L u) = 0 := fun u => by
    rw [hL, hL, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN0
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [hL, Matrix.mulVec_single_one] using this
  set v := L w with hvdef
  have hv0 : L v = 0 := hL2 w
  have hrange : LinearMap.range L ≤ LinearMap.ker L := by
    rintro _ ⟨u, rfl⟩
    exact hL2 u
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hle := Submodule.finrank_mono hrange
  have hpos : 0 < Module.finrank F (LinearMap.range L) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨v, w, rfl⟩, fun h => hw (by simpa using congrArg Subtype.val h)⟩
  have h3 : Module.finrank F (Fin 3 → F) = 3 := by simp
  have hker : Module.finrank F (LinearMap.ker L) = 2 := by omega
  have hspan : Submodule.span F {v} < LinearMap.ker L := by
    refine lt_of_le_of_ne ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hv0
    · intro h
      have := congrArg (fun S : Submodule F (Fin 3 → F) => Module.finrank F S) h
      rw [finrank_span_singleton hw, hker] at this
      omega
  obtain ⟨x, hxker, hxspan⟩ := IsConcreteLE.exists_of_lt hspan
  have hxL : L x = 0 := hxker
  refine ⟨v, w, x, rfl, hv0, hxL, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have h1 := congrArg L hg
  simp only [map_add, map_smul, hv0, hxL, smul_zero, zero_add, add_zero, map_zero] at h1
  have hg1 : g 1 = 0 := by
    have : g 1 • v = 0 := by simpa [hvdef] using h1
    exact (smul_eq_zero.mp this).resolve_right hw
  rw [hg1, zero_smul, add_zero] at hg
  have hg2 : g 2 = 0 := by
    by_contra hne
    apply hxspan
    rw [Submodule.mem_span_singleton]
    refine ⟨-(g 2)⁻¹ * g 0, ?_⟩
    have h5 : g 2 • x = -(g 0 • v) := eq_neg_of_add_eq_zero_right hg
    calc (-(g 2)⁻¹ * g 0) • v = (g 2)⁻¹ • (-(g 0 • v)) := by
          rw [smul_neg, neg_mul, neg_smul, smul_smul]
      _ = (g 2)⁻¹ • (g 2 • x) := by rw [h5]
      _ = x := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hg2, zero_smul, add_zero] at hg
  have hg0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hw
  fin_cases i <;> simp [hg0, hg1, hg2]

theorem exists_conj_transvection (t : SL(3, F)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ g : SL(3, F), g⁻¹ * t * g = up3 0 0 1 := by
  set T : Matrix (Fin 3) (Fin 3) F := (t : Matrix (Fin 3) (Fin 3) F) with hT
  set N : Matrix (Fin 3) (Fin 3) F := T - 1 with hN
  have hTT : T * T = 1 := by
    simpa using congrArg (fun s : SL(3, F) => (s : Matrix (Fin 3) (Fin 3) F)) ht2
  have hNN : N * N = 0 := by
    have h1 : N * N = T * T - T - T + 1 := by
      rw [hN]
      noncomm_ring
    rw [h1, hTT]
    have h2 : (1 : Matrix (Fin 3) (Fin 3) F) + 1 = 0 := by
      ext i j
      by_cases hij : i = j
      · simp [hij, CharTwo.add_self_eq_zero]
      · simp [hij]
    have h3 : T + T = 0 := by
      ext i j
      simp [CharTwo.add_self_eq_zero]
    calc (1 : Matrix (Fin 3) (Fin 3) F) - T - T + 1 = (1 + 1) - (T + T) := by abel
      _ = 0 := by rw [h2, h3, sub_zero]
  have hN0 : N ≠ 0 := by
    intro h
    apply ht1
    apply Subtype.ext
    rw [hN] at h
    simpa [sub_eq_zero] using h
  obtain ⟨v, w, x, hw, hv, hx, hli⟩ := exists_basis_of_square_zero N hNN hN0
  set g0 : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ![v, w, x] j i with hg0
  have hcols : LinearIndependent F (fun j => g0.col j) := by
    have : (fun j => g0.col j) = ![v, w, x] := by
      funext j
      ext i
      simp [hg0, Matrix.col_apply]
    rw [this]
    exact hli
  have hunit : IsUnit g0.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)
  set d : F := g0.det with hd
  have hd0 : d ≠ 0 := hunit.ne_zero
  set D : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, 1, d⁻¹] with hD
  set g : Matrix (Fin 3) (Fin 3) F := g0 * D with hg
  have hdet : g.det = 1 := by
    rw [hg, Matrix.det_mul, hD, Matrix.det_diagonal]
    simp [Fin.prod_univ_three, hd0, ← hd]
  let G : SL(3, F) := ⟨g, hdet⟩
  have hg0col : ∀ i, g i 0 = v i := fun i => by
    simp [hg, hg0, hD, Matrix.mul_diagonal]
  have hg1col : ∀ i, g i 1 = w i := fun i => by
    simp [hg, hg0, hD, Matrix.mul_diagonal]
  have hg2col : ∀ i, g i 2 = d⁻¹ * x i := fun i => by
    simp [hg, hg0, hD, Matrix.mul_diagonal, mul_comm]
  have hTN : T = N + 1 := by rw [hN]; abel
  have hTv : T *ᵥ v = v := by
    rw [hTN, Matrix.add_mulVec, hv, Matrix.one_mulVec, zero_add]
  have hTw : T *ᵥ w = v + w := by
    rw [hTN, Matrix.add_mulVec, hw, Matrix.one_mulVec]
  have hTx : T *ᵥ (fun k => d⁻¹ * x k) = fun k => d⁻¹ * x k := by
    have e : (fun k => d⁻¹ * x k) = d⁻¹ • x := rfl
    rw [e, Matrix.mulVec_smul, hTN, Matrix.add_mulVec, hx, Matrix.one_mulVec, zero_add]
  have key : T * g = g * upMat 0 0 1 := by
    ext i j
    fin_cases j
    · show (T * g : Matrix (Fin 3) (Fin 3) F) i 0 = (g * upMat (0 : F) 0 1 : Matrix (Fin 3) (Fin 3) F) i 0
      have h1 : (T * g) i 0 = (T *ᵥ v) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hg0col]
      rw [h1, hTv]
      simp [Matrix.mul_apply, Fin.sum_univ_three, upMat, hg0col]
    · show (T * g : Matrix (Fin 3) (Fin 3) F) i 1 = (g * upMat (0 : F) 0 1 : Matrix (Fin 3) (Fin 3) F) i 1
      have h1 : (T * g) i 1 = (T *ᵥ w) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hg1col]
      rw [h1, hTw]
      simp [Matrix.mul_apply, Fin.sum_univ_three, upMat, hg0col, hg1col]
    · show (T * g : Matrix (Fin 3) (Fin 3) F) i 2 = (g * upMat (0 : F) 0 1 : Matrix (Fin 3) (Fin 3) F) i 2
      have h1 : (T * g) i 2 = (T *ᵥ (fun k => d⁻¹ * x k)) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hg2col]
      rw [h1, hTx]
      simp [Matrix.mul_apply, Fin.sum_univ_three, upMat, hg2col]
  have hG : t * G = G * up3 0 0 1 := Subtype.ext key
  refine ⟨G, ?_⟩
  calc G⁻¹ * t * G = G⁻¹ * (t * G) := by group
    _ = G⁻¹ * (G * up3 0 0 1) := by rw [hG]
    _ = up3 0 0 1 := by group

end Invol

end CFSG.QuasithinUnique.Setup.X7a
