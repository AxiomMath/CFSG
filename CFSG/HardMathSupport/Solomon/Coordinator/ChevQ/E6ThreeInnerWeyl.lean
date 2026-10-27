module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs
import TauCeti.LinearAlgebra.Trace.Idempotent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Matrix

private theorem e6InW_fixesForm_iff (v : WeylGroup Tag.E6) (l : Fin Tag.E6.rank → ℤ) :
    FixesForm v l ↔ l ᵥ* weylMatrix v = l := by
  have key : ∀ β : Fin Tag.E6.rank → ℤ,
      ∑ i, l i * (v • β) i = (l ᵥ* weylMatrix v) ⬝ᵥ β := by
    intro β
    rw [← weylMatrix_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [dotProduct]
  have key' : ∀ β : Fin Tag.E6.rank → ℤ, ∑ i, l i * β i = l ⬝ᵥ β := fun β => by
    simp only [dotProduct]
  simp only [FixesForm, key, key']
  constructor
  · intro h
    funext j
    simpa [dotProduct_single] using h (Pi.single j 1)
  · intro h β
    rw [h]

private theorem e6InW_sum_trace_eq_zero (Ω : Subgroup (WeylGroup Tag.E6)) [Fintype Ω]
    (h : ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ∃ w ∈ Ω, ¬ FixesForm w l) :
    ∑ g : Ω, (weylMatrix (g : WeylGroup Tag.E6)).trace = 0 := by
  set P : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
    ∑ g : Ω, weylMatrix (g : WeylGroup Tag.E6) with hP
  have hPM : ∀ x ∈ Ω, P * weylMatrix x = P := by
    intro x hx
    rw [hP, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight ⟨x, hx⟩) _ _ fun g => ?_
    rw [Equiv.coe_mulRight, Subgroup.coe_mul, weylMatrix_mul]
  have hrow : ∀ i, P i = 0 := by
    intro i
    by_contra hne
    obtain ⟨w, hw, hnot⟩ := h (P i) hne
    apply hnot
    rw [e6InW_fixesForm_iff]
    calc P i ᵥ* weylMatrix w = (P * weylMatrix w) i := by
          funext j
          simp [Matrix.vecMul, Matrix.mul_apply, dotProduct]
      _ = P i := by rw [hPM w hw]
  rw [← Matrix.trace_sum, ← hP]
  simp [Matrix.trace, hrow]

private theorem e6InW_trace_cast (M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) :
    ((Int.castRingHom ℚ).mapMatrix M).trace = (M.trace : ℚ) := by
  simp [Matrix.trace]

open CFSG.LieType.RootSystem in
private theorem e6InW_transpose_mul_mul (w : WeylGroup Tag.E6) :
    ((Int.castRingHom ℚ).mapMatrix (weylMatrix w))ᵀ * symmetrized (isFiniteType_cartan Tag.E6) *
      (Int.castRingHom ℚ).mapMatrix (weylMatrix w) =
        symmetrized (isFiniteType_cartan Tag.E6) := by
  set N := (Int.castRingHom ℚ).mapMatrix (weylMatrix w) with hN
  have hcol : ∀ j, toRat (weylAction (isFiniteType_cartan Tag.E6) w (Pi.single j 1)) =
      fun k => N k j := by
    intro j
    funext k
    rw [toRat_apply, ← smul_def, ← weylMatrix_apply, hN, RingHom.mapMatrix_apply,
      Matrix.map_apply, eq_intCast]
  ext i j
  have h := form_weylAction (isFiniteType_cartan Tag.E6) w (Pi.single i 1) (Pi.single j 1)
  rw [form_apply, form_apply, hcol, hcol, toRat_single, toRat_single, single_dotProduct,
    one_mul, Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_)
  ring

open CFSG.LieType.RootSystem in
private theorem e6InW_trace_inv (w : WeylGroup Tag.E6) :
    (weylMatrix w⁻¹).trace = (weylMatrix w).trace := by
  set S := symmetrized (isFiniteType_cartan Tag.E6) with hS
  set N := (Int.castRingHom ℚ).mapMatrix (weylMatrix w) with hN
  set N' := (Int.castRingHom ℚ).mapMatrix (weylMatrix w⁻¹) with hN'
  have hdet : IsUnit S.det :=
    isUnit_iff_ne_zero.mpr (posDef_symmetrized (isFiniteType_cartan Tag.E6)).det_pos.ne'
  have hNN' : N * N' = 1 := by
    rw [hN, hN', ← map_mul, ← weylMatrix_mul, mul_inv_cancel, weylMatrix_one, map_one]
  have h1 : Nᵀ * S = S * N' := by
    calc Nᵀ * S = Nᵀ * S * (N * N') := by rw [hNN', Matrix.mul_one]
      _ = Nᵀ * S * N * N' := by simp only [Matrix.mul_assoc]
      _ = S * N' := by rw [hN, hS, e6InW_transpose_mul_mul]
  have h2 : N' = S⁻¹ * (Nᵀ * S) := by
    rw [h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have h3 : N'.trace = N.trace := by
    rw [h2, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
      Matrix.mul_one, Matrix.trace_transpose]
  rw [hN, hN', e6InW_trace_cast, e6InW_trace_cast] at h3
  exact_mod_cast h3

private theorem e6InW_trace_nonneg {g : WeylGroup Tag.E6} (hg : g ^ 3 = 1)
    {l : Fin Tag.E6.rank → ℤ} (hl : l ≠ 0) (hfix : l ᵥ* weylMatrix g = l) :
    0 ≤ (weylMatrix g).trace := by
  set N := (Int.castRingHom ℚ).mapMatrix (weylMatrix g) with hN
  have hN3 : N ^ 3 = 1 := by
    rw [hN, ← map_pow, ← weylMatrix_pow, hg, weylMatrix_one, map_one]
  have hginv : g⁻¹ = g ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hg)).symm
  have htr2 : (N ^ 2).trace = N.trace := by
    rw [hN, ← map_pow, ← weylMatrix_pow, ← hginv, e6InW_trace_cast, e6InW_trace_cast,
      e6InW_trace_inv]
  set Q := 1 + N + N ^ 2 with hQ
  have hQQ : Q * Q = (3 : ℚ) • Q := by
    have h4 : N ^ 4 = N := by rw [pow_succ, hN3, one_mul]
    calc Q * Q = 1 + 2 • N + 3 • N ^ 2 + 2 • N ^ 3 + N ^ 4 := by rw [hQ]; noncomm_ring
      _ = (3 : ℚ) • Q := by
        rw [hN3, h4, hQ, ofNat_smul_eq_nsmul (R := ℚ)]
        abel
  set f := Matrix.toLin' Qᵀ with hf
  have hff : f * f = (3 : ℚ) • f := by
    rw [hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.transpose_mul, hQQ,
      Matrix.transpose_smul, map_smul]
  have htr := TauCeti.LinearMap.trace_eq_mul_finrank_range hff
  rw [hf, Matrix.trace_toLin'_eq, Matrix.trace_transpose, hQ, Matrix.trace_add,
    Matrix.trace_add, htr2, Matrix.trace_one, Fintype.card_fin, hN, e6InW_trace_cast] at htr
  obtain ⟨lq, hlq⟩ : ∃ lq : Fin Tag.E6.rank → ℚ, lq = fun i => (l i : ℚ) := ⟨_, rfl⟩
  have hlN : lq ᵥ* N = lq := by
    funext j
    have := congrFun hfix j
    simp only [Matrix.vecMul, dotProduct] at this ⊢
    simp only [hlq, hN, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
    exact_mod_cast this
  have hfl : f lq = (3 : ℚ) • lq := by
    rw [hf, Matrix.toLin'_apply, Matrix.mulVec_transpose, hQ, Matrix.vecMul_add,
      Matrix.vecMul_add, Matrix.vecMul_one, sq, ← Matrix.vecMul_vecMul, hlN, hlN,
      ofNat_smul_eq_nsmul (R := ℚ)]
    abel
  have hmem : lq ∈ LinearMap.range f :=
    ⟨(3 : ℚ)⁻¹ • lq, by rw [map_smul, hfl, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]⟩
  have hne : lq ≠ 0 := by
    intro h0
    apply hl
    funext i
    have := congrFun h0 i
    rw [hlq] at this
    simpa using this
  have hbot : LinearMap.range f ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨lq, hmem, hne⟩
  have hpos : 0 < Module.finrank ℚ (LinearMap.range f) :=
    Nat.pos_of_ne_zero fun h0 => hbot (Submodule.finrank_eq_zero.1 h0)
  have h6 : ((Tag.E6.rank : ℕ) : ℚ) = 6 := by
    rw [show Tag.E6.rank = 6 from rfl]
    norm_num
  rw [h6] at htr
  have hint : (6 : ℤ) + (weylMatrix g).trace + (weylMatrix g).trace =
      3 * (Module.finrank ℚ (LinearMap.range f) : ℤ) := by
    exact_mod_cast htr
  omega

theorem e6WeylEllipticOfNoFixed_holds : E6WeylEllipticOfNoFixed := by
  intro Ω hΩ3 _ hnofix
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  have hsum := e6InW_sum_trace_eq_zero Ω hnofix
  by_contra hcon
  push Not at hcon
  have hnn : ∀ g : Ω, 0 ≤ (weylMatrix (g : WeylGroup Tag.E6)).trace := fun g => by
    obtain ⟨l, hl, hfix⟩ := hcon g g.2
    exact e6InW_trace_nonneg (hΩ3 g g.2) hl ((e6InW_fixesForm_iff _ _).1 hfix)
  have h1 := Finset.single_le_sum (f := fun g : Ω => (weylMatrix (g : WeylGroup Tag.E6)).trace)
    (fun g _ => hnn g) (Finset.mem_univ 1)
  rw [hsum, OneMemClass.coe_one, weylMatrix_one, Matrix.trace_one, Fintype.card_fin] at h1
  exact absurd h1 (by decide)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
