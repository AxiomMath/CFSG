module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.QTGen4.DSGen4.OmegaH

open Matrix

@[expose] def cK (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

@[expose] def sqK (K : Type) [Field K] [CharP K 2] : K →+* K :=
  frobenius K 2

structure HermCtx (K : Type) [Field K] [Fintype K] [CharP K 2] (ω : K) : Prop where
  card : Fintype.card K = 4
  ne_zero : ω ≠ 0
  ne_one : ω ≠ 1
  cube : ω ^ 3 = 1

variable {K : Type} [Field K] [Fintype K] [CharP K 2]

theorem two_eq_zero_K : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

theorem sqK_apply (x : K) : sqK K x = x ^ 2 := rfl

theorem cK_sq (c : ZMod 2) : cK K c ^ 2 = cK K c := by
  rw [← map_pow]
  congr 1
  revert c
  decide

theorem sq_add_char2 (x y : K) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  rw [add_sq, two_eq_zero_K]
  ring

theorem pow_four {ω : K} (C : HermCtx K ω) (x : K) : x ^ 4 = x := by
  have h := FiniteField.pow_card x
  rw [C.card] at h
  exact h

theorem sqK_sqK {ω : K} (C : HermCtx K ω) (x : K) : sqK K (sqK K x) = x := by
  rw [sqK_apply, sqK_apply, ← pow_mul]
  exact pow_four C x

theorem omega_sq_add {ω : K} (C : HermCtx K ω) : ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination C.cube
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (sub_eq_zero.mp h') C.ne_one
  · exact h'

theorem omega_four {ω : K} (C : HermCtx K ω) : (ω ^ 2) ^ 2 = ω := by
  rw [← pow_mul]
  linear_combination ω * C.cube

theorem exists_omega (hK : Fintype.card K = 4) : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  obtain ⟨x, hx0, hx1⟩ : ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hK] at h1
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  refine ⟨x, hx0, hx1, ?_⟩
  have h := FiniteField.pow_card_sub_one_eq_one x hx0
  rw [hK] at h
  simpa using h

theorem comb_eq_zero {ω : K} (h0 : ω ≠ 0) (h1 : ω ≠ 1) {a c : ZMod 2}
    (h : cK K a + cK K c * ω = 0) : a = 0 ∧ c = 0 := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) c with rfl | rfl
  · refine ⟨?_, rfl⟩
    rw [map_zero, zero_mul, add_zero] at h
    exact (cK K).injective (h.trans (map_zero _).symm)
  · exfalso
    rw [map_one, one_mul] at h
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) a with rfl | rfl
    · rw [map_zero, zero_add] at h
      exact h0 h
    · rw [map_one] at h
      apply h1
      linear_combination h - (two_eq_zero_K (K := K))

theorem exists_comb {ω : K} (C : HermCtx K ω) (b : K) :
    ∃ c₁ c₂ : ZMod 2, b = cK K c₁ + cK K c₂ * ω := by
  let f : ZMod 2 × ZMod 2 → K := fun p => cK K p.1 + cK K p.2 * ω
  have hinj : Function.Injective f := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ hf
    have h : cK K (a - a') + cK K (c - c') * ω = 0 := by
      simp only [f, map_sub] at hf ⊢
      linear_combination hf
    obtain ⟨ha, hc⟩ := comb_eq_zero C.ne_zero C.ne_one h
    rw [sub_eq_zero] at ha hc
    simp [ha, hc]
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_prod, ZMod.card, C.card]
  obtain ⟨⟨c₁, c₂⟩, hp⟩ := hbij.2 b
  exact ⟨c₁, c₂, hp.symm⟩

@[expose] def IsHermM (X : Matrix (Fin 2) (Fin 2) K) : Prop :=
  X.map (sqK K) = X.transpose

@[expose] def hermMat (ω : K) (v : Fin 4 → ZMod 2) : Matrix (Fin 2) (Fin 2) K :=
  !![cK K (v 0), cK K (v 1) + cK K (v 2) * ω; cK K (v 1) + cK K (v 2) * ω ^ 2, cK K (v 3)]

theorem hermMat_add (ω : K) (v w : Fin 4 → ZMod 2) :
    hermMat ω (v + w) = hermMat ω v + hermMat ω w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermMat, map_add] <;> ring

theorem hermMat_zero (ω : K) : hermMat ω 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermMat]

theorem hermMat_isHerm {ω : K} (C : HermCtx K ω) (v : Fin 4 → ZMod 2) :
    IsHermM (hermMat ω v) := by
  have h4 := omega_four C
  have e00 : cK K (v 0) ^ 2 = cK K (v 0) := cK_sq _
  have e01 : (cK K (v 1) + cK K (v 2) * ω) ^ 2 = cK K (v 1) + cK K (v 2) * ω ^ 2 := by
    rw [sq_add_char2, mul_pow, cK_sq, cK_sq]
  have e10 : (cK K (v 1) + cK K (v 2) * ω ^ 2) ^ 2 = cK K (v 1) + cK K (v 2) * ω := by
    rw [sq_add_char2, mul_pow, cK_sq, cK_sq, h4]
  have e11 : cK K (v 3) ^ 2 = cK K (v 3) := cK_sq _
  unfold IsHermM
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [hermMat, sqK_apply] using e00
  · simpa [hermMat, sqK_apply] using e01
  · simpa [hermMat, sqK_apply] using e10
  · simpa [hermMat, sqK_apply] using e11

theorem hermMat_injective {ω : K} (C : HermCtx K ω) : Function.Injective (hermMat ω) := by
  intro v w h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp only [hermMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] at e00 e01 e11
  have hc := comb_eq_zero C.ne_zero C.ne_one (a := v 1 - w 1) (c := v 2 - w 2)
    (by simp only [map_sub]; linear_combination e01)
  have h0 : v 0 = w 0 := (cK K).injective e00
  have h3 : v 3 = w 3 := (cK K).injective e11
  have h1 : v 1 = w 1 := sub_eq_zero.mp hc.1
  have h2 : v 2 = w 2 := sub_eq_zero.mp hc.2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem exists_hermMat {ω : K} (C : HermCtx K ω) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : IsHermM X) : ∃ v, hermMat ω v = X := by
  have e00 : X 0 0 ^ 2 = X 0 0 := by
    have := congrFun (congrFun hX 0) 0
    simpa [IsHermM, sqK_apply] using this
  have e11 : X 1 1 ^ 2 = X 1 1 := by
    have := congrFun (congrFun hX 1) 1
    simpa [IsHermM, sqK_apply] using this
  have e01 : X 0 1 ^ 2 = X 1 0 := by
    have := congrFun (congrFun hX 0) 1
    simpa [IsHermM, sqK_apply] using this
  have e10 : X 1 0 ^ 2 = X 0 1 := by
    have := congrFun (congrFun hX 1) 0
    simpa [IsHermM, sqK_apply] using this
  have bit : ∀ x : K, x ^ 2 = x → ∃ c : ZMod 2, cK K c = x := by
    intro x hx
    have : x * (x - 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨0, by rw [map_zero, h]⟩
    · exact ⟨1, by rw [map_one, sub_eq_zero.mp h]⟩
  obtain ⟨c0, hc0⟩ := bit _ e00
  obtain ⟨c3, hc3⟩ := bit _ e11
  obtain ⟨c1, c2, hc12⟩ := exists_comb C (X 0 1)
  refine ⟨![c0, c1, c2, c3], ?_⟩
  have hX10 : X 1 0 = cK K c1 + cK K c2 * ω ^ 2 := by
    rw [← e01, hc12, sq_add_char2, mul_pow, cK_sq, cK_sq]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [hermMat, hc0]
  · simp [hermMat, hc12]
  · simp [hermMat, hX10]
  · simp [hermMat, hc3]

open Classical in
@[expose] noncomputable def hermCoord (ω : K) (X : Matrix (Fin 2) (Fin 2) K) : Fin 4 → ZMod 2 :=
  if h : ∃ v, hermMat ω v = X then h.choose else 0

theorem hermMat_hermCoord {ω : K} (C : HermCtx K ω) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : IsHermM X) : hermMat ω (hermCoord ω X) = X := by
  have h : ∃ v, hermMat ω v = X := exists_hermMat C hX
  unfold hermCoord
  rw [dif_pos h]
  exact h.choose_spec

@[expose] def tm (s X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  s * X * (s.map (sqK K)).transpose

theorem tm_isHerm {ω : K} (C : HermCtx K ω) (s : Matrix (Fin 2) (Fin 2) K) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : IsHermM X) : IsHermM (tm s X) := by
  have hss : (s.map (sqK K)).map (sqK K) = s := by
    ext i j
    simp [Matrix.map_apply, sqK_sqK C]
  have hT : (s.map (sqK K)).transpose.map (sqK K) = sᵀ := by
    ext i j
    simp [Matrix.map_apply, sqK_sqK C]
  unfold IsHermM tm at *
  rw [Matrix.map_mul, Matrix.map_mul, hX, hT]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem tm_mul (s t X : Matrix (Fin 2) (Fin 2) K) : tm (s * t) X = tm s (tm t X) := by
  simp only [tm, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem tm_one (X : Matrix (Fin 2) (Fin 2) K) : tm 1 X = X := by
  simp [tm, Matrix.map_one (sqK K) (map_zero _) (map_one _)]

theorem tm_add (s X Y : Matrix (Fin 2) (Fin 2) K) : tm s (X + Y) = tm s X + tm s Y := by
  simp [tm, Matrix.mul_add, Matrix.add_mul]

@[expose] noncomputable def rhoFun {ω : K} (C : HermCtx K ω) (s : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  hermCoord ω (tm s (hermMat ω v))

theorem rhoFun_spec {ω : K} (C : HermCtx K ω) (s : Matrix (Fin 2) (Fin 2) K) (v : Fin 4 → ZMod 2) :
    hermMat ω (rhoFun C s v) = tm s (hermMat ω v) :=
  hermMat_hermCoord C (tm_isHerm C s (hermMat_isHerm C v))

theorem rhoFun_add {ω : K} (C : HermCtx K ω) (s : Matrix (Fin 2) (Fin 2) K) (v w : Fin 4 → ZMod 2) :
    rhoFun C s (v + w) = rhoFun C s v + rhoFun C s w := by
  apply hermMat_injective C
  rw [rhoFun_spec, hermMat_add, tm_add, hermMat_add, rhoFun_spec, rhoFun_spec]

theorem rhoFun_mul {ω : K} (C : HermCtx K ω) (s t : Matrix (Fin 2) (Fin 2) K) (v : Fin 4 → ZMod 2) :
    rhoFun C (s * t) v = rhoFun C s (rhoFun C t v) := by
  apply hermMat_injective C
  rw [rhoFun_spec, tm_mul, rhoFun_spec, rhoFun_spec]

theorem rhoFun_one {ω : K} (C : HermCtx K ω) (v : Fin 4 → ZMod 2) : rhoFun C 1 v = v := by
  apply hermMat_injective C
  rw [rhoFun_spec, tm_one]

@[expose] noncomputable def rhoLin {ω : K} (C : HermCtx K ω) (s : Matrix (Fin 2) (Fin 2) K) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun := rhoFun C s
  map_add' := rhoFun_add C s
  map_smul' := by
    intro c v
    have h0 : rhoFun C s 0 = 0 := by
      simpa using rhoFun_add C s 0 0
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) c with rfl | rfl
    · simp [h0]
    · simp

@[expose] noncomputable def R4 {ω : K} (C : HermCtx K ω) (s : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  LinearMap.toMatrix' (rhoLin C s)

theorem R4_mulVec {ω : K} (C : HermCtx K ω) (s : Matrix (Fin 2) (Fin 2) K) (v : Fin 4 → ZMod 2) :
    R4 C s *ᵥ v = rhoFun C s v := by
  exact LinearMap.toMatrix'_mulVec (rhoLin C s) v

theorem R4_mul {ω : K} (C : HermCtx K ω) (s t : Matrix (Fin 2) (Fin 2) K) :
    R4 C (s * t) = R4 C s * R4 C t := by
  unfold R4
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro v
  exact rhoFun_mul C s t v

theorem R4_one {ω : K} (C : HermCtx K ω) : R4 C 1 = 1 := by
  have h : rhoLin C 1 = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact rhoFun_one C v
  unfold R4
  rw [h, LinearMap.toMatrix'_id]

@[expose] def transvM : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]

theorem rhoFun_transv {ω : K} (C : HermCtx K ω) :
    rhoFun C (transvM : Matrix (Fin 2) (Fin 2) K) ![0, 0, 0, 1] = ![1, 1, 0, 1] := by
  apply hermMat_injective C
  rw [rhoFun_spec]
  have hv1 : hermMat ω ![0, 0, 0, 1] = !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermMat]
  have hv2 : hermMat ω ![1, 1, 0, 1] = !![1, 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermMat]
  rw [hv1, hv2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tm, transvM, sqK_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem R4_transv_ne_one {ω : K} (C : HermCtx K ω) :
    R4 C (transvM : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
  intro h
  have h1 : R4 C (transvM : Matrix (Fin 2) (Fin 2) K) *ᵥ ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
    rw [h, Matrix.one_mulVec]
  rw [R4_mulVec, rhoFun_transv] at h1
  have h0 := congrFun h1 0
  simp at h0

@[expose] def transvSL : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨transvM, by simp [transvM, Matrix.det_fin_two]⟩

theorem eig_of_det {β : Matrix (Fin 2) (Fin 2) K} {c : K}
    (h : (β - c • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0) :
    ∃ w : Fin 2 → K, w ≠ 0 ∧ β *ᵥ w = c • w := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨w, hw0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hw
  exact hw

theorem exists_eigen {ω : K} (C : HermCtx K ω) {β : Matrix (Fin 2) (Fin 2) K} (hβ : β * β * β = 1) :
    ∃ c : K, c ^ 3 = 1 ∧ ∃ w : Fin 2 → K, w ≠ 0 ∧ β *ᵥ w = c • w := by
  have hprod : (β - (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)) * (β - ω • (1 : Matrix (Fin 2) (Fin 2) K)) *
      (β - (ω ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K)) = 0 := by
    have e : (β - (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)) * (β - ω • (1 : Matrix (Fin 2) (Fin 2) K)) *
        (β - (ω ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K)) =
          β * β * β - ((1 : K) + ω + ω ^ 2) • (β * β) + ((1 : K) * ω + ω * ω ^ 2 + ω ^ 2 * 1) • β -
            ((1 : K) * ω * ω ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
        Matrix.one_mul, Matrix.mul_one, mul_assoc]
      module
    rw [e]
    have h1 : (1 : K) + ω + ω ^ 2 = 0 := by linear_combination omega_sq_add C
    have h2 : (1 : K) * ω + ω * ω ^ 2 + ω ^ 2 * 1 = 0 := by
      linear_combination omega_sq_add C + C.cube
    have h3 : (1 : K) * ω * ω ^ 2 = 1 := by linear_combination C.cube
    rw [h1, h2, h3, hβ]
    simp
  have hdet : ((β - (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)) * (β - ω • (1 : Matrix (Fin 2) (Fin 2) K)) *
      (β - (ω ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K))).det = 0 := by
    rw [hprod]
    simp
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  rcases mul_eq_zero.mp hdet with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · obtain ⟨w, hw0, hw⟩ := eig_of_det h'
      exact ⟨1, one_pow 3, w, hw0, hw⟩
    · obtain ⟨w, hw0, hw⟩ := eig_of_det h'
      exact ⟨ω, C.cube, w, hw0, hw⟩
  · obtain ⟨w, hw0, hw⟩ := eig_of_det h
    exact ⟨ω ^ 2, by linear_combination (ω ^ 3 + 1) * C.cube, w, hw0, hw⟩

theorem exists_fixed_of_cube {ω : K} (C : HermCtx K ω) {β : Matrix (Fin 2) (Fin 2) K}
    (hβ : β * β * β = 1) : ∃ v : Fin 4 → ZMod 2, v ≠ 0 ∧ R4 C β *ᵥ v = v := by
  obtain ⟨c, hc3, w, hw0, hw⟩ := exists_eigen C hβ
  let X : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => w i * w j ^ 2
  have hi : ∀ i, β i 0 * w 0 + β i 1 * w 1 = c * w i := by
    intro i
    have := congrFun hw i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hX1 : β * X = c • X := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, X, Matrix.of_apply, smul_eq_mul]
    linear_combination (w j ^ 2) * hi i
  have hX2 : X * (β.map (sqK K)).transpose = (c ^ 2) • X := by
    ext i j
    have hj := hi j
    have h2 := two_eq_zero_K (K := K)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, X, Matrix.of_apply,
      Matrix.transpose_apply, Matrix.map_apply, sqK_apply, smul_eq_mul]
    linear_combination (w i * (β j 0 * w 0 + β j 1 * w 1 + c * w j)) * hj +
      (-(w i * β j 0 * w 0 * β j 1 * w 1)) * h2
  have hXH : IsHermM X := by
    unfold IsHermM
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, X, Matrix.of_apply, sqK_apply]
    linear_combination (w i ^ 2) * pow_four C (w j)
  have hX0 : X ≠ 0 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw0
    intro h
    have hkk : X k k = 0 := by rw [h]; rfl
    simp only [X, Matrix.of_apply] at hkk
    exact (mul_ne_zero hk (pow_ne_zero 2 hk)) (by simpa using hkk)
  have hfix : tm β X = X := by
    unfold tm
    rw [hX1, Matrix.smul_mul, hX2, smul_smul]
    have : c * c ^ 2 = 1 := by linear_combination hc3
    rw [this, one_smul]
  refine ⟨hermCoord ω X, ?_, ?_⟩
  · intro h0
    apply hX0
    rw [← hermMat_hermCoord C hXH, h0, hermMat_zero]
  · rw [R4_mulVec]
    unfold rhoFun
    rw [hermMat_hermCoord C hXH, hfix]

@[expose] noncomputable def RM {ω : K} (C : HermCtx K ω) :
    Matrix.SpecialLinearGroup (Fin 2) K →* Matrix (Fin 4) (Fin 4) (ZMod 2) where
  toFun s := R4 C (s : Matrix (Fin 2) (Fin 2) K)
  map_one' := by
    simp only [Matrix.SpecialLinearGroup.coe_one]
    exact R4_one C
  map_mul' s t := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact R4_mul C _ _

@[expose] noncomputable def RSL {ω : K} (C : HermCtx K ω) :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 4) (ZMod 2) :=
  (RM C).toHomUnits

theorem RSL_val {ω : K} (C : HermCtx K ω) (s : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((RSL C s : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      R4 C (s : Matrix (Fin 2) (Fin 2) K) := rfl

end CFSG.GH74.QTGen4.DSGen4.OmegaH
