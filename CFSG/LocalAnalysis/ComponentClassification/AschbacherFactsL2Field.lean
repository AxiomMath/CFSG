module

import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter

@[expose] noncomputable def psl2Incl (K : Type) [Field K] : PSL2 K →* PGammaL2 K :=
  (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).comp
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K))

theorem psl2Incl_apply (K : Type) [Field K] (x : PSL2 K) :
    psl2Incl K x = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := rfl

theorem psl2Incl_injective (K : Type) [Field K] : Function.Injective (psl2Incl K) :=
  fun _ _ h => Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (SemidirectProduct.inl_injective h)

@[expose] noncomputable def conjPSL (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (γ : PGammaL2 K) :
    MulAut (PSL2 K) :=
  haveI := pGammaL2PSLRange_normal K hK hcard
  MulAut.congr (pGammaL2PSLRangeEquiv K).symm (MulAut.conjNormal γ)

theorem psl2Incl_conjPSL (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (γ : PGammaL2 K)
    (x : PSL2 K) : psl2Incl K (conjPSL K hK hcard γ x) = γ * psl2Incl K x * γ⁻¹ := by
  have := pGammaL2PSLRange_normal K hK hcard
  have h1 : pGammaL2PSLRangeEquiv K (conjPSL K hK hcard γ x) =
      MulAut.conjNormal γ (pGammaL2PSLRangeEquiv K x) := by
    change pGammaL2PSLRangeEquiv K ((pGammaL2PSLRangeEquiv K).symm
      (MulAut.conjNormal γ (pGammaL2PSLRangeEquiv K x))) = _
    rw [MulEquiv.apply_symm_apply]
  have h2 := congrArg Subtype.val h1
  rw [pGammaL2PSLRangeEquiv_coe, MulAut.conjNormal_apply, pGammaL2PSLRangeEquiv_coe] at h2
  exact h2

theorem conjPSL_eq_iff (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (γ : PGammaL2 K)
    (x y : PSL2 K) : conjPSL K hK hcard γ x = y ↔ γ * psl2Incl K x * γ⁻¹ = psl2Incl K y := by
  rw [← psl2Incl_conjPSL]
  exact (psl2Incl_injective K).eq_iff.symm

theorem specialLinearGroup_map_transvection' {K : Type} [Field K] (e : K ≃+* K)
    {i j : Fin 2} (hij : i ≠ j) (t : K) :
    Matrix.SpecialLinearGroup.map e.toRingHom (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij (e t) := by
  classical
  ext a b
  by_cases h : i = a ∧ j = b <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, h]

theorem transvection_pow {K : Type} [Field K] {i j : Fin 2} (hij : i ≠ j) (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij (1 : K) ^ n =
      Matrix.SpecialLinearGroup.transvection hij (n : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add, Nat.cast_succ]

theorem psl2_root_pair (K : Type) [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    ∃ ρ₁ ρ₂ : PSL2 K, ρ₁ ^ p = 1 ∧ ρ₁ ≠ 1 ∧ ρ₂ ^ p = 1 ∧ ρ₂ ≠ 1 ∧ ρ₁ * ρ₂ ≠ ρ₂ * ρ₁ ∧
      ∀ σ : K ≃+* K, psl2FieldAut K σ ρ₁ = ρ₁ ∧ psl2FieldAut K σ ρ₂ = ρ₂ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hKcard
  have : CharP K p := charP_of_card_eq_prime_pow hKF
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  set τ₁ := Matrix.SpecialLinearGroup.transvection h01 (1 : K) with hτ₁
  set τ₂ := Matrix.SpecialLinearGroup.transvection h10 (1 : K) with hτ₂
  let π : Matrix.SpecialLinearGroup (Fin 2) K →* PSL2 K := QuotientGroup.mk' _
  have hpow : ∀ {i j : Fin 2} (hij : i ≠ j),
      π (Matrix.SpecialLinearGroup.transvection hij (1 : K)) ^ p = 1 := by
    intro i j hij
    rw [← map_pow, transvection_pow, CharP.cast_eq_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
  have hne : ∀ {i j : Fin 2} (hij : i ≠ j),
      π (Matrix.SpecialLinearGroup.transvection hij (1 : K)) ≠ 1 := by
    intro i j hij h
    have hc : Matrix.SpecialLinearGroup.transvection hij (1 : K) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
      (QuotientGroup.eq_one_iff _).mp h
    rw [Matrix.SpecialLinearGroup.transvection_mem_center_iff] at hc
    exact one_ne_zero hc
  have hfix : ∀ {i j : Fin 2} (hij : i ≠ j) (σ : K ≃+* K),
      psl2FieldAut K σ (π (Matrix.SpecialLinearGroup.transvection hij (1 : K))) =
        π (Matrix.SpecialLinearGroup.transvection hij (1 : K)) := by
    intro i j hij σ
    rw [psl2FieldAut_apply]
    change psl2RingEquiv σ (QuotientGroup.mk' _ _) = _
    rw [psl2RingEquiv_mk, specialLinearGroup_map_transvection', map_one]
  refine ⟨π τ₁, π τ₂, hpow h01, hne h01, hpow h10, hne h10, ?_,
    fun σ => ⟨hfix h01 σ, hfix h10 σ⟩⟩
  intro h
  rw [← map_mul, ← map_mul] at h
  have hc : (τ₁ * τ₂)⁻¹ * (τ₂ * τ₁) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    QuotientGroup.eq.mp h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hBA : ((τ₂ * τ₁ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((τ₁ * τ₂ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        Matrix.scalar (Fin 2) r := by
    rw [hr, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have e01 := congrFun (congrFun hBA 0) 1
  have e00 := congrFun (congrFun hBA 0) 0
  simp [hτ₁, hτ₂, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply] at e01 e00
  rw [← e01] at e00
  exact one_ne_zero (by linear_combination -e00 : (1 : K) = 0)

theorem inr_commute_of_fixed {K : Type} [Field K] (σ : K ≃+* K) {x : PSL2 K}
    (hx : psl2FieldAut K σ x = x) :
    SemidirectProduct.inr σ * psl2Incl K x = psl2Incl K x * SemidirectProduct.inr σ := by
  have h1 : (SemidirectProduct.inr σ : PGammaL2 K) * psl2Incl K x *
      (SemidirectProduct.inr σ)⁻¹ = psl2Incl K x := by
    rw [psl2Incl_apply, ← map_inv, ← SemidirectProduct.inl_aut, ← psl2FieldAut_toPGL, hx]
  calc (SemidirectProduct.inr σ : PGammaL2 K) * psl2Incl K x =
      SemidirectProduct.inr σ * psl2Incl K x * (SemidirectProduct.inr σ)⁻¹ *
        SemidirectProduct.inr σ := by group
    _ = psl2Incl K x * SemidirectProduct.inr σ := by rw [h1]

theorem field_involution_fixed_root_pair {K : Type} [Field K] [Finite K] {p f : ℕ}
    [hp : Fact p.Prime] (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {v : PGammaL2 K} (hv : v ^ 2 = 1) (hfield : v.right ≠ 1) :
    ∃ r₁ r₂ : PSL2 K, r₁ ^ p = 1 ∧ r₁ ≠ 1 ∧ r₂ ^ p = 1 ∧ r₂ ≠ 1 ∧ r₁ * r₂ ≠ r₂ * r₁ ∧
      v * psl2Incl K r₁ = psl2Incl K r₁ * v ∧ v * psl2Incl K r₂ = psl2Incl K r₂ * v := by
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hfield rfl
  obtain ⟨C, hC⟩ := projective_semilinear_involution_conj_inr hK v (orderOf_eq_prime hv hv1)
    hfield
  obtain ⟨ρ₁, ρ₂, h₁p, h₁1, h₂p, h₂1, h₁₂, hσ⟩ := psl2_root_pair K hKcard
  set c : PGammaL2 K := SemidirectProduct.inl C with hcdef
  set φ := conjPSL K hK hcard c with hφ
  have hvc : v = c * SemidirectProduct.inr v.right * c⁻¹ := by
    rw [← hC]
    group
  have hcomm : ∀ ρ : PSL2 K, psl2FieldAut K v.right ρ = ρ →
      v * psl2Incl K (φ ρ) = psl2Incl K (φ ρ) * v := by
    intro ρ hρ
    rw [hφ, psl2Incl_conjPSL, hvc]
    have h := inr_commute_of_fixed v.right hρ
    calc c * SemidirectProduct.inr v.right * c⁻¹ * (c * psl2Incl K ρ * c⁻¹) =
        c * (SemidirectProduct.inr v.right * psl2Incl K ρ) * c⁻¹ := by group
      _ = c * (psl2Incl K ρ * SemidirectProduct.inr v.right) * c⁻¹ := by rw [h]
      _ = c * psl2Incl K ρ * c⁻¹ * (c * SemidirectProduct.inr v.right * c⁻¹) := by group
  refine ⟨φ ρ₁, φ ρ₂, by rw [← map_pow, h₁p, map_one], fun h => h₁1 (φ.injective
    (h.trans (map_one φ).symm)), by rw [← map_pow, h₂p, map_one], fun h => h₂1 (φ.injective
    (h.trans (map_one φ).symm)), fun h => h₁₂ (φ.injective (by rw [map_mul, map_mul, h])),
    hcomm ρ₁ (hσ v.right).1, hcomm ρ₂ (hσ v.right).2⟩

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
