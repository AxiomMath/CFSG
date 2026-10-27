module

import CFSG.FeitThompson.Representations.CyclicTIIsometryUnique
public import CFSG.FeitThompson.Representations.CyclicTITwoColumnHalfSelection
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import CFSG.FeitThompson.Representations.CyclicTIIsometryPowerEquivariance
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators
import CFSG.FeitThompson.Representations.CoprimePowerNonprincipalPrimeChars
import CFSG.FeitThompson.Representations.ConstantValuePuncturedSubgroupInteger
import CFSG.FeitThompson.Representations.RationalAlgebraicIntegerIsInteger
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem indClassFun_apply_eq_zero_of_forall_not_isConj {G : Type*} [Group G] [Fintype G]
    (W : Subgroup G) {A : Set G} {θ : ↥W → ℂ}
    (hθ : ∀ z : ↥W, (z : G) ∉ A → θ z = 0) {x : G} (hx : ∀ v ∈ A, ¬ IsConj x v) :
    indClassFun W θ x = 0 := by
  classical
  rw [indClassFun_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  by_cases hmem : t⁻¹ * x * t ∈ W
  · rw [dif_pos hmem]
    refine hθ ⟨_, hmem⟩ fun hA => hx _ hA (isConj_iff.2 ⟨t⁻¹, ?_⟩)
    group
  · rw [dif_neg hmem]

theorem not_isIntegral_of_natCast_mul_add_one_eq_zero {q : ℕ} (hq : q.Prime) {z : ℂ}
    (hz : (q : ℂ) * z + 1 = 0) : ¬ IsIntegral ℤ z := by
  intro hint
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hzq : z = ((-1 / q : ℚ) : ℂ) := by
    push_cast
    field_simp
    linear_combination hz
  obtain ⟨n, hn⟩ := (Complex.isIntegral_int_iff_exists_int_of_exists_rat ⟨_, hzq⟩).1 hint
  rw [hn] at hz
  have hint2 : ((q : ℤ) * n + 1 : ℤ) = 0 := by
    have : (((q : ℤ) * n + 1 : ℤ) : ℂ) = 0 := by push_cast; linear_combination hz
    exact_mod_cast this
  have hle : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨-n, by linarith⟩
  have := hq.two_le
  omega

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G} {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem ne_principalIrr_iff {A : Type*} [Group A] {i : Irr A} :
    i ≠ principalIrr A ↔ (i : A → ℂ) ≠ 1 := by
  rw [ne_eq, ne_eq, Subtype.ext_iff, coe_principalIrr]

namespace IsCyclicTIPair

theorem prodChar_ne_zero (hW : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ} {mu : ↥W2 → ℂ}
    (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) (z : ↥W) : hW.prodChar lam mu z ≠ 0 := by
  have := hW.isMulCommutative_left
  have := hW.isMulCommutative_right
  obtain ⟨ψ₁, hψ₁⟩ := exists_monoidHom_coe_eq_of_mem_Irr hlam
  obtain ⟨ψ₂, hψ₂⟩ := exists_monoidHom_coe_eq_of_mem_Irr hmu
  rw [prodChar_apply, ← hψ₁, ← hψ₂]
  exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)

theorem powOp_prodChar_principal (hW : IsCyclicTIPair W W1 W2) {lam lam' : ↥W1 → ℂ} {k : ℕ}
    (hk : ∀ c : ↥W1, lam' c = lam (c ^ k)) :
    powOp k (hW.prodChar lam (1 : ↥W2 → ℂ)) = hW.prodChar lam' (1 : ↥W2 → ℂ) := by
  funext z
  rw [powOp_apply, prodChar_apply, prodChar_apply, hk, map_pow]
  simp

variable [Fintype G] [Fintype ↥W]

theorem forall_not_isConj_of_prodCharEta_apply_eq_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) {x : G}
    (hx : hW.prodCharEta σ i j x = 0) : ∀ v ∈ cyclicTIDiff W W1 W2, ¬ IsConj x v := by
  intro v hv hconj
  have h1 : hW.prodCharEta σ i j x = hW.prodCharEta σ i j v :=
    classFun.apply_eq_of_isConj (hW.prodCharEta_mem_classFun i j) hconj
  rw [hx, hW.prodCharEta_apply_of_mem_cyclicTIDiff hσ i j hv] at h1
  exact hW.prodChar_ne_zero i.2 j.2 _ h1.symm

theorem prodCharEta_apply_eq_of_forall_not_isConj (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) {x : G}
    (hx : ∀ v ∈ cyclicTIDiff W W1 W2, ¬ IsConj x v) :
    hW.prodCharEta σ i j x =
      hW.prodCharEta σ i (principalIrr ↥W2) x
        + hW.prodCharEta σ (principalIrr ↥W1) j x - 1 := by
  have hind : indClassFun W (hW.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)) x = 0 :=
    indClassFun_apply_eq_zero_of_forall_not_isConj W
      (mem_dadeDomain.1 (hW.prodCharAlpha_mem_dadeDomain i.2 j.2)).2 hx
  have hβ := congrFun (hW.prodCharBeta_eq_prodCharEta hσ i j) x
  rw [hW.prodCharBeta_eq] at hβ
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.one_apply, hind] at hβ
  linear_combination -hβ

theorem prodCharEta_axis_apply_eq_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hq : (Nat.card ↥W1).Prime)
    {i i₀ : Irr ↥W1} (hi : i ≠ principalIrr ↥W1) (hi₀ : i₀ ≠ principalIrr ↥W1) {x : G}
    (h0 : hW.prodCharEta σ i₀ (principalIrr ↥W2) x = 0) :
    hW.prodCharEta σ i (principalIrr ↥W2) x = 0 := by
  have hne0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, hk1, hk, hkeq⟩ :=
    exists_pow_apply_eq_of_mem_Irr_of_natCard_eq_prime hq hne0 (C := ↥W1) rfl
      i₀.2 (ne_principalIrr_iff.1 hi₀) i.2 (ne_principalIrr_iff.1 hi)
  have hbasis : classFun.powOpₗ ↥W k (hW.basisProdIrr (i₀, principalIrr ↥W2))
      = hW.basisProdIrr (i, principalIrr ↥W2) := by
    refine Subtype.ext ?_
    rw [classFun.coe_powOpₗ_apply, hW.coe_basisProdIrr_apply, hW.coe_basisProdIrr_apply]
    simpa using hW.powOp_prodChar_principal hkeq
  have hstep : hW.prodCharEta σ i (principalIrr ↥W2) x
      = hW.prodCharEta σ i₀ (principalIrr ↥W2) (x ^ k) := by
    rw [hW.prodCharEta_eq_coe_apply i (principalIrr ↥W2),
      hW.prodCharEta_eq_coe_apply i₀ (principalIrr ↥W2), ← hbasis]
    exact IsCyclicTIIsometry.apply_powOpₗ_apply hW hσ hk1 hk _ x
  rw [hstep]
  have hkord : k.Coprime (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard x) hk
  refine (apply_eq_zero_iff_of_zpowers_eq ?_ (isOfFinOrder_of_finite x)
    (zpowers_pow_eq_zpowers hkord).symm).1 h0
  exact mem_span_Irr_of_mem_virtualChars (hW.prodCharEta_mem_virtualChars hσ _ _)

theorem prodCharEtaColSum_apply_eq (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hq : (Nat.card ↥W1).Prime)
    {i₀ : Irr ↥W1} (hi₀ : i₀ ≠ principalIrr ↥W1) (j₀ : Irr ↥W2) {x : G}
    (h0 : hW.prodCharEta σ i₀ (principalIrr ↥W2) x = 0) :
    hW.prodCharEtaColSum σ j₀ x = (Nat.card ↥W1 : ℂ) * hW.prodCharEta σ i₀ j₀ x + 1 := by
  classical
  have := hW.finite_left
  have : Fintype (Irr ↥W1) := Fintype.ofFinite _
  have hnc := hW.forall_not_isConj_of_prodCharEta_apply_eq_zero hσ i₀ (principalIrr ↥W2) h0
  set t := hW.prodCharEta σ (principalIrr ↥W1) j₀ x with ht
  have hi₀val : hW.prodCharEta σ i₀ j₀ x = t - 1 := by
    rw [hW.prodCharEta_apply_eq_of_forall_not_isConj hσ i₀ j₀ hnc, h0, ht]
    ring
  have hentry : ∀ i : Irr ↥W1, hW.prodCharEta σ i j₀ x
      = (t - 1) + (if i = principalIrr ↥W1 then 1 else 0) := by
    intro i
    by_cases hip : i = principalIrr ↥W1
    · subst hip; rw [if_pos rfl]; ring
    · rw [if_neg hip, add_zero, hW.prodCharEta_apply_eq_of_forall_not_isConj hσ i j₀ hnc,
        hW.prodCharEta_axis_apply_eq_zero hσ hq hip hi₀ h0, ht]
      ring
  rw [hW.prodCharEtaColSum_eq_sum, Finset.sum_apply,
    Finset.sum_congr rfl fun i _ => hentry i,
    Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq' Finset.univ (principalIrr ↥W1)
      (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ _), Finset.card_univ, hi₀val,
    show Fintype.card (Irr ↥W1) = Nat.card ↥W1 by
      rw [← Nat.card_eq_fintype_card, hW.card_Irr_left]]
  ring

theorem apply_ne_zero_or_prodCharEta_axis_ne_zero_of_ne_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hq : (Nat.card ↥W1).Prime)
    {i₀ : Irr ↥W1} (hi₀ : i₀ ≠ principalIrr ↥W1) (j₀ : Irr ↥W2)
    {ε : ℂ} (hε : ε ≠ 0) {h : G → ℂ} {B₀ : Set G}
    (hB : ∀ y ∈ B₀, h y = ε * hW.prodCharEtaColSum σ j₀ y) {x : G} (hx : x ∈ B₀) :
    h x ≠ 0 ∨ hW.prodCharEta σ i₀ (principalIrr ↥W2) x ≠ 0 := by
  by_contra hcon
  rw [not_or, not_ne_iff, not_ne_iff] at hcon
  obtain ⟨hh0, h0⟩ := hcon
  have hcol : hW.prodCharEtaColSum σ j₀ x = 0 :=
    (mul_eq_zero.1 ((hB x hx).symm.trans hh0)).resolve_left hε
  rw [hW.prodCharEtaColSum_apply_eq hσ hq hi₀ j₀ h0] at hcol
  exact not_isIntegral_of_natCast_mul_add_one_eq_zero hq hcol
    (isIntegral_apply_of_mem_span_Irr
      (mem_span_Irr_of_mem_virtualChars (hW.prodCharEta_mem_virtualChars hσ i₀ j₀)) x)

theorem apply_ne_zero_or_prodCharEta_axis_ne_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hq : (Nat.card ↥W1).Prime)
    {i₀ : Irr ↥W1} (hi₀ : i₀ ≠ principalIrr ↥W1) {j₀ : Irr ↥W2} (_hj₀ : j₀ ≠ principalIrr ↥W2)
    {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {h : G → ℂ} {B₀ : Set G}
    (hB : ∀ y ∈ B₀, h y = ε * hW.prodCharEtaColSum σ j₀ y) {x : G} (hx : x ∈ B₀) :
    h x ≠ 0 ∨ hW.prodCharEta σ i₀ (principalIrr ↥W2) x ≠ 0 :=
  hW.apply_ne_zero_or_prodCharEta_axis_ne_zero_of_ne_zero hσ hq hi₀ j₀
    (by rcases hε with rfl | rfl <;> norm_num) hB hx

end IsCyclicTIPair

end CFSG.FeitThompson
