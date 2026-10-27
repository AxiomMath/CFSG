module

public import CFSG.ClassicalInvolution.Balance.Prop311
public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.ClassicalInvolution.Balance.LocalBalance

open CFSG

section Fixed

variable {X : Type*} [Group X]

theorem eq_one_of_mem_of_isPGroup_of_odd {R O : Subgroup X} (hR : IsPGroup 2 R)
    (hO : Odd (Nat.card O)) {c : X} (hcR : c ∈ R) (hcO : c ∈ O) : c = 1 := by
  have hodd : Odd (orderOf c) := by
    have := orderOf_dvd_natCard (⟨c, hcO⟩ : O)
    rw [← Subgroup.orderOf_coe (⟨c, hcO⟩ : O)] at this
    exact hO.of_dvd_nat this
  obtain ⟨k, hk⟩ := hR ⟨c, hcR⟩
  have h2 : orderOf c ∣ 2 ^ k := by
    have : orderOf (⟨c, hcR⟩ : R) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rwa [← Subgroup.orderOf_coe (⟨c, hcR⟩ : R)] at this
  obtain ⟨j, hj, hj2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have : j = 0 := by
    by_contra hj0
    rw [hj2] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  rw [this, pow_zero, orderOf_eq_one_iff] at hj2
  exact hj2

theorem commute_pCore_of_mem_involutionOddCore [Finite X] {f d : X} (hf : orderOf f = 2)
    (hd : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore f) :
    ∀ q ∈ CFSG.pCore 2 X, d * q * d⁻¹ = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hQp : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have hO : d ∈ oddCoreCentralizer (Subgroup.zpowers f) := by
    rwa [← involutionOddCore_eq_oddCoreCentralizer]
  have hcen := centralizer_zpowers_eq f
  have hdC : d ∈ Subgroup.centralizer ({f} : Set X) := by
    rw [← hcen]
    exact oddCoreCentralizer_le_centralizer _ hO
  have hdf : d * f = f * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
  have hdodd : ¬ 2 ∣ orderOf d := by
    have hdvd := orderOf_dvd_natCard (⟨d, hO⟩ : oddCoreCentralizer (Subgroup.zpowers f))
    rw [← Subgroup.orderOf_coe] at hdvd
    have hodd : Odd (orderOf d) := (odd_card_oddCoreCentralizer _).of_dvd_nat hdvd
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  intro q hq
  let A := Subgroup.zpowers d
  let B := Subgroup.zpowers f
  let α : A →* MulAut (CFSG.pCore 2 X) := MulAut.conjNormal.comp A.subtype
  let β : B →* MulAut (CFSG.pCore 2 X) := MulAut.conjNormal.comp B.subtype
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
    change MulAut.conjNormal (d ^ i) * MulAut.conjNormal (f ^ j) =
      MulAut.conjNormal (f ^ j) * MulAut.conjNormal (d ^ i)
    rw [← map_mul, ← map_mul, ((Commute.zpow_zpow (hdf : Commute d f)) i j).eq]
  have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    rintro ⟨a, i, rfl⟩ r hr
    have hrf : (r : X) ∈ Subgroup.centralizer ({f} : Set X) := by
      have := congrArg Subtype.val (hr ⟨f, Subgroup.mem_zpowers f⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change f * r * f⁻¹ = r at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hrd : d * r = r * d := by
      have hc1 : d * (r : X) * d⁻¹ * (r : X)⁻¹ ∈ CFSG.pCore 2 X :=
        mul_mem (hQn.conj_mem r r.2 d) (inv_mem r.2)
      have hc2 : d * (r : X) * d⁻¹ * (r : X)⁻¹ ∈ oddCoreCentralizer (Subgroup.zpowers f) := by
        have h1 : (r : X) * d⁻¹ * (r : X)⁻¹ ∈ oddCoreCentralizer (Subgroup.zpowers f) :=
          conj_mem_oddCoreCentralizer_of_mem_centralizer (hcen ▸ hrf) (inv_mem hO)
        have : d * (r : X) * d⁻¹ * (r : X)⁻¹ = d * ((r : X) * d⁻¹ * (r : X)⁻¹) := by group
        rw [this]
        exact mul_mem hO h1
      have h1 := eq_one_of_mem_of_isPGroup_of_odd hQp (odd_card_oddCoreCentralizer _) hc1 hc2
      have h2 : d * (r : X) * d⁻¹ = r := by
        rwa [mul_inv_eq_one] at h1
      rwa [mul_inv_eq_iff_eq_mul] at h2
    apply Subtype.ext
    change d ^ i * r * (d ^ i)⁻¹ = r
    rw [((Commute.zpow_left (hrd : Commute d r)) i).eq, mul_inv_cancel_right]
  have hA : ¬ 2 ∣ Nat.card A := by
    rw [Nat.card_zpowers]
    exact hdodd
  have hB : IsPGroup 2 B := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hf, pow_one]⟩
  have h := CFSG.GroupTheory.thompson_A_times_B hQp hA hB α β hcomm hfix ⟨d, Subgroup.mem_zpowers _⟩
  have := congrArg (fun φ : MulAut (CFSG.pCore 2 X) => ((φ ⟨q, hq⟩ : CFSG.pCore 2 X) : X)) h
  simpa [α, MulAut.conjNormal_apply] using this

end Fixed

section Final

variable {X : Type*} [Group X] [Finite X]

theorem eq_bot_of_centralizes_pCore_of_centralizes_components (hO : CFSG.pPrimeCore 2 X = ⊥)
    {D : Subgroup X} (hD : Odd (Nat.card D))
    (hQ : D ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X))
    (hL : ∀ L : Subgroup X, CFSG.IsComponent L → D ≤ Subgroup.centralizer (L : Set X)) :
    D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.fittingSubgroup X = CFSG.pCore 2 X := CFSG.Fitting_eq_pcore X 2 hO
  have hFc : CFSG.generalizedFitting X ≤ Subgroup.centralizer (D : Set X) := by
    refine sup_le ?_ (sSup_le fun L hL' => ?_)
    · rw [hF]
      exact Subgroup.le_centralizer_iff.mp hQ
    · exact Subgroup.le_centralizer_iff.mp (hL L hL')
  have hDF : D ≤ CFSG.fittingSubgroup X := by
    have h1 : D ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) :=
      Subgroup.le_centralizer_iff.mp hFc
    have h2 := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting X
    rw [← CFSG.generalizedFitting_eq_componentClassification] at h2
    exact h1.trans h2
  rw [hF] at hDF
  refine (Subgroup.eq_bot_iff_forall D).mpr fun d hd => ?_
  exact eq_one_of_mem_of_isPGroup_of_odd CFSG.pCore_isPGroup hD (hDF hd) hd

end Final

end CFSG.ClassicalInvolution.Balance.LocalBalance
