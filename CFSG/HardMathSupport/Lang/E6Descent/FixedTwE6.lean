module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.Chevalley

section Main


theorem eq_one_of_central_fixed_twE6 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p) {η : K ≃+* K}
    (hηo : orderOf η = p) {x : twistedE6RootGroup K σ}
    (hx : x ∈ fixedSubgroup (fieldActor σ η))
    (hc : ∀ y ∈ fixedSubgroup (fieldActor σ η), x * y = y * x) : x = 1 := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hηp : η ^ p = 1 := by rw [← hηo]; exact pow_orderOf_eq_one η
  have hη1 : η ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hηo
    exact hp.one_lt.ne hηo
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK'
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hηmem : η ∈ Subgroup.zpowers fr := by rw [hgen]; exact Subgroup.mem_top η
  obtain ⟨k, -, hkη⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hηmem)
  replace hkη : fr ^ k = η := hkη
  have hp2f : p ∣ 2 * f := by
    rw [← hηo, ← hord, ← hkη]
    exact orderOf_pow_dvd k
  have hpf : p ∣ f :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 (by omega)) hp2f
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hdk : 2 * d ∣ k := by
    have h1 : 2 * f ∣ k * p := by
      rw [← hord]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, hkη, hηp]
    rw [← hdp, ← mul_assoc] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hp.pos h1
  obtain ⟨j, rfl⟩ := hdk
  obtain ⟨T, hTdef⟩ : ∃ T, fr ^ d = T := ⟨_, rfl⟩
  have hT : ∀ c, T c = c ^ ℓ ^ d := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hfr d c
  have hTη : T ^ (2 * j) = η := by rw [← hTdef, ← pow_mul, ← hkη, mul_left_comm, mul_assoc]
  have hT2p : T ^ (2 * p) = 1 := by
    rw [← hTdef, ← pow_mul, show d * (2 * p) = orderOf fr by rw [hord, ← hdp]; ring,
      pow_orderOf_eq_one]
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨ε, hεdef⟩ : ∃ ε, T ^ (p + 1) = ε := ⟨_, rfl⟩
  have hε : ∀ c, ε c = c ^ ℓ ^ (d * (p + 1)) := fun c => by
    rw [← hεdef, ← hTdef, ← pow_mul]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  obtain ⟨κ, hκdef⟩ : ∃ κ, T ^ 2 = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d) := fun c => by
    rw [← hκdef, ← hTdef, ← pow_mul, mul_comm]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK', ← hdp, mul_assoc]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hdp, hσ]
  obtain ⟨-, -, hJC, -, hΓ', -, -, -, hNδ, -, hcent, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd0
      (by omega : 3 ≤ p) (hp.odd_of_ne_two (by omega)) K hKdp κ hκ σ hσdp
      (fixSubfieldRestrict T κ) hσ₀ ε hε
  have hεp : ε ^ p = 1 := by
    rw [← hεdef, ← pow_mul, show (p + 1) * p = 2 * p * (m + 1) by rw [hm]; ring, pow_mul, hT2p,
      one_pow]
  have hε2j : ε ^ (2 * j) = η := by
    rw [← hεdef, ← pow_mul, show (p + 1) * (2 * j) = 2 * j * (p + 1) by ring, pow_mul, hTη,
      pow_succ, hηp, one_mul]
  have hε1 : ε ≠ 1 := fun h => hη1 (by rw [← hε2j, h, one_pow])
  have hεo : orderOf ε = p := orderOf_eq_prime hεp hε1
  have hzp : Subgroup.zpowers η = Subgroup.zpowers ε :=
    zpowers_ringEquiv_eq_of_orderOf hℓ (by omega : 1 ≤ 2 * f) hK' hηo hεo
  have hfix : fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) =
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε) := by
    have := fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.E6) σ) hzp
    simpa only [fieldActorHom_apply] using this
  rw [hfix] at hx hc
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδ
  have hxδ : δ x = x := hx
  have hΓ'le : ∀ y ∈ (MonoidHom.eqLocus δ.toMonoidHom
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))), y ∈ fixedSubgroup δ :=
    fun y hy => hy
  have h1 : (MulAut.conj x : MulAut (twistedE6RootGroup K σ)) ∈ Subgroup.centralizer {δ} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine MulEquiv.ext fun y => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hxδ]
  have h2 : (MulAut.conj x : MulAut (twistedE6RootGroup K σ)) ∈
      Subgroup.centralizer (subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ)
        (fixSubfieldRestrict T κ) : Set (MulAut (twistedE6RootGroup K σ))) := by
    rintro _ ⟨j, hj, rfl⟩
    have hjΓ : j ∈ MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id (twistedE6RootGroup K σ)) := by
      have hj' : j ∈ ⁅MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id (twistedE6RootGroup K σ)),
          MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id (twistedE6RootGroup K σ))⁆ := by
        rw [hΓ']
        exact hj
      exact Subgroup.commutator_le.2 (fun a ha b hb =>
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
          (Subgroup.inv_mem _ hb)) hj'
    have hcomm : x * j = j * x := hc j hjΓ
    change (MulAut.conj j : MulAut (twistedE6RootGroup K σ)) * MulAut.conj x =
      MulAut.conj x * MulAut.conj j
    rw [← map_mul, ← map_mul, hcomm.symm]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hcent ▸ Subgroup.mem_inf.2 ⟨h1, h2⟩)
  have hδi : δ ^ i = fieldActor σ (ε ^ i) := by
    rw [hδ, ← fieldActorHom_apply, ← map_zpow, fieldActorHom_apply]
  have hΘ1 : Θ (MulAut.conj x) = 1 :=
    hΘ _ x 1 1 (by rw [map_one, mul_one, ← fieldActorHom_apply, map_one, mul_one])
  have hΘ2 : Θ (fieldActor σ (ε ^ i)) = ε ^ i :=
    hΘ _ 1 1 (ε ^ i) (by rw [map_one, map_one, one_mul, one_mul])
  have hconj : (MulAut.conj x : MulAut (twistedE6RootGroup K σ)) = fieldActor σ (ε ^ i) :=
    hi.symm.trans hδi
  have hεi : ε ^ i = 1 := by rw [← hΘ2, ← hconj, hΘ1]
  have hxc : (MulAut.conj x : MulAut (twistedE6RootGroup K σ)) = 1 := by
    rw [hconj, hεi, ← fieldActorHom_apply, map_one]
  exact mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (hxc.trans (map_one _).symm)

end Main

end CFSG.HardMathSupport.Lang.E6Descent
