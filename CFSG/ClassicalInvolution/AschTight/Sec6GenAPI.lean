module

public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2LayerSylow
public import CFSG.ClassicalInvolution.Asc77.AscSix66Aux
public import CFSG.ClassicalInvolution.Asc77.AscSixEta
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_conjSub_eq_of_isSylow2In [Finite G] {P V₁ V₂ : Subgroup G} (h₁ : IsSylow2In V₁ P)
    (h₂ : IsSylow2In V₂ P) : ∃ x ∈ P, conjSub x V₁ = V₂ := by
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥P) (AscL62.sylowOfIsSylow2In'' h₁)
    (AscL62.sylowOfIsSylow2In'' h₂)
  refine ⟨(x : G), x.2, ?_⟩
  have hV₁x : conjSub (x : G) V₁ ≤ P := by
    have := conjSub_mono (n := (x : G)) h₁.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have h1 : (conjSub (x : G) V₁).subgroupOf P = V₂.subgroupOf P := by
    rw [← conjSub_subgroupOf P x V₁]
    exact hx
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr hV₁x, inf_eq_left.mpr h₂.1] at h2

theorem exists_uniqueInvolution (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ z : G, IsUniqueInvolution K z :=
  (hΩ.omega1 K hK).1

theorem natCard_isSylow2In_eq (hΩ : HypOmegaGen Ω) {K J R R' : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hR : IsSylow2In R K) (hR' : IsSylow2In R' J) : Nat.card R = Nat.card R' :=
  hΩ.omega3 K hK J hJ R R' hR hR'

theorem mem_of_isSylow2In [Finite G] {K R : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hR : IsSylow2In R K) : z ∈ R := by
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers z) := isPGroup_zpowers_of_mul_self_eq_one hz.sq hz.ne_one
  have hzc : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hle := hR.natCard_le hz2 (Subgroup.zpowers_le.mpr hz.mem)
  exact AscL62.mem_of_uniqueInvolution_of_pGroup hz hR.1 hR.2.1 (by omega)

theorem isQuatSub_of_mem_RSet [Finite G] (hΩ : HypOmegaGen Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨⟨t, ht⟩, P, hP, hPnc⟩ := hΩ.omega1 J hJ
  have htR : t ∈ R := mem_of_isSylow2In ht hRJ
  have hord : orderOf (⟨t, htR⟩ : ↥R) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  have hrank : twoRank ↥R ≤ 1 := by
    refine CFSG.Semidihedral.CharacteristicSL2Layer.twoRank_le_one_of_unique_involution
      ⟨t, htR⟩ hord fun x hx => ?_
    have hx1 : (x : G) ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      omega
    have hxx : (x : G) * (x : G) = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx, pow_two] at this
      exact congrArg Subtype.val this
    exact Subtype.ext ((ht.unique _ (hRJ.1 x.2) hxx).resolve_left hx1)
  rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion ↥R hRJ.2.1 hrank
    with hcyc | ⟨e, he, hiso⟩
  · exfalso
    obtain ⟨x, -, hx⟩ := exists_conjSub_eq_of_isSylow2In hRJ hP
    have hcycP : IsCyclic ↥P := hx ▸ AscL62.isCyclic_conjSub x hcyc
    exact hPnc ⟨⟨fun a b => Subtype.ext (AscL62.cyclic_comm hcycP a.2 b.2)⟩⟩
  · exact ⟨e - 2, by omega, hiso⟩

theorem eight_le_of_mem_RSet [Finite G] (hΩ : HypOmegaGen Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  (isQuatSub_of_mem_RSet hΩ hR).eight_le

theorem center_two [Finite G] (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∀ w ∈ K, IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) →
      w = 1 ∨ w = z := by
  intro w hwK hw2 hcomm
  obtain ⟨R, hR, hwR⟩ := IsSylow2In.exists_ge hw2 (Subgroup.zpowers_le.mpr hwK)
  have hwR' : w ∈ R := hwR (Subgroup.mem_zpowers w)
  have hq := isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  have hcen : ∀ y ∈ R, w * y = y * w := by
    intro y hy
    have h1 : ⁅w, y⁆ ∈ oddCoreOf K := hcomm y (hR.1 hy)
    have h2 : ⁅w, y⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hwR' hy) (R.inv_mem hwR')) (R.inv_mem hy)
    have h3 : IsPGroup 2 (Subgroup.zpowers ⁅w, y⁆) :=
      hR.2.1.to_le (Subgroup.zpowers_le.mpr h2)
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1 h3)
  exact hz.unique w hwK (hq.sq_eq_one_of_central hwR' hcen)

theorem exists_noncentral [Finite G] (hΩ : HypOmegaGen Ω) {J : Subgroup G} (hJ : J ∈ Ω)
    {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A) (hA3 : 3 ≤ Nat.card A) :
    ∃ v ∈ A, ¬ ∀ w ∈ J, v * w = w * v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht⟩ := exists_uniqueInvolution hΩ hJ
  obtain ⟨R, hR, hAR⟩ := IsSylow2In.exists_ge hA2 hAJ
  have hq := isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ hR)
  have := natCard_subgroup_le_two_of_subset (A := A) (a := 1) (b := t) fun v hv =>
    ht.unique v (hAJ hv) (hq.sq_eq_one_of_central (hAR hv) fun y hy => hcon v hv y (hR.1 hy))
  omega

theorem card_le_two_of_le_inf [Finite G] (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card ↥(K ⊓ J) := Subgroup.card_dvd_of_le (le_inf hAK hAJ)
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  rw [hn] at hdvd
  have h1 := (padicValNat_dvd_iff_le hN).mp hdvd
  have h2 := (hΩ.omega4 K hK J hJ hKJ).1
  have hn1 : n ≤ 1 := h1.trans h2
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 2 := by norm_num

theorem eq_of_le_of_le [Finite G] (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : K = J := by
  by_contra hne
  have := card_le_two_of_le_inf hΩ hK hJ hne hA hAK hAJ
  omega

theorem le_normalizer_of_le_centralizer [Finite G] (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hz : IsUniqueInvolution K z)
    {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A) (hA3 : 3 ≤ Nat.card A)
    (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) : A ≤ Subgroup.normalizer (K : Set G) := by
  refine le_of_noncentral_mem (J := J) (exists_noncentral hΩ hJ hAJ hA2 hA3) ?_
  intro v hv hnc
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := hA2.to_le (Subgroup.zpowers_le.mpr hv)
  exact hΩ.omega5 K hK J hJ hKJ z hz v (hAJ hv) hnc hv2
    (Subgroup.mem_centralizer_singleton_iff.mp (hAc hv))

theorem comm_le_oddCore_of_twin [Finite G] (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ J) (x := z) ⟨hzK.mem, hzJ.mem⟩
    rwa [hz2] at this
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h1 := one_le_padicValNat_of_dvd hN hdvd
  obtain ⟨h2, h3⟩ := hΩ.omega4 K hK J hJ hKJ
  exact h3 (le_antisymm h2 h1)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
