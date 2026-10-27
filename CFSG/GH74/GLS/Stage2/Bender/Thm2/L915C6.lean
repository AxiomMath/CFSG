module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C3
public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Local.P34Two
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203PSp4

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement Pointwise

@[expose] def NoL3InPSp4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (q : ℕ), Odd q → 5 ≤ q → IVK.IsPSp4 K q →
    ∀ (X : Type) [Group X] [Finite X] (f : X →* K), Function.Injective f →
      Odd (Nat.card ↥(center X)) →
      ∀ p n : ℕ, p.Prime → p ≠ 2 → 1 ≤ n → LieModel (X ⧸ center X) .PSL 3 p n → False

namespace L915

section CaseA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pPrimeCoreOf_conj {H : Subgroup G} {h : G} (hh : h ∈ H) {o : G} (ho : o ∈ pPrimeCoreOf 2 H) :
    h * o * h⁻¹ ∈ pPrimeCoreOf 2 H := by
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨h, hh⟩ * o' * ⟨h, hh⟩⁻¹, (inferInstance : (pPrimeCore 2 ↥H).Normal).conj_mem o' ho' ⟨h, hh⟩, rfl⟩

theorem odd_orderOf_of_mem_pPrimeCoreOf {H : Subgroup G} {o : G} (ho : o ∈ pPrimeCoreOf 2 H) :
    Odd (orderOf o) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o', ho', rfl⟩ := ho
  have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥H)) := pPrimeCore_coprime_card (p := 2) (G := ↥H)
  have h1 : orderOf (o' : ↥H) ∣ Nat.card (pPrimeCore 2 ↥H) := Subgroup.orderOf_dvd_natCard _ ho'
  have h2 : Odd (Nat.card (pPrimeCore 2 ↥H)) := Nat.coprime_two_left.mp hc
  have h3 : orderOf (((o' : ↥H) : G)) = orderOf (o' : ↥H) := Subgroup.orderOf_coe (o' : ↥H)
  show Odd (orderOf (((o' : ↥H) : G)))
  rw [h3]
  exact Odd.of_dvd_nat h2 h1

theorem false_of_caseA {z : G} {H J : Subgroup G} (hCH : Cen z ≤ H) (hJH : J ≤ H)
    (hJ : IsQuasisimple ↥J) (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1)
    (hA : ∀ h ∈ H, ∃ c ∈ Cen z, ∃ o ∈ pPrimeCoreOf 2 H, h = c * o) : False := by
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz, pow_two] at h1
    exact h1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hzH : z ∈ H := hJH hzJ
  set O := pPrimeCoreOf 2 H with hO
  have hcomm : ∀ j ∈ J, ⁅j, z⁆ ∈ O := by
    intro j hj
    obtain ⟨c, hc, o, ho, hjco⟩ := hA j (hJH hj)
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcz' : c⁻¹ * z⁻¹ = z⁻¹ * c⁻¹ := (Commute.inv_inv (show Commute c z from hcz)).eq
    have e : ⁅j, z⁆ = c * (o * (z * o⁻¹ * z⁻¹)) * c⁻¹ := by
      rw [hjco, commutatorElement_def]
      calc c * o * z * (c * o)⁻¹ * z⁻¹ = c * o * z * o⁻¹ * (c⁻¹ * z⁻¹) := by group
        _ = c * o * z * o⁻¹ * (z⁻¹ * c⁻¹) := by rw [hcz']
        _ = c * (o * (z * o⁻¹ * z⁻¹)) * c⁻¹ := by group
    rw [e]
    have h1 : z * o⁻¹ * z⁻¹ ∈ O := by
      have := pPrimeCoreOf_conj hzH (O.inv_mem ho)
      exact this
    exact pPrimeCoreOf_conj (hCH hc) (O.mul_mem ho h1)
  set N : Subgroup ↥J := (O ⊓ J).subgroupOf J with hN
  have hNnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, (g * n * g⁻¹).2⟩
    have := pPrimeCoreOf_conj (hJH g.2) hn.1
    simpa using this
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hzN : (⟨z, hzJ⟩ : ↥J) ∈ N := by rw [htop]; trivial
    rw [hN, Subgroup.mem_subgroupOf] at hzN
    have := odd_orderOf_of_mem_pPrimeCoreOf hzN.1
    rw [hz] at this
    exact absurd this (by decide)
  have hNc : N ≤ center ↥J := (CFSG.LocalCores.quasisimple_normal_subgroups hJ hNnorm).resolve_left hNtop
  have hJcomm : ⁅J, zpowers z⁆ ≤ centralizer (J : Set G) := by
    refine Subgroup.commutator_le.mpr fun j hj g hg => ?_
    have hg' : g = 1 ∨ g = z := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have h1 := zpow_mod_orderOf z k
      rw [hz] at h1
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [← h1]
        have : (k % ((2 : ℕ) : ℤ)) = 0 := by exact_mod_cast h
        rw [this, zpow_zero]
      · right
        rw [← h1]
        have : (k % ((2 : ℕ) : ℤ)) = 1 := by exact_mod_cast h
        rw [this, zpow_one]
    rcases hg' with h | h
    · rw [h, commutatorElement_one_right]
      exact one_mem _
    · rw [h]
      have hcJ : ⁅j, z⁆ ∈ J := by
        rw [commutatorElement_def]
        exact J.mul_mem (J.mul_mem (J.mul_mem hj hzJ) (J.inv_mem hj)) (J.inv_mem hzJ)
      have hmem : (⟨⁅j, z⁆, hcJ⟩ : ↥J) ∈ N := by
        rw [hN, Subgroup.mem_subgroupOf]
        exact ⟨hcomm j hj, hcJ⟩
      have hmem' := Subgroup.mem_center_iff.mp (hNc hmem)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := congrArg Subtype.val (hmem' ⟨x, hx⟩)
      simpa [Subgroup.coe_mul] using this
  have hzc : zpowers z ≤ centralizer (J : Set G) :=
    le_centralizer_of_commutator_le_centralizer hJ.1 hJcomm
  have hzcent : ∀ g ∈ J, z * g = g * z := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (hzc (Subgroup.mem_zpowers z)) g hg).symm
  exact hz1 (hnoc z hzJ hzcent hz2)

end CaseA

section Transport

theorem transport_center {X Y : Type} [Group X] [Group Y] [Finite X] (hX : Group.IsPerfect X)
    (ρ : X →* Y) (hs : Function.Surjective ρ) (hker : ρ.ker ≤ center X)
    (hodd : Odd (Nat.card ↥(center X))) {p n : ℕ}
    (hLie : LieModel (X ⧸ center X) .PSL 3 p n) :
    Odd (Nat.card ↥(center Y)) ∧ LieModel (Y ⧸ center Y) .PSL 3 p n := by
  have hcenter : (center Y).comap ρ = center X :=
    CFSG.LocalCores.comap_center_eq_of_perfect hX ρ hs hker
  refine ⟨?_, Odd87.Transport.lieModel_of_mulEquiv (quotientCenterEquiv hX ρ hs hker) hLie⟩
  have hm : (center X).map ρ = center Y := by
    rw [← hcenter]
    exact Subgroup.map_comap_eq_self_of_surjective hs _
  rw [← hm]
  exact Odd.of_dvd_nat hodd (Subgroup.card_map_dvd (center X) ρ)

end Transport

section CaseC

variable {G : Type} [Group G] [Finite G]

open CFSG.GH74.GLS.Stage2.Local.P34 in
theorem false_of_caseC (hK2 : NoL3InPSp4) {z : G} {H J : Subgroup G} (hJH : J ≤ H)
    (hJ : IsQuasisimple ↥J) (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1)
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 p n) {q : ℕ} (hqodd : Odd q) (hq5 : 5 ≤ q)
    (hpsp : IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := HBar H with hY
  set Kb := generalizedFitting Y with hKb
  obtain ⟨hs, hperf⟩ := Final.Thm4.isSimple_isPerfect_of_isPSp4 (by omega : 3 < q) hpsp
  have hF : fittingSubgroup Y = ⊥ := Final.Thm4.fitting_quot_eq_bot hs hperf
  have hlayer : generalizedFitting Y = layer Y := generalizedFitting_eq_layer hF
  have hexists : ∃ A : Subgroup Y, IsComponent A := by
    by_contra hno
    push Not at hno
    have hl : layer Y = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall hno
    have hbot : Kb = ⊥ := by rw [hKb, hlayer, hl]
    have h1 : Nontrivial ↥Kb := hs.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot Kb).mp h1 hbot
  have hall : ∀ L : Subgroup Y, IsComponent L → L = Kb := by
    intro L hL
    have hLle : L ≤ Kb := by
      rw [hKb, hlayer]
      exact CFSG.LocalCores.component_le_layer hL
    have hnorm : Kb ≤ normalizer (L : Set Y) := by
      rw [hKb, hlayer]
      refine sSup_le fun M hM => ?_
      rcases CFSG.LocalCores.distinct_components_commute hM hL with rfl | hML
      · exact Subgroup.le_normalizer
      · intro m hm
        exact Subgroup.centralizer_le_normalizer _
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hML hm)
    have hLn : (L.subgroupOf Kb).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mpr hnorm
    have := hLn
    rcases hs.eq_bot_or_eq_top_of_normal (L.subgroupOf Kb) with h | h
    · exfalso
      have hLbot : L = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hLle hx⟩ : ↥Kb) ∈ L.subgroupOf Kb := hx
        rw [h, Subgroup.mem_bot] at this
        simpa using congrArg Subtype.val this
      have h1 : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
      exact (Subgroup.nontrivial_iff_ne_bot L).mp h1 hLbot
    · refine le_antisymm hLle fun x hx => ?_
      have : (⟨x, hx⟩ : ↥Kb) ∈ L.subgroupOf Kb := by rw [h]; trivial
      exact this
  have hK : IsComponent Kb := by
    obtain ⟨A, hA⟩ := hexists
    rw [← hall A hA]
    exact hA
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Kb) :=
    (Final.Thm6.L203.psp4Facts Y Kb q hqodd hq5 hpsp).1
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 hJ.1
  have h1 : ⁅barIn H J, barIn H J⁆ = barIn H J := commutator_barIn H hJH hJperf
  have hle : barIn H J ≤ Kb := perfect_le_of_unique hF hK hall hOut h1
  set π : ↥H →* Y := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  set J' : Subgroup ↥H := J.subgroupOf H with hJ'
  let eJ : ↥J ≃* ↥J' := (Subgroup.subgroupOfEquivOfLe hJH).symm
  let ρ : ↥J →* ↥(barIn H J) := (π.subgroupMap J').comp eJ.toMonoidHom
  have hsurj : Function.Surjective ρ :=
    (π.subgroupMap_surjective J').comp eJ.surjective
  have hker : ρ.ker ≤ center ↥J := by
    have hkn : ρ.ker.Normal := MonoidHom.normal_ker ρ
    have hktop : ρ.ker ≠ ⊤ := by
      intro htop
      have hzk : (⟨z, hzJ⟩ : ↥J) ∈ ρ.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker] at hzk
      have hz1 : π ⟨z, hJH hzJ⟩ = 1 := by
        have := congrArg Subtype.val hzk
        exact this
      have hzO : (⟨z, hJH hzJ⟩ : ↥H) ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hz1
      have := odd_orderOf_of_mem_pPrimeCoreOf (H := H) (o := z) ⟨⟨z, hJH hzJ⟩, hzO, rfl⟩
      rw [hz] at this
      exact absurd this (by decide)
    exact (CFSG.LocalCores.quasisimple_normal_subgroups hJ hkn).resolve_left hktop
  have hZodd : Odd (Nat.card ↥(center ↥J)) := by
    by_contra hne
    have heven : Even (Nat.card ↥(center ↥J)) := Nat.not_odd_iff_even.mp hne
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥J)) 2 heven.two_dvd
    set c' : ↥J := (c : ↥J) with hc'
    set g : G := (c' : G) with hg
    have hog : orderOf g = 2 := by
      rw [hg, Subgroup.orderOf_coe, hc', Subgroup.orderOf_coe, hc]
    have hg2 : g * g = 1 := by
      have := pow_orderOf_eq_one g
      rw [hog, pow_two] at this
      exact this
    have hgJ : g ∈ J := c'.2
    have hgc : ∀ x ∈ J, g * x = x * g := by
      intro x hx
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨x, hx⟩)
      simpa [hg, hc', Subgroup.coe_mul] using this.symm
    have := hnoc g hgJ hgc hg2
    rw [this, orderOf_one] at hog
    omega
  obtain ⟨hZodd', hLie'⟩ := transport_center hJ.1 ρ hsurj hker hZodd hLie
  exact hK2 ↥Kb q hqodd hq5 hpsp ↥(barIn H J) (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    hZodd' p n hp hp2 hn hLie'

end CaseC

theorem noL3Overgroup_of (h34 : Leaf_Prop34) (hK2 : NoL3InPSp4) : NoL3Overgroup := by
  intro G _ _ z k S ctx H hCH hHne J hJH hJ hzJ hnoc p n hp hp2 hn hLie
  have hz : orderOf z = 2 := ctx.central.1
  rcases h34 G z k S ctx H hCH hHne with hA | hD | ⟨ε, q, L₁, L₂, hk, hL4, hq4, hq3, hpsp, hcoat, hLle, hnS, hO2, hFm⟩
  · exact false_of_caseA hCH hJH hJ hzJ hz hnoc hA
  · exact Final.Thm4.not_isDihedral_S ctx hD
  · have hqodd : Odd q := by
      split_ifs at hq4 <;> exact Nat.odd_iff.mpr (by omega)
    exact false_of_caseC hK2 hJH hJ hzJ hz hnoc hp hp2 hn hLie hqodd (by
      rcases hqodd with ⟨m, hm⟩
      omega) hpsp

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
