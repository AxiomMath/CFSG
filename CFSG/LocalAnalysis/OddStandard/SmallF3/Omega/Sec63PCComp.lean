module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSub
public import CFSG.GH74.Orders.LieType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec63PC_le_of_isPerfect_of_card_quotient {C : Type*} [Group C] [Finite C]
    {F K : Subgroup C} [F.Normal] {n : ℕ} (hq : Nat.card (C ⧸ F) = 2 ^ n)
    (hK : Group.IsPerfect K) : K ≤ F := by
  have hp : IsPGroup 2 (C ⧸ F) := IsPGroup.of_card hq
  have : Group.IsNilpotent (C ⧸ F) := hp.isNilpotent
  have hmap : Group.IsPerfect (K.map (QuotientGroup.mk' F)) := Group.IsPerfect.map _
  by_contra hnot
  have hne : K.map (QuotientGroup.mk' F) ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hnot
  have : Nontrivial (K.map (QuotientGroup.mk' F)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact Group.IsPerfect.not_isSolvable (K.map (QuotientGroup.mk' F)) inferInstance

private theorem sec63PC_mem_of_orderOf_prime_of_normal {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp2 : ¬ p ^ 2 ∣ Nat.card L) (R : Subgroup L) [R.Normal]
    (hR : p ∣ Nat.card R) {y : L} (hy : orderOf y = p) : y ∈ R := by
  have hcard : Nat.card L = Nat.card R * Nat.card (L ⧸ R) := by
    rw [mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup R
  have hq : ¬ p ∣ Nat.card (L ⧸ R) := fun h => hp2 (by
    rw [hcard, pow_two]
    exact Nat.mul_dvd_mul hR h)
  have h1 : orderOf (QuotientGroup.mk y : L ⧸ R) ∣ p :=
    hy ▸ orderOf_map_dvd (QuotientGroup.mk' R) y
  have h2 : orderOf (QuotientGroup.mk y : L ⧸ R) ∣ Nat.card (L ⧸ R) := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
  · exact absurd (h ▸ h2) hq

private theorem sec63PC_mem_of_isSubnormal_of_orderOf_prime {L : Type*} [Group L] [Finite L]
    {p : ℕ} (hp : p.Prime) (hp2 : ¬ p ^ 2 ∣ Nat.card L) {K : Subgroup L} (hK : K.IsSubnormal)
    (hpK : p ∣ Nat.card K) {y : L} (hy : orderOf y = p) : y ∈ K := by
  revert hpK
  induction hK with
  | top => exact fun _ => mem_top y
  | step H M hHM _ hN ih =>
    intro hpH
    have hyM : y ∈ M := ih (hpH.trans (Subgroup.card_dvd_of_le hHM))
    have : (H.subgroupOf M).Normal := hN
    have hM2 : ¬ p ^ 2 ∣ Nat.card M := fun h => hp2 (h.trans (Subgroup.card_subgroup_dvd_card M))
    have hHp : p ∣ Nat.card (H.subgroupOf M) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hHM).toEquiv]
    have hy' : orderOf (⟨y, hyM⟩ : M) = p := by rw [Subgroup.orderOf_mk, hy]
    exact Subgroup.mem_subgroupOf.mp
      (sec63PC_mem_of_orderOf_prime_of_normal hp hM2 (H.subgroupOf M) hHp hy')

theorem sec63PC_component_eq [Finite G] {H L K : Subgroup G} (hLH : L ≤ H)
    (hLn : ∀ h ∈ H, ∀ x ∈ L, h * x * h⁻¹ ∈ L) (hpow : ∃ a : ℕ, L.relIndex H = 2 ^ a)
    (hs : IsSimpleGroup ↥L) (hK : IsComponentIn K H) : K = L := by
  let F : Subgroup ↥H := L.subgroupOf H
  haveI hFnorm : F.Normal := ⟨fun n hn g => hLn (g : G) g.2 (n : G) hn⟩
  obtain ⟨a, ha⟩ := hpow
  have hq : Nat.card (↥H ⧸ F) = 2 ^ a := by
    simpa [F, Subgroup.relIndex, Subgroup.index] using ha
  have hKsub : K.subgroupOf H ≤ F :=
    sec63PC_le_of_isPerfect_of_card_quotient hq hK.2.1.1
  have hKle : K ≤ L := by
    intro x hx
    have hxH : x ∈ H := hK.1 hx
    exact hKsub (show (⟨x, hxH⟩ : ↥H) ∈ K.subgroupOf H from hx)
  have hsub : (K.subgroupOf L).IsSubnormal := by
    have h1 : (K.subgroupOf H).IsSubnormal := hK.2.2
    have h2 : ((K.subgroupOf H).comap (Subgroup.inclusion hLH)).IsSubnormal :=
      h1.comap (Subgroup.inclusion hLH)
    have heq : (K.subgroupOf H).comap (Subgroup.inclusion hLH) = K.subgroupOf L := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    rwa [heq] at h2
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hs hsub with hbot | htop
  · exfalso
    have hdisj : Disjoint K L := (Subgroup.subgroupOf_eq_bot (H := K) (K := L)).1 hbot
    have hKbot : K = ⊥ := by
      rw [← inf_eq_left.mpr hKle]
      exact disjoint_iff.mp hdisj
    exact hK.ne_bot hKbot
  · exact le_antisymm hKle (Subgroup.subgroupOf_eq_top.mp htop)

theorem sec63PC_card_of_isL29 [Finite G] {V : Subgroup G} (hV : IsL29 V) :
    ∃ m : ℕ, Odd m ∧ Nat.card V = 360 * m := by
  have hcard : Nat.card (↥V ⧸ oddCore ↥V) = 360 := by
    rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num : (2 : ℕ) ≠ 0) hV]
    decide
  refine ⟨Nat.card (oddCore ↥V), ?_, ?_⟩
  · exact CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  · have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore ↥V)
    rw [hcard] at h
    exact h

theorem sec63PC_card_dvd_of_component [Finite G] {C V : Subgroup G} (hC : IsComponentIn V C)
    (hV : IsL29 V) : 360 ∣ Nat.card C := by
  obtain ⟨m, _, hcard⟩ := sec63PC_card_of_isL29 hV
  have h1 : Nat.card V ∣ Nat.card C := Subgroup.card_dvd_of_le hC.1
  rw [hcard] at h1
  exact (dvd_mul_right 360 m).trans h1

theorem sec63PC_fact_of_not_five_dvd [Finite G] {Y : Subgroup G} {t : G}
    (h5 : ¬ 5 ∣ Nat.card ↥(Y ⊓ centralizer ({t} : Set G))) : Sec63PCFact Y t := by
  unfold Sec63PCFact
  intro V hV hL b hb hb2
  exfalso
  exact h5 ((by norm_num : 5 ∣ 360).trans (sec63PC_card_dvd_of_component hV hL))

theorem sec63PC_fact_of_five [Finite G] {Y : Subgroup G} {t : G} {S : Set G}
    (hS : ∀ x ∈ S, x ∈ Y ⊓ centralizer ({t} : Set G) ∧ orderOf x = 5)
    (h25 : 360 ∣ Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) →
      ¬ 25 ∣ Nat.card ↥(Y ⊓ centralizer ({t} : Set G)))
    (h16 : 16 ∣ Nat.card ↥(closure S)) : Sec63PCFact Y t := by
  unfold Sec63PCFact
  intro V hV hL b hb hb2
  exfalso
  let C : Subgroup G := Y ⊓ centralizer ({t} : Set G)
  have hV' : IsComponentIn V C := hV
  obtain ⟨m, hm, hcardV⟩ := sec63PC_card_of_isL29 hL
  have h360 : 360 ∣ Nat.card C := sec63PC_card_dvd_of_component hV' hL
  have h25C : ¬ 25 ∣ Nat.card C := h25 h360
  have hSV : S ⊆ V := by
    intro x hx
    obtain ⟨hxC, hx5⟩ := hS x hx
    have hp2 : ¬ 5 ^ 2 ∣ Nat.card ↥C := by
      rw [show 5 ^ 2 = 25 by norm_num]
      exact h25C
    have hcardVC : Nat.card (V.subgroupOf C) = Nat.card V := sec63PT_card_subgroupOf hV'.1
    have h5V : 5 ∣ Nat.card V := by
      rw [hcardV]
      exact dvd_mul_of_dvd_left (by norm_num : 5 ∣ 360) m
    have hpK : 5 ∣ Nat.card (V.subgroupOf C) := by
      rw [hcardVC]
      exact h5V
    have hy : orderOf (⟨x, hxC⟩ : ↥C) = 5 := by
      rw [Subgroup.orderOf_mk]
      exact hx5
    have hyV : (⟨x, hxC⟩ : ↥C) ∈ V.subgroupOf C :=
      sec63PC_mem_of_isSubnormal_of_orderOf_prime Nat.prime_five hp2 hV'.2.2 hpK hy
    exact hyV
  have hclV : closure S ≤ V := by
    rw [Subgroup.closure_le]
    exact hSV
  have h16V : 16 ∣ Nat.card V :=
    h16.trans (Subgroup.card_dvd_of_le hclV)
  obtain ⟨k, rfl⟩ := hm
  rw [hcardV] at h16V
  omega

end CFSG.OddStandard.SmallF3.Omega
