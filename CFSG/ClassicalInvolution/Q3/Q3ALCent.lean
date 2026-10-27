module

public import CFSG.ClassicalInvolution.Q3.Q3NTLemmaD
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AL

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

section Pairing

variable {G : Type} [Group G]

theorem commutator_mul_right_eq (g h₁ h₂ : G) :
    ⁅g, h₁ * h₂⁆ = ⁅g, h₁⁆ * (h₁ * ⁅g, h₂⁆ * h₁⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutator_pow_eq {N : Subgroup G} {a b : G} (haN : ∀ x ∈ N, a * x = x * a)
    (hba : ⁅b, a⁆ ∈ N) (n : ℕ) : ⁅b, a ^ n⁆ = ⁅b, a⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmem : ⁅b, a⁆ ^ n ∈ N := N.pow_mem hba n
    have hcomm : a * ⁅b, a ^ n⁆ * a⁻¹ = ⁅b, a ^ n⁆ := by
      rw [ih, mul_inv_eq_iff_eq_mul]
      exact haN _ hmem
    rw [pow_succ', commutator_mul_right_eq, hcomm, ih, pow_succ']

theorem commutes_of_commutator_mem_of_centralizes {N : Subgroup G} {a b : G}
    (haN : ∀ x ∈ N, a * x = x * a) (hba : ⁅b, a⁆ ∈ N)
    (hcop : Nat.Coprime (orderOf a) (Nat.card N)) : a * b = b * a := by
  have hpow := commutator_pow_eq haN hba (orderOf a)
  rw [pow_orderOf_eq_one, commutatorElement_one_right] at hpow
  have h1 : orderOf ⁅b, a⁆ ∣ orderOf a := orderOf_dvd_of_pow_eq_one hpow.symm
  have h2 : orderOf ⁅b, a⁆ ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hba
  have h3 : orderOf ⁅b, a⁆ = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : ⁅b, a⁆ = 1 := orderOf_eq_one_iff.mp h3
  exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm

end Pairing

section Local

variable {G : Type} [Group G]


theorem commutes_locImg_of_ne [Finite G] (hMFZ : RouteD.Gaps.FundNoncentral 3)
    {Ω : Set (Subgroup G)} {ι : Type} {l : G}
    (D : LieSystemData3 ι (locQuot Ω l) (locFamily Ω l)) {L M : Subgroup G} {m : G}
    (hL : L ∈ centralizingMembers Ω {l}) (hM : M ∈ centralizingMembers Ω {l})
    (hl : IsClassicalMember3 L l) (hm : IsClassicalMember3 M m) (hne : l ≠ m) :
    Commutes (locImg Ω l L) (locImg Ω l M) := by
  have hlY : l ∈ locLayer Ω l := le_centralizingLayer hL hl.mem
  have hmY : m ∈ locLayer Ω l := le_centralizingLayer hM hm.mem
  have hl2 : l * l = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two hl.orderOf_eq_two
  have hm2 : m * m = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two hm.orderOf_eq_two
  have hlm : l * m = m * l := (Subgroup.mem_centralizer_singleton_iff.mp (hM.2 hm.mem)).symm
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω l)) with hπ
  set a : ↥(locLayer Ω l) := ⟨l, hlY⟩ with ha
  set b : ↥(locLayer Ω l) := ⟨m, hmY⟩ with hb
  have ha2 : a * a = 1 := Subtype.ext hl2
  have hb2 : b * b = 1 := Subtype.ext hm2
  have hab : a * b = b * a := Subtype.ext hlm
  obtain ⟨i, hi, hLbar⟩ := exists_kind_eq_sl23 hMFZ D hL hl
  obtain ⟨j, R', -, hMbar⟩ := D.fundamental _ (mem_locFamily_iff.mpr ⟨M, hM, rfl⟩ :
    locImg Ω l M ∈ locFamily Ω l)
  have hπM : ∀ y ∈ locImg Ω l M, y ∈ (D.hom j).range := fun y hy => by
    rw [hMbar] at hy
    obtain ⟨r, -, hr⟩ := hy
    exact ⟨r, hr⟩
  by_cases hji : j = i
  · exfalso
    subst hji
    have hcard : Nat.card (D.hom j).range = 24 := by
      rw [← hLbar]
      exact D.card_eq _ (mem_locFamily_iff.mpr ⟨L, hL, rfl⟩)
    have hπa : π a ∈ (D.hom j).range := by
      rw [← hLbar]
      exact ⟨a, Subgroup.mem_subgroupOf.mpr hl.mem, rfl⟩
    have hπb : π b ∈ (D.hom j).range :=
      hπM _ ⟨b, Subgroup.mem_subgroupOf.mpr hm.mem, rfl⟩
    have hπa1 : π a ≠ 1 := Q3W.mk_involution_ne_one3 Ω hl.orderOf_eq_two hlY
    have hπb1 : π b ≠ 1 := fun h => by
      have := Q3NT.eq_one_of_mem_oddCore_of_mul_self_eq_one ((QuotientGroup.eq_one_iff _).mp h) hb2
      exact hm.ne_one (congrArg Subtype.val this)
    have hπab : π a = π b :=
      Q3NT.eq_of_involutions_of_kind_eq_sl23 (D.kind j) hi (D.hom j) hcard hπa hπb
        (by rw [← map_mul, ha2, map_one]) (by rw [← map_mul, hb2, map_one]) hπa1 hπb1
    have hmem : a⁻¹ * b ∈ classicalInvolutionOddCore ↥(locLayer Ω l) := QuotientGroup.eq.mp hπab
    have h1 : a⁻¹ * b = 1 := Q3NT.eq_one_of_mem_oddCore_of_mul_self_eq_one hmem
      (Q3NT.inv_mul_mul_self_eq_one hab ha2 hb2)
    exact hne (congrArg Subtype.val (inv_mul_eq_one.mp h1))
  · intro x hx y hy
    rw [hLbar] at hx
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hπM y hy
    rw [← hx', ← hy']
    exact D.commute i j (Ne.symm hji) x' y'

theorem commutator_mem_oddCoreIn {Ω : Set (Subgroup G)} {l : G} {L M : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {l}) (hM : M ∈ centralizingMembers Ω {l})
    (h : Commutes (locImg Ω l L) (locImg Ω l M)) {a b : G} (ha : a ∈ L) (hb : b ∈ M) :
    ⁅b, a⁆ ∈ oddCoreIn (locLayer Ω l) := by
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω l)) with hπ
  set a' : ↥(locLayer Ω l) := ⟨a, le_centralizingLayer hL ha⟩ with ha'
  set b' : ↥(locLayer Ω l) := ⟨b, le_centralizingLayer hM hb⟩ with hb'
  have hcm : π a' * π b' = π b' * π a' :=
    h _ ⟨a', Subgroup.mem_subgroupOf.mpr ha, rfl⟩ _ ⟨b', Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hc : b' * a' * b'⁻¹ * a'⁻¹ ∈ classicalInvolutionOddCore ↥(locLayer Ω l) := by
    rw [← QuotientGroup.eq_one_iff]
    show π (b' * a' * b'⁻¹ * a'⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcm]
    group
  exact ⟨b' * a' * b'⁻¹ * a'⁻¹, hc, rfl⟩

theorem commutes_elt_of_centralizes_oddCore [Finite G] (hMFZ : RouteD.Gaps.FundNoncentral 3)
    {Ω : Set (Subgroup G)} (hIH : LocalLieSystems3 Ω) {L M : Subgroup G} {l m : G}
    (hlc : ¬ ({l} : Set G) ⊆ Subgroup.center G) (hLΩ : L ∈ Ω) (hMΩ : M ∈ Ω)
    (hl : IsClassicalMember3 L l) (hm : IsClassicalMember3 M m) (hne : l ≠ m)
    (hMl : M ≤ Subgroup.centralizer ({l} : Set G))
    (hBase : L ≤ Subgroup.centralizer (oddCoreIn (locLayer Ω l) : Set G)) {a : G} (ha : a ∈ L)
    (hcop : Nat.Coprime (orderOf a) (Nat.card (oddCoreIn (locLayer Ω l)))) {b : G} (hb : b ∈ M) :
    a * b = b * a := by
  obtain ⟨ι, hι, ⟨D⟩⟩ := hIH {l} hlc
  have hLmem : L ∈ centralizingMembers Ω {l} := ⟨hLΩ, isSubnormal_le hl.subnormal⟩
  have hMmem : M ∈ centralizingMembers Ω {l} := ⟨hMΩ, hMl⟩
  have himg := commutes_locImg_of_ne hMFZ D hLmem hMmem hl hm hne
  exact commutes_of_commutator_mem_of_centralizes (N := oddCoreIn (locLayer Ω l))
    (fun x hx => (Subgroup.mem_centralizer_iff.mp (hBase ha) x hx).symm)
    (commutator_mem_oddCoreIn hLmem hMmem himg ha hb) hcop

theorem le_centralizer_oddCoreIn_of_exact [Finite G] {Ω : Set (Subgroup G)} {L : Subgroup G}
    {l : G} (hLΩ : L ∈ Ω) (hl : IsClassicalMember3 L l)
    (hLex : classicalInvolutionOddCore ↥L = ⊥)
    (h3 : ¬ 3 ∣ Nat.card (classicalInvolutionOddCore ↥(locLayer Ω l))) :
    L ≤ Subgroup.centralizer (oddCoreIn (locLayer Ω l) : Set G) := by
  have hLmem : L ∈ centralizingMembers Ω {l} := ⟨hLΩ, isSubnormal_le hl.subnormal⟩
  set N : Subgroup G := oddCoreIn (locLayer Ω l) with hN
  have hodd : Odd (Nat.card N) := odd_card_oddCoreIn _
  have hcardN : Nat.card N = Nat.card (classicalInvolutionOddCore ↥(locLayer Ω l)) := by
    rw [hN, oddCoreIn, Subgroup.card_map_of_injective (locLayer Ω l).subtype_injective]
    rfl
  have h3' : ¬ 3 ∣ Nat.card N := by
    rw [hcardN]
    exact h3
  have h24 : Nat.card L = 24 := hl.natCard_eq_of_exact hLex
  have hLY : L ≤ locLayer Ω l := le_centralizingLayer hLmem
  have hYC : locLayer Ω l ≤ Subgroup.centralizer ({l} : Set G) :=
    centralizingLayer_le_centralizer Ω {l}
  have hHC : L ⊔ N ≤ Subgroup.centralizer ({l} : Set G) :=
    sup_le (isSubnormal_le hl.subnormal) ((oddCoreIn_le _).trans hYC)
  have hJ : IsSubnormal L (L ⊔ N) := by
    have := isSubnormal_inf hl.subnormal (L ⊔ N)
    rwa [inf_eq_left.mpr le_sup_left, inf_eq_right.mpr hHC] at this
  have hHN : L ⊔ N ≤ Subgroup.normalizer (N : Set G) :=
    sup_le (hLY.trans (normalizer_oddCoreIn _)) (Subgroup.le_normalizer)
  exact le_centralizer_of_exact_of_not_three_dvd hJ le_sup_right hHN hodd h3' hLex h24

theorem commutes_of_exact_threeFree [Finite G] [IsSimpleGroup G]
    (hMFZ : RouteD.Gaps.FundNoncentral 3) (hnab : ∃ a b : G, a * b ≠ b * a)
    {Ω : Set (Subgroup G)} (hIH : LocalLieSystems3 Ω) {L M : Subgroup G} {l m : G}
    (hLΩ : L ∈ Ω) (hMΩ : M ∈ Ω) (hl : IsClassicalMember3 L l) (hm : IsClassicalMember3 M m)
    (hne : l ≠ m) (hMl : M ≤ Subgroup.centralizer ({l} : Set G))
    (hLex : classicalInvolutionOddCore ↥L = ⊥)
    (h3 : ¬ 3 ∣ Nat.card (classicalInvolutionOddCore ↥(locLayer Ω l))) : Commutes L M := by
  have hnc : ¬ ({l} : Set G) ⊆ Subgroup.center G := not_subset_center_of_ne_one hnab hl.ne_one
  have hBase := le_centralizer_oddCoreIn_of_exact hLΩ hl hLex h3
  have hodd : Odd (Nat.card (oddCoreIn (locLayer Ω l))) := odd_card_oddCoreIn _
  have hcardN : Nat.card (oddCoreIn (locLayer Ω l)) =
      Nat.card (classicalInvolutionOddCore ↥(locLayer Ω l)) := by
    rw [oddCoreIn, Subgroup.card_map_of_injective (locLayer Ω l).subtype_injective]
    rfl
  have h3' : ¬ 3 ∣ Nat.card (oddCoreIn (locLayer Ω l)) := by
    rw [hcardN]
    exact h3
  have h24 : Nat.card L = 24 := hl.natCard_eq_of_exact hLex
  have hcop : Nat.Coprime 24 (Nat.card (oddCoreIn (locLayer Ω l))) := by
    have h2 : Nat.Coprime 2 (Nat.card (oddCoreIn (locLayer Ω l))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h =>
        (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    have h3c : Nat.Coprime 3 (Nat.card (oddCoreIn (locLayer Ω l))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3'
    have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left 3 h2) h3c
  intro a ha b hb
  have hord : orderOf a ∣ 24 := h24 ▸ Subgroup.orderOf_dvd_natCard L ha
  exact commutes_elt_of_centralizes_oddCore hMFZ hIH hnc hLΩ hMΩ hl hm hne hMl hBase ha
    (Nat.Coprime.coprime_dvd_left hord hcop) hb

end Local

end CFSG.ClassicalInvolution.Q3.Q3AL
