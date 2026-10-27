module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem le_of_isPerfect_of_index_le_two {H : Type} [Group H] [Finite H] {N L : Subgroup H}
    (hN : N.Normal) (hidx : N.index ≤ 2) (hL : Group.IsPerfect ↥L) : L ≤ N := by
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hQ : Nat.card (H ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
  rcases (show N.index = 1 ∨ N.index = 2 by omega) with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact le_top
  · have hcyc : IsCyclic (H ⧸ N) := isCyclic_of_prime_card (p := 2) (by rw [hQ, h2])
    let _ : IsMulCommutative (H ⧸ N) := IsCyclic.isMulCommutative
    let f : ↥L →* H ⧸ N := (QuotientGroup.mk' N).comp L.subtype
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    have : IsMulCommutative f.range := inferInstance
    have : Subsingleton f.range := inferInstance
    intro x hx
    have hfx : f ⟨x, hx⟩ = 1 := congrArg Subtype.val
      (Subsingleton.elim (f.rangeRestrict ⟨x, hx⟩) 1)
    exact (QuotientGroup.eq_one_iff (N := N) x).mp hfx

variable {H : Type} [Group H] [Finite H] {N L : Subgroup H}

theorem FStarSimple.not_mem_centralizer_of_orderOf_eq_two (hN : FStarSimple N) {t : H}
    (ht : orderOf t = 2) : t ∉ centralizer (N : Set H) := by
  intro htC
  have htN : t ∈ N := hN.centralizer_le htC
  have := hN.isSimpleGroup
  have hz : (⟨t, htN⟩ : ↥N) ∈ center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 htC g g.2)
  have hbot : center ↥N = ⊥ := by
    rcases (center ↥N).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hN.nonabelian
      have ha : a ∈ center ↥N := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  rw [hbot, Subgroup.mem_bot] at hz
  have : t = 1 := congrArg Subtype.val hz
  rw [this, orderOf_one] at ht
  omega

theorem not_oddCover_fi24Prime (hN : FStarSimple N) (hNs : IsSporadic ↥N .Fi24Prime)
    (hidx : N.index ≤ 2) (hstd : SolStd L) : ¬ OddCover .Fi24Prime L := by
  intro hcov
  have hLN : L ≤ N := le_of_isPerfect_of_index_le_two hN.normal hidx hcov.1.1
  obtain ⟨t, ht2, hcomp⟩ := hstd.2
  have hLt : L ≤ centralizer ({t} : Set H) := hcomp.le
  have hnot : ¬ N ≤ centralizer ({t} : Set H) := by
    intro hle
    refine hN.not_mem_centralizer_of_orderOf_eq_two ht2 (mem_centralizer_iff.2 fun g hg => ?_)
    exact mem_centralizer_singleton_iff.1 (hle hg)
  obtain ⟨n, hnN, hnt⟩ : ∃ n ∈ N, n ∉ centralizer ({t} : Set H) := by
    by_contra hcon
    exact hnot fun n hn => by_contra fun h => hcon ⟨n, hn, h⟩
  have hlt : L.subgroupOf N < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hnt (hLt ?_)
    have : (⟨n, hnN⟩ : ↥N) ∈ L.subgroupOf N := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨e⟩ := hNs
  obtain ⟨e'⟩ := hcov.2.2
  have hNc : Nat.card ↥N = Nat.card (Carrier .Fi24Prime) := Nat.card_congr e.toEquiv
  have hQc : Nat.card (↥L ⧸ center ↥L) = Nat.card (Carrier .Fi24Prime) :=
    Nat.card_congr e'.toEquiv
  have hQL : Nat.card (↥L ⧸ center ↥L) ≤ Nat.card ↥L :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have hLs : Nat.card (L.subgroupOf N) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv
  have hltc : Nat.card (L.subgroupOf N) < Nat.card ↥N := by
    have := Subgroup.card_lt_of_lt hlt
    simpa using this
  omega

@[expose] def Fi24NoStdFi22 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L : Subgroup H), FStarSimple N →
    IsSporadic ↥N .Fi24Prime → N.index ≤ 2 → SolStd L → ¬ OddCover .Fi22 L

theorem fiGiven_of (hmult : OddMultTrivial .Fi23) (h22 : Fi24NoStdFi22) : FiGiven := by
  intro H _ _ N L s hs hN hNs hidx _ hstd hcov
  have hs' : s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime := by simpa [fiTypes] using hs
  rcases hs' with rfl | rfl | rfl
  · exact absurd hcov (h22 H N L hN hNs hidx hstd)
  · exact ⟨hcov.isSporadic_of_mult hmult, hcov.center_eq_bot hmult⟩
  · exact absurd hcov (not_oddCover_fi24Prime hN hNs hidx hstd)

end CFSG.EvenSporadicStandard.Induction
