module

public import CFSG.RankThree.PartOne.KP.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding.OutElemRank

open CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial

theorem isElementaryAbelian_of_open {Y : Type*} [Group Y] {p : ℕ} {E : Subgroup Y}
    (h : CFSG.Open.IsElemAbelian p E) : CFSG.IsElementaryAbelian p E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h

theorem card_le_of_elementaryRankAtMostOne {Y : Type*} [Group Y] {p : ℕ} {L E : Subgroup Y}
    [Group.IsPerfect L]
    (hrank : ElementaryRankAtMostOne p (MulAut (L ⧸ Subgroup.center L)))
    (hEN : E ≤ Subgroup.normalizer (L : Set Y)) (hE : CFSG.Open.IsElemAbelian p E)
    (hEC : E ⊓ Subgroup.centralizer (L : Set Y) = ⊥) : Nat.card E ≤ p := by
  have := isElementaryAbelian_of_open hE
  set α := (Finkelstein1977.automizer L).comp (Subgroup.inclusion hEN) with hα
  have hker : α.ker = ⊥ := by
    have h1 := CFSG.RankThree.GroupTheory.SteinbergBM.card_ker_automizer_comp_inclusion
      (L := L) (E := E) hEN
    rw [hEC, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).1 hker
  have hcard : Nat.card α.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hcard]
  exact hrank _ (isElementaryAbelian_range_of_hom α)

theorem isPerfect_of_quasisimple {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    Group.IsPerfect G :=
  ⟨h.1⟩

theorem exists_noncomm_of_quasisimple {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := h.2
  have : Group.IsPerfect G := isPerfect_of_quasisimple h
  have : IsMulCommutative (G ⧸ Subgroup.center G) := ⟨⟨fun a b => hcon a b⟩⟩
  have hsub : Subsingleton (G ⧸ Subgroup.center G) :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  exact not_subsingleton (G ⧸ Subgroup.center G) hsub

theorem not_dvd_card_quotient_center {G : Type*} [Group G] [Finite G] {p : ℕ}
    (h : ¬ p ∣ Nat.card G) : ¬ p ∣ Nat.card (G ⧸ Subgroup.center G) :=
  fun hd => h (hd.trans (Subgroup.card_quotient_dvd_card _))

end CFSG.AGLEmbedding.OutElemRank
