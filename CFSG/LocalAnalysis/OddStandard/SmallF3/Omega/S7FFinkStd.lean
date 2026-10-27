module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_isStandard_L (h36 : Asc82Lemma36) (hP34 : Asc82PocketExists) (h34c : Asc82Lemma34c)
    [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) (hLC : InCStar L) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup L := by
  have h2 : ComponentAtCentralInvolutions L :=
    componentAtCentralInvolutions_of_pocketed h36 hS hLC (Or.inl hS.inF) (Or.inl hS.inF)
  have h4 : ∀ g : G, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := fun g =>
    nonCommute_of_componentAt hP34 h34c hS hLC (Or.inl hS.inF) (Or.inl hS.inF) h2 g
  exact standard_of_componentAtCentralInvolutions hLC.1 h2 h4

theorem s7f_assemblyOddCore_eq_bot [Finite G] [IsSimpleGroup G] {t : G} (ht : orderOf t = 2) :
    CFSG.Assembly.oddCore G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Assembly.oddCore G) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card (CFSG.Assembly.oddCore G)) :=
      CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := G)
    rw [h, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem s7f_three_le_twoRank_L (hP : Asc82Tab6P) [Finite G] {L : Subgroup G} (hL : IsOm6P L) :
    3 ≤ CFSG.Open.twoRank (↥L ⧸ center ↥L) := by
  obtain ⟨P, hPL⟩ : ∃ P : Subgroup G, IsSylow2Of P L :=
    ⟨_, isSylow2Of_map_sylow (Classical.arbitrary (Sylow 2 ↥L))⟩
  obtain ⟨B, B₂, -, hB, -, -⟩ := hP.sylow_E16 G L hL P hPL
  have hBL : B ≤ L := hB.1.trans hPL.1
  have hc : center ↥L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp (hP.center_triv G L hL)
  have hinj : Function.Injective (QuotientGroup.mk' (center ↥L)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hc])
  have hE : CFSG.Open.IsElemAbelian 2
      ((B.subgroupOf L).map (QuotientGroup.mk' (center ↥L))) :=
    (hB.2.1.1.subgroupOf L).map _
  have hcard : Nat.card ((B.subgroupOf L).map (QuotientGroup.mk' (center ↥L))) = 2 ^ 4 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv).trans hB.2.1.2
  have h4 := CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary _ _ hE 4 hcard
  omega

theorem s7f_not_normal [IsSimpleGroup G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) : ¬ L.Normal := by
  intro hn
  haveI := hn
  obtain ⟨-, -, -, -, hcomm⟩ := hL
  have hne : L ≠ ⊥ := fun h => hcomm 1 (by rw [h, Subgroup.commutator_bot_left])
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
  · exact hne h
  · have htZ : t ∈ center G :=
      mem_center_iff.mpr fun g => mem_centralizer_iff.mp htC g (by rw [h]; exact mem_top g)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hZ | hZ
    · rw [hZ, mem_bot] at htZ
      rw [htZ, orderOf_one] at ht
      omega
    · apply hcomm 1
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [mem_centralizer_iff]
      intro b _
      exact mem_center_iff.mp (hZ ▸ mem_top a) b

theorem s7f_le_normalClosure [IsSimpleGroup G] (L : Subgroup G) {y : G} (hy : y ≠ 1) :
    L ≤ normalClosure ({y} : Set G) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure ({y} : Set G)) with h | h
  · exfalso
    have hmem : y ∈ normalClosure ({y} : Set G) := subset_normalClosure rfl
    rw [h, mem_bot] at hmem
    exact hy hmem
  · rw [h]
    exact le_top

end CFSG.OddStandard.SmallF3.Omega
