module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeAutomizer
import CFSG.RankThree.PartTwo.Sec21.StronglyEmbedded
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GuestConj

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.LocalAnalysis.RankThreeTheoremC (TransitiveOnNonidentity)

theorem transitive_of_oddIndex_of_pair {G : Type} [Group G] [Finite G]
    (hK : KFactStrongThreeAutomizer) {P : Sylow 3 G} {M A H R : Subgroup G}
    (hpr : AGLPair 3 M H R) (hesc : D2Escape 3 P M A H R) (hstr : GLBStronglyEmbedded 3 M)
    (hodd : ¬ 2 ∣ (H ⊓ M).relIndex H) :
    IsElemAbelian 3 R ∧ Nat.card R = 9 ∧
      TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hRHM : R ≤ H ⊓ M := le_inf hpr.le_H hpr.le_M
  have hR9 : 9 ∣ Nat.card R := by
    obtain ⟨E, hER, -, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 h3 R
    rw [hesc.pRank_eq] at hEc
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← hEc]
    exact Subgroup.card_dvd_of_le hER
  have h3HM : 3 ∣ Nat.card (H ⊓ M : Subgroup G) :=
    (show (3 : ℕ) ∣ 9 by norm_num).trans (hR9.trans (Subgroup.card_dvd_of_le hRHM))
  set N₀ : Subgroup ↥H := (H ⊓ M).subgroupOf H with hN₀
  have hstr : GLBStronglyEmbedded 3 N₀ :=
    CFSG.RankThree.PartTwo.Sec21.glbStronglyEmbedded_subgroupOf_inf hstr hesc.not_le h3HM
  have hrk : Open.pRank 3 N₀ = 2 := by
    rw [hN₀, CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 h3 _ _ inf_le_left]
    apply le_antisymm
    · exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 inf_le_left).trans
        hesc.pRank_H.le
    · exact hesc.pRank_eq.symm.le.trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hRHM)
  obtain ⟨T, hT⟩ := hesc.isSylow
  set R' : Subgroup ↥H := R.subgroupOf H with hR'
  have hR'T : R' = (T : Subgroup ↥H) := by
    rw [hR', ← hT]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hR'N₀ : R' ≤ N₀ := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hRHM (Subgroup.mem_subgroupOf.mp hx))
  have hR'p : IsPGroup 3 R' := hR'T ▸ T.isPGroup'
  have hR'syl : ¬ 3 ∣ R'.relIndex N₀ := by
    intro hd
    apply T.not_dvd_index
    rw [← hR'T, ← Subgroup.relIndex_mul_index hR'N₀]
    exact hd.mul_right _
  have hidx : ¬ 2 ∣ N₀.index := hodd
  obtain ⟨hel, hc9, htr⟩ := (hK ↥H hpr.isKGroup.2 N₀ hstr hrk R' hR'N₀ hR'p hR'syl).2 hidx
  have hRmap : R'.map H.subtype = R := Subgroup.map_subgroupOf_eq_of_le hpr.le_H
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_⟩
  ·
    have hc := hel.1.is_comm.comm (⟨⟨a, hpr.le_H a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩ : R')
      ⟨⟨b, hpr.le_H b.2⟩, Subgroup.mem_subgroupOf.mpr b.2⟩
    exact Subtype.ext (congrArg (fun z : R' => ((z : ↥H) : G)) hc)
  ·
    have he := hel.2 ⟨x, hpr.le_H hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    exact congrArg Subtype.val he
  · rw [← hRmap, Subgroup.card_map_of_injective H.subtype_injective]
    exact hc9
  ·
    intro x hx y hy hx1 hy1
    have hx' : (⟨x, hpr.le_H hx⟩ : ↥H) ∈ R' := Subgroup.mem_subgroupOf.mpr hx
    have hy' : (⟨y, hpr.le_H hy⟩ : ↥H) ∈ R' := Subgroup.mem_subgroupOf.mpr hy
    obtain ⟨n, ⟨hnN₀, hnR⟩, hnxy⟩ := htr _ hx' _ hy' (fun h => hx1 (congrArg Subtype.val h))
      (fun h => hy1 (congrArg Subtype.val h))
    refine ⟨(n : G), ⟨Subgroup.mem_subgroupOf.mp hnN₀, ?_⟩, congrArg Subtype.val hnxy⟩
    show (n : G) ∈ Subgroup.normalizer (R : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have hr' : (⟨r, hpr.le_H hr⟩ : ↥H) ∈ R' := Subgroup.mem_subgroupOf.mpr hr
      have := (Subgroup.mem_normalizer_iff.mp hnR _).mp hr'
      exact Subgroup.mem_subgroupOf.mp this
    · intro hr
      have hrH : r ∈ H := by
        have h1 : (n : G) * r * (n : G)⁻¹ ∈ H := hpr.le_H hr
        have e : r = (n : G)⁻¹ * ((n : G) * r * (n : G)⁻¹) * (n : G) := by group
        rw [e]
        exact H.mul_mem (H.mul_mem (H.inv_mem n.2) h1) n.2
      have hr' : (n * ⟨r, hrH⟩ * n⁻¹ : ↥H) ∈ R' := Subgroup.mem_subgroupOf.mpr hr
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hnR _).mpr hr')

end CFSG.AGLEmbeddingD2.McLaughlin
