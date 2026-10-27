module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeSmallBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeSmallNorm
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeSmallData
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small

theorem isSmallTwoOrG2_quotient_center_top {Q : Type} [Group Q]
    (h : IsSmallTwoOrG2 (Q ⧸ Subgroup.center Q)) :
    IsSmallTwoOrG2 (↥(⊤ : Subgroup Q) ⧸ Subgroup.center ↥(⊤ : Subgroup Q)) := by
  obtain ⟨e⟩ := ParabCensus.nonempty_quotient_center_top (Q := Q)
  rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨d, hd, ⟨e.trans f⟩⟩

theorem kFactTwelveLeSmall_holds :
    KFactTwelveLeSmall := by
  intro A _ _ Y P β hY hO hsmall hpar hne hS _ hβ3 hβY _ hW
  have hsmall' : IsSmallTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) := hsmall
  have hcl : IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) := by
    rcases hsmall' with ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn, ⟨e⟩⟩)
    · exact Or.inr (Or.inr ⟨d, hd, ⟨e⟩⟩)
  have hpar0 := hpar
  obtain ⟨hPY, T, hT, hNT⟩ := hpar
  have hTP : T ≤ P := fun x hx => hNT ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
  have hCP : CompParab (⊤ : Subgroup ↥Y) (P.subgroupOf Y) := by
    rcases ParabCensus.parabolic_cases hY hO hcl hpar0 with hPeq | ⟨T₁, hT₁, hPN⟩ | hCP
    · exact absurd hPeq hne
    · exfalso
      apply hS
      have hT₁P : T₁ ≤ P := by
        rw [hPN]
        exact fun x hx => ⟨hT₁.1 hx, Subgroup.le_normalizer hx⟩
      have hPN' : P ≤ Subgroup.normalizer (T₁ : Set A) := by
        rw [hPN]
        exact inf_le_right
      exact isSylowTwoOf_pCoreOf_of_le_normalizer hT₁ hT₁P hPY hPN'
    · exact hCP
  have hodd : ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index := by
    have h0 := ParabCensus.not_two_dvd_index_wSup_small hCP
      (isSmallTwoOrG2_quotient_center_top hsmall')
    obtain ⟨eq⟩ :=
      ParabCensus.nonempty_quotient_pCore_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPY)
    rw [← ParabCensus.index_wSup_eq_of_mulEquiv eq]
    exact h0
  have hβT : ∀ t ∈ T, β * t * β⁻¹ ∈ T := conj_mem_sylow_of_wCent hT hTP hPY hodd hW
  have hβ3' : β ^ 3 = 1 := by simpa [hβ3] using pow_orderOf_eq_one β
  obtain ⟨⟨j, hj⟩, hcases⟩ := small_data hsmall'
  refine centralizes_of_normalizer_le hY hT hβ3' hβY hβT hj ?_
  have hTsyl : IsSylowTwoOf (T.subgroupOf Y) (⊤ : Subgroup ↥Y) :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT
  rcases hcases with h96 | ⟨⟨e⟩⟩
  · have hN : Subgroup.normalizer (T.subgroupOf Y : Set ↥Y) =
        (Subgroup.normalizer (T : Set A)).comap Y.subtype := by
      have h := Subgroup.comap_normalizer_eq_of_le_range (f := Y.subtype) (H := T)
        (by rw [Subgroup.range_subtype]; exact hT.1)
      rw [Subgroup.comap_subtype] at h
      exact h.symm
    refine normalizer_map_le_of_overgroup96 (P := P.subgroupOf Y)
      (ParabCensus.odd_card_center_of_pCoreOf_eq_bot hO) h96 hTsyl ?_ ?_ ?_ ?_
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hTP (Subgroup.mem_subgroupOf.mp hx))
    · intro htop
      exact hne (le_antisymm hPY (Subgroup.subgroupOf_eq_top.mp htop))
    · intro x hx
      rw [hN] at hx
      exact Subgroup.mem_subgroupOf.mpr (hNT ⟨x.2, hx⟩)
    · intro h
      apply hS
      have hPN : P ≤ Subgroup.normalizer (T : Set A) := by
        intro p hp
        have hmem : (⟨p, hPY hp⟩ : ↥Y) ∈ Subgroup.normalizer (T.subgroupOf Y : Set ↥Y) :=
          h (Subgroup.mem_subgroupOf.mpr hp)
        rw [hN] at hmem
        exact hmem
      exact isSylowTwoOf_pCoreOf_of_le_normalizer hT hTP hPY hPN
  · exact normalizer_map_le_of_equiv_slt (n := 4) (by norm_num) e hTsyl

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
