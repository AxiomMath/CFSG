module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

theorem am_card_subgroupOf {A : Type} [Group A] {X D : Subgroup A} (hDX : D ≤ X) :
    Nat.card (D.subgroupOf X) = Nat.card D :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv

theorem am_normalizer_le {A : Type} [Group A] {X Y : Subgroup A} (S : Subgroup X)
    (h : normalizer ((S.map X.subtype : Subgroup A) : Set A) ⊓ X ≤ Y) :
    normalizer (S : Set X) ≤ Y.subgroupOf X := by
  intro g hg
  have hS : (S.map X.subtype).subgroupOf X = S :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective S
  have hSX : S.map X.subtype ≤ X := Subgroup.map_subtype_le S
  have hg' : g ∈ (normalizer ((S.map X.subtype : Subgroup A) : Set A)).subgroupOf X := by
    rw [Subgroup.subgroupOf_normalizer_eq hSX, hS]
    exact hg
  show (g : A) ∈ Y
  exact h (Subgroup.mem_inf.mpr ⟨hg', g.2⟩)

theorem am_map_le {A : Type} [Group A] {X Q : Subgroup A} {S : Subgroup X}
    (hS : S ≤ Q.subgroupOf X) : S.map X.subtype ≤ Q := by
  refine (Subgroup.map_mono hS).trans ?_
  rw [Subgroup.subgroupOf_map_subtype]
  exact inf_le_left

theorem kfactRankThreeStructure_of_grp (h : K2Grp) : KFactRankThreeStructure := by
  intro A _ _ X Y Q hK hQX hQp hQidx hQrk hxex hYX hYne hQY hy1 hy2 _hy3
  obtain ⟨x, hxX, hxo, hxr⟩ := hxex
  have hsetup : K2Setup ↥X (Y.subgroupOf X) (Q.subgroupOf X) := by
    refine ⟨?_, ?_, hQidx, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mpr
        (CFSG.KCore.KGroupAllSimple.kGroupNonab hK)
    · exact hQp.comap_subtype
    · rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf 3 hQX]
      exact hQrk
    · refine ⟨⟨x, hxX⟩, ?_, ?_⟩
      · rw [Subgroup.orderOf_mk]
        exact hxo
      · have hc : centralizer ({(⟨x, hxX⟩ : ↥X)} : Set ↥X) =
            (centralizer ({x} : Set A) ⊓ X).subgroupOf X := by
          ext g
          simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
            Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          constructor
          · intro hg
            exact ⟨congrArg Subtype.val hg, g.2⟩
          · rintro ⟨hg, -⟩
            exact Subtype.ext hg
        rw [hc, CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf 3 inf_le_right]
        exact hxr
    · intro hYtop
      exact hYne (le_antisymm hYX (Subgroup.subgroupOf_eq_top.mp hYtop))
    · exact fun g hg => hQY hg
    · intro S' hS' hS'rk
      refine am_normalizer_le S' (hy1 _ (am_map_le hS') ?_)
      rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 3
        X.subtype_injective S']
      exact hS'rk
    · intro E' hE'Q hE'ab hE'card S' hS'E' hS'rk
      have hEcard : Nat.card (E'.map X.subtype) = 27 := by
        rw [Subgroup.card_map_of_injective X.subtype_injective]
        exact hE'card
      refine am_normalizer_le S' (hy2 _ (am_map_le hE'Q) (hE'ab.map _) hEcard _
        (Subgroup.map_mono hS'E') ?_)
      rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 3
        X.subtype_injective S']
      exact hS'rk
  obtain ⟨⟨N', hN'n, hN'i⟩, hW⟩ := h ↥X (Y.subgroupOf X) (Q.subgroupOf X) hsetup
  have hN : (N'.map X.subtype).subgroupOf X = N' :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective N'
  refine ⟨⟨N'.map X.subtype, Subgroup.map_subtype_le N', ?_, ?_⟩, ?_⟩
  · rw [hN]
    exact hN'n
  · rw [hN]
    exact hN'i
  · intro D hDX hDab hD9 W hWX hDW hWcop
    have hD' : D.subgroupOf X ≤ normalizer ((W.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hWX]
      exact fun g hg => hDW hg
    have hW' := hW (D.subgroupOf X) (hDab.subgroupOf X)
      (by rw [am_card_subgroupOf hDX]; exact hD9) (W.subgroupOf X) hD'
      (by rw [am_card_subgroupOf hWX]; exact hWcop)
    rw [rankThreePrimeCore_eq_map_primeComplementCore]
    calc W = (W.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hWX).symm
      _ ≤ _ := Subgroup.map_mono hW'

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
