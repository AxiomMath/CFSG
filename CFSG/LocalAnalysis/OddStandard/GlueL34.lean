module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeCatalog
import CFSG.Adapters.LieModelSmallOrders
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.GlueL34

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Preamble

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem ne_top (hS : StandardSetting G L) : L ≠ ⊤ := by
  have := hS.simple
  have heven : Even (Nat.card (centralizer (L : Set G))) := hS.standard.2.1
  intro htop
  rw [htop, Subgroup.coe_top, Subgroup.centralizer_univ,
    ComponentClassification.StandardRecognition.center_eq_bot_of_isSimpleGroup hS.nonab,
    Subgroup.card_bot] at heven
  exact Nat.not_even_one heven

theorem ne_bot (hS : StandardSetting G L) : L ≠ ⊥ := by
  rintro rfl
  have hs : IsSimpleGroup (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) :=
    hS.standard.1.2
  exact not_nontrivial _ hs.toNontrivial

theorem not_normal (hS : StandardSetting G L) : ¬ L.Normal := by
  have := hS.simple
  intro hN
  have := hN
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal L).elim (ne_bot hS) (ne_top hS)

theorem oddCore_eq_bot (hS : StandardSetting G L) : standardComponentOddCore G = ⊥ := by
  have := hS.simple
  have heven : Even (Nat.card (centralizer (L : Set G))) := hS.standard.2.1
  refine sSup_eq_bot.2 fun N hN => ?_
  have := hN.1
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_right fun htop => ?_
  have hGodd : Odd (Nat.card G) := by
    rw [← Subgroup.card_top (G := G), ← htop]
    exact hN.2
  have hdvd := Subgroup.card_subgroup_dvd_card (centralizer (L : Set G))
  exact Nat.not_even_iff_odd.2 hGodd ((even_iff_two_dvd.1 heven).trans hdvd |> even_iff_two_dvd.2)

theorem normalClosure_eq_top (hS : StandardSetting G L) :
    Subgroup.normalClosure (L : Set G) = ⊤ := by
  have := hS.simple
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.normalClosure (L : Set G))).resolve_left fun hbot => ne_bot hS (le_bot_iff.1 ?_)
  rw [← hbot]
  exact Subgroup.le_normalClosure

theorem rankTwoHyp (hS : StandardSetting G L)
    (hrank : 2 ≤ Open.pRank 2 (centralizer (L : Set G))) :
    ComponentClassification.RankTwoStandard.RankTwoHyp G L :=
  ⟨hS.kProper, hS.standard, not_normal hS, hrank⟩

end Preamble

theorem isSporadic_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {s : TauCeti.SporadicName} (h : IsSporadic Y s) : IsSporadic X s :=
  Nonempty.map (e.trans ·) h

theorem card_quotient_center_dvd {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    Nat.card (L ⧸ center L) ∣ Nat.card G := by
  have h1 : Nat.card (L ⧸ center L) ∣ Nat.card L :=
    ⟨Nat.card (center L), Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)⟩
  exact h1.trans (Subgroup.card_subgroup_dvd_card L)

theorem statedClassicalModel_of_lieModel_psl34 {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 2) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 2 :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem card_eq_of_lieModel_psl34 {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Blueprint.LieModel.card_psl_three_four h

end CFSG.OddStandard.GlueL34
