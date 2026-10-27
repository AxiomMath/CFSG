module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoX
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.Sporadic.NativeFinite

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift

theorem three_le_pRank_of_e8Datum' {J X : Type} [Group J] [Finite J] [Group X] {φ : J →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center J) {a₁ a₂ a₃ n : X}
    (h : E8Datum a₁ a₂ a₃ n) : 3 ≤ CFSG.pRank 2 J := by
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, s₁, s₂, s₃, c₁₂, c₁₃, c₂₃⟩ := h.exists_lift hφ hker
  refine three_le_pRank_of_involutions (by rw [← sq]; exact s₁)
    (by rw [← sq]; exact s₂) (by rw [← sq]; exact s₃) c₁₂.eq c₁₃.eq c₂₃.eq ?_
  intro a b d hprod
  by_contra hne
  have himg := congrArg φ hprod
  simp only [map_mul, map_pow, map_one, hb₁, hb₂, hb₃] at himg
  refine h.prod_ne_one a b d ?_ himg
  intro h0
  exact hne ⟨congrArg Prod.fst h0, congrArg (fun x => x.2.1) h0, congrArg (fun x => x.2.2) h0⟩

theorem three_le_pRank_hs_cover {J : Type} [Group J] [Finite J]
    (e : J ⧸ center J ≃* Carrier .HS) : 3 ≤ CFSG.pRank 2 J := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := DoubleCoverRanks.hs_e8Datum
  refine three_le_pRank_of_e8Datum' (φ := e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ h
  intro x hx
  have h1 : e (QuotientGroup.mk' (center J) x) = 1 := hx
  rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem three_le_pRank_ru_cover {J : Type} [Group J] [Finite J]
    (e : J ⧸ center J ≃* Carrier .Ru) : 3 ≤ CFSG.pRank 2 J := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := DoubleCoverRanks.ru_e8Datum
  refine three_le_pRank_of_e8Datum' (φ := e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ h
  intro x hx
  have h1 : e (QuotientGroup.mk' (center J) x) = 1 := hx
  rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end CFSG.EvenSporadicStandard.Induction
