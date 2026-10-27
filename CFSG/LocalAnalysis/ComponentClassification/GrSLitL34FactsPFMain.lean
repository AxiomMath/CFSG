module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34ProperFixedSimple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFEven
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFON
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporHS

public section

namespace CFSG.ComponentClassification.GrSLit.L34PF

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem he_or_rank_of_sporadic
    (hONO : SolMax.ONOuterComponentsInput)
    (hcomp : ∀ s : TauCeti.SporadicName, s ≠ .J1 → s ≠ .J2 → s ≠ .J3 → s ≠ .M12 → s ≠ .HS →
      s ≠ .He → s ≠ .Suz → s ≠ .ONan → HarrisLit.SporCompData s)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    Nonempty (S ≃* NativeSporadic.He) ∨ pRank 2 ↥(Open.fusionZStar P) ≤ 1 := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  by_cases hr : pRank 2 ↥(Open.fusionZStar P) ≤ 1
  · exact Or.inr hr
  have hrank : 2 ≤ pRank 2 ↥(Open.fusionZStar P) := by omega
  have hZS : center S = ⊥ := center_eq_bot_of_simple hna
  have eS : S ⧸ center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZS).trans QuotientGroup.quotientBot
  have hZ1 : Nat.card (center S) ≤ 2 := by rw [hZS, Subgroup.card_bot]; omega
  cases s
  case J1 => exact (false_of_J1 e htype).elim
  case J3 => exact (false_of_J3 e htype).elim
  case M12 => exact (L34R.not_isL34Type_M12 e P htype).elim
  case J2 => exact (L34R.not_isL34Type_J2 e h htype).elim
  case HS => exact (L34R.false_of_hs hZ1 (eS.trans e) htype hrank).elim
  case He => exact Or.inl ⟨(e : S ≃* NativeSporadic.He)⟩
  case Suz => exact Or.inr (rank_le_one_of_suz hna e h htype)
  case ONan => exact Or.inr (rank_le_one_of_ON hONO hna e h htype)
  all_goals exact (not_isL34Type_of_sporCompData (hcomp _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) hna e h htype).elim

theorem l34ProperFixedSimpleRank_of_inputs
    (hONO : SolMax.ONOuterComponentsInput)
    (hcomp : ∀ s : TauCeti.SporadicName, s ≠ .J1 → s ≠ .J2 → s ≠ .J3 → s ≠ .M12 → s ≠ .HS →
      s ≠ .He → s ≠ .Suz → s ≠ .ONan → HarrisLit.SporCompData s) :
    L34ProperFixedSimpleRank := by
  intro S _ _ hS hna hcat σ hσ P hPF hP hPne htype
  have h : ProperFixedComponent σ P := ⟨hσ, hPF, hP, hPne⟩
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, ⟨θ⟩⟩ | ho | he | hsp
  · exact (not_isL34Type_of_properFixedComponent_alternating hn θ h htype).elim
  · exact (not_isL34Type_of_oddLie_or_alt hna h htype (Or.inl ho)).elim
  · exact he_or_rank_of_evenLie hna he h htype
  · exact he_or_rank_of_sporadic hONO hcomp hna hsp h htype

end CFSG.ComponentClassification.GrSLit.L34PF
