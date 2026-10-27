module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatClass
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatHS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFSpor
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporHS

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem cat_of_sporadic
    (hcomp : ∀ s : TauCeti.SporadicName, s ≠ .J1 → s ≠ .J2 → s ≠ .J3 → s ≠ .M12 → s ≠ .HS →
      s ≠ .He → s ≠ .Suz → s ≠ .ONan → HarrisLit.SporCompData s)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    Nonempty (S ≃* NativeSporadic.He) ∨ NativeSporadic.IsSporadic S .Suz ∨
      NativeSporadic.IsSporadic S .ONan := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  cases s
  case J1 => exact (L34PF.false_of_J1 e htype).elim
  case J3 => exact (L34PF.false_of_J3 e htype).elim
  case M12 => exact (L34R.not_isL34Type_M12 e P htype).elim
  case J2 => exact (L34R.not_isL34Type_J2 e h htype).elim
  case HS => exact (false_of_hs_fixed e h htype).elim
  case He => exact Or.inl ⟨(e : S ≃* NativeSporadic.He)⟩
  case Suz => exact Or.inr (Or.inl ⟨e⟩)
  case ONan => exact Or.inr (Or.inr ⟨e⟩)
  all_goals exact (L34PF.not_isL34Type_of_sporCompData (hcomp _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hna e h htype).elim

theorem cat_of_simple
    (hcomp : ∀ s : TauCeti.SporadicName, s ≠ .J1 → s ≠ .J2 → s ≠ .J3 → s ≠ .M12 → s ≠ .HS →
      s ≠ .He → s ≠ .Suz → s ≠ .ONan → HarrisLit.SporCompData s)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    Nonempty (S ≃* NativeSporadic.He) ∨ NativeSporadic.IsSporadic S .Suz ∨
      NativeSporadic.IsSporadic S .ONan ∨ LieModel S .PSL 3 2 4 := by
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, ⟨θ⟩⟩ | ho | he | hsp
  · exact (not_isL34Type_of_properFixedComponent_alternating hn θ h htype).elim
  · exact (L34PF.not_isL34Type_of_oddLie_or_alt hna h htype (Or.inl ho)).elim
  · rcases he_or_L316_of_evenLie hna he h htype with hH | hL
    · exact Or.inl hH
    · exact Or.inr (Or.inr (Or.inr hL))
  · rcases cat_of_sporadic hcomp hna hsp h htype with hH | hS | hO
    · exact Or.inl hH
    · exact Or.inr (Or.inl hS)
    · exact Or.inr (Or.inr (Or.inl hO))

end CFSG.ComponentClassification.GrSLit.L34Sec5S
