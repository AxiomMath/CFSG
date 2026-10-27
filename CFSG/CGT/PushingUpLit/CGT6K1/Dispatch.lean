module

public import CFSG.CGT.PushingUpLit.CGT6K1.Cases
public import CFSG.CGT.PushingUpLit.CGT6K1.Setting
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndTypes

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.Blueprint CFSG.CGT.PushingUpLit.CGT6

@[expose] def SimpleOutcome : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ) (A T₀ : Subgroup Q),
    AlmostSimple Q n A T₀ → SimpleOuterOutcome Q n T₀

section Assembly

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem caseOutcome'_of_ysl (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hOut : SimpleOutcome) (h : EndCfg4 G T Y) {f : ℕ} (hf : 2 ≤ f) (hY : YSL Y f) :
    CaseOutcome' G T Y := by
  obtain ⟨eL⟩ := h.nonempty_equiv_layerQ hf hY
  rcases hOut _ f _ _ (endCfg4_almostSimple hbridge h hf hY) with ⟨rfl, hv⟩ | ⟨hβ, hlist⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hY, smallList_of_gmsVList eL hv⟩)))
  · have hO : OuterT G T Y := endCfg4_outerT_of_inf_bot h hf hY hβ
    rcases hlist with h1 | h2 | h3 | ⟨rfl, hg⟩
    · exact Or.inr (Or.inl ⟨f, hf, hY, hO,
        stated_psl_congr eL (stated_psl_of_lieModel (by norm_num) h1)⟩)
    · exact Or.inl ⟨f, hf, hY, hO,
        Or.inr (stated_psu_congr eL (stated_psu_of_lieModel (by norm_num) h2))⟩
    · exact Or.inl ⟨f, hf, hY, hO,
        Or.inl (stated_psl_congr eL (stated_psl_of_lieModel (by norm_num) h3))⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hY, hO,
        chevalley_g2_congr eL (chevalley_g2_of_lieModel hg)⟩))

theorem endGMS'_of_inputs (hM4 : SchurMultL2Two)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (hOut : SimpleOutcome) : EndGMS' := by
  intro V _ _ hV G T Y h
  rcases h.types hM4 hV with ⟨f, hf, hY⟩ | hY5 | ⟨m, hm, hodd, hY⟩
  · exact caseOutcome'_of_ysl hbridge hOut h hf hY
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hY5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, hodd, hY⟩))))

end Assembly

end CFSG.CGT.PushingUpLit.CGT6K1
