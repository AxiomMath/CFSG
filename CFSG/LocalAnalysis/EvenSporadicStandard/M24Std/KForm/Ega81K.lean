module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2A8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Reduction.Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Reduction.Product
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Reduction.Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Reduction.RHyp

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped MatrixGroups

@[expose] def Ega81HypAZ2A8KSharp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsKGroupCat X →
    ∀ (z : X) (H : Subgroup X), orderOf z = 2 → Nonempty (H ≃* alternatingGroup (Fin 8)) →
      centralizer ({z} : Set X) = H ⊔ zpowers z → z ∈ centralizer (H : Set X) →
      Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃*
        alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) ∨
      Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* PSL(4, GaloisField 2 2))

theorem ega81HypAZ2A8K_of_sharp (h : Ega81HypAZ2A8KSharp) : Ega81HypAZ2A8K := by
  intro X _ _ hK z H hz hH hC hzH
  rcases h X hK z H hz hH hC hzH with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))

section Assembly

set_option linter.unusedSectionVars false


theorem ega81HypAZ2A8KSharp_holds : Ega81HypAZ2A8KSharp := by
  intro X _ _ hK z H hz hH hC hzH
  obtain ⟨e⟩ := hH
  have hR := KForm.Reduction.rhyp_alt8
  obtain ⟨ζ⟩ := KForm.Reduction.centralizer_equiv_prod_of_eq hz e hR.center hC hzH
  have hB := KForm.Reduction.fusionOddCore_prod_eq_bot_of_rhyp hR
    KForm.Reduction.even_natCard_top_alt8
  obtain ⟨hO, hK', hz', ⟨ζ'⟩⟩ := KForm.Reduction.quotient_setting hK hz hB ζ
  rcases KForm.Reduction.layer_cases hR hO hz' ζ' with h1 | h2 | h3
  · obtain ⟨e1⟩ := h1
    exact Or.inl ⟨e1.trans Subgroup.topEquiv⟩
  · obtain ⟨e2⟩ := h2
    exact Or.inr (Or.inl ⟨e2.trans (MulEquiv.prodCongr Subgroup.topEquiv Subgroup.topEquiv)⟩)
  · obtain ⟨S, hSn, hSs, hSc, hSe⟩ := h3
    haveI := hSn
    haveI := hSs
    have hcat : Catalog ↥S :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK' S (MonoidHom.id ↥S)
        Function.surjective_id
    obtain ⟨f⟩ := catZ2A8_holds (X ⧸ fusionOddCore X) S hSn hSs hcat hSc
      (QuotientGroup.mk' (fusionOddCore X) z) hz' ⟨ζ'⟩
    exact Or.inr (Or.inr ⟨(MulEquiv.subgroupCongr hSe).trans f⟩)

theorem ega81HypAZ2A8K_holds : Ega81HypAZ2A8K :=
  ega81HypAZ2A8K_of_sharp ega81HypAZ2A8KSharp_holds

end Assembly

end CFSG.EvenSporadicStandard.M24Std
