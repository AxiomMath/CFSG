module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.AutInn
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Derived
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.InnEquiv
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.NormalClosure
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.SolomonRed

theorem harris311_of_cat (h : CatHarrisAS) : Harris311 := by
  intro G _ _ hK hO t ht ⟨e⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hnab : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
    exists_noncommute_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp))
  have hR := rhyp_mulAut hnab
  have hL : centralizerDerived t =
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.map
        (embA e) := by
    rw [centralizerDerived_eq_map e, commutator_mulAut_alt6]
  obtain ⟨hiso⟩ := nonempty_mulEquiv_range_conj hnab
  let ι : ↥((MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.map
      (embA e)) ≃* alternatingGroup (Fin 6) :=
    (Subgroup.equivMapOfInjective _ (embA e) (embA_injective e)).symm.trans hiso
  rcases lemmaR hR hO ht e with htc | ⟨hS, hswap | ⟨S, hF, hle⟩⟩
  ·
    have hN := map_embA_normal_of_central htc e hR.normal
    rw [hL, normalClosureOf_eq_of_normal hN]
    exact Or.inl ⟨ι⟩
  ·
    obtain ⟨S₁, S₂, hs⟩ := hswap
    rw [hL, normalClosureOf_eq_layer hS hs]
    obtain ⟨φ⟩ := swapData_layer_equiv hS hs
    let ψ : ↥S₁ ≃* alternatingGroup (Fin 6) := hs.iso.some.trans ι
    exact Or.inr (Or.inl ⟨φ.trans (MulEquiv.prodCongr ψ ψ)⟩)
  ·
    haveI := hF.simple
    have hBne : (MulAut.conj :
        alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.map (embA e) ≠ ⊥ := by
      intro hbot
      obtain ⟨a, ha, b, hb, hab⟩ := hS.nonab
      rw [hbot, Subgroup.mem_bot] at ha hb
      exact hab (by rw [ha, hb])
    rw [hL, normalClosureOf_eq_of_le_simple hF.normal hF.simple hle hBne]
    have hcat : Catalog ↥S :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK S (MonoidHom.id ↥S)
        Function.surjective_id
    obtain ⟨a, ha, b, hb, hab⟩ := hF.nonab
    rcases h G S hF.normal hF.simple ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h' => hab (congrArg Subtype.val h')⟩
      hcat hF.cent t ht ⟨e⟩ with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))

end CFSG.EvenSporadicStandard.HSStd.InvCent
