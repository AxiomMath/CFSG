module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardCaseA
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardDichotomy
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardProductExclusion
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowDatum
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardCoverFrame
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardNonSwap
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardWData
import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseACommon

public section

open Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77 (Datum)

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2] {A : Subgroup G}

private noncomputable def coverFrameOfCover (e : (A ⧸ center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (center A))).comp φ = LinearFlag.proj 3 F)
    {V : Subgroup G} (hV : (FieldFourCover.unipAll F).map (A.subtype.comp φ) = V) :
    CoverFrame A V F where
  ρ := A.subtype.comp φ
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  ker_le := ker_subtype_comp_le_center e φ hφproj
  map_unipAll := hV

variable [Finite G]

private theorem commutator_oddCore_Ebar_of_caseB_of_normalizer {f : ℕ} (hf : 3 ≤ f)
    (d : Datum A) {V₁ V₂ Vi : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f)) {K : Type} [Field K] [Finite K] (D : LeviData A Vi K)
    (hKc : Nat.card K = 2 ^ f) (hB : w.CaseB D.lev.range) :
    ⁅CFSG.Open.standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥ :=
  Hyp.commutator_oddCore_Ebar_of_conj hf d hR hW hN w D hKc fun _ hz _ hz2 =>
    hB.exists_conj hz hz2

variable [IsSimpleGroup G]


theorem false_of_standard_of_datum
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hF : 16 ≤ Nat.card F)
    (d : Datum A) (hZ : Odd (Nat.card (center A)))
    (e : (A ⧸ center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (center A))).comp φ = LinearFlag.proj 3 F)
    {f : ℕ} (hq : Nat.card F = 2 ^ f)
    (hV : d.V = (FieldFourCover.unipAll F).map (A.subtype.comp φ))
    (hR : Radicals d.V ((FieldFourCover.unipOne F).map (A.subtype.comp φ))
      ((FieldFourCover.unipTwo F).map (A.subtype.comp φ)) (2 ^ f)) :
    False := by
  have hf : 3 ≤ f := by
    by_contra h
    have h2 : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27 : ∀ {Vi : Subgroup G}, (Vi = (FieldFourCover.unipOne F).map (A.subtype.comp φ) ∨
      Vi = (FieldFourCover.unipTwo F).map (A.subtype.comp φ)) →
      ∀ (w : WData d Vi (2 ^ f)) (D : LeviData A Vi F),
        w.CaseA f D.lev.range ∨ w.CaseB D.lev.range := by
    intro Vi hVi w D
    exact caseA_or_caseB_of_standard_of_cover hK hnonab hF hZ e φ hφsurj hφproj hq d.t
      d rfl hV hR hVi w D
  let Fr := (coverFrameOfCover e φ hφsurj hφproj hV.symm).toFrameData
  obtain ⟨w₀⟩ : Nonempty (WData d ((FieldFourCover.unipOne F).map (A.subtype.comp φ)) (2 ^ f)) :=
    hq ▸ nonempty_WData_of_standard_row hnonab hF d hZ e φ hφsurj hφproj
  obtain ⟨w₁⟩ : Nonempty (WData d ((FieldFourCover.unipTwo F).map (A.subtype.comp φ)) (2 ^ f)) :=
    hq ▸ nonempty_WData_of_standard_column hnonab hF d hZ e φ hφsurj hφproj
  rcases h27 (Or.inl rfl) w₀ (Fr.leviData 0) with hA₀ | hB₀
  · exact false_of_caseA_of_standard hnonab hF d hZ e φ hφsurj hφproj hq hR (Or.inl rfl) w₀
      (Fr.leviData 0) hq hA₀
  rcases h27 (Or.inr rfl) w₁ (Fr.leviData 1) with hA₁ | hB₁
  · exact false_of_caseA_of_standard hnonab hF d hZ e φ hφsurj hφproj hq hR (Or.inr rfl) w₁
      (Fr.leviData 1) hq hA₁
  have hO₀ := commutator_oddCore_Ebar_of_caseB_of_normalizer hf d hR (Or.inl rfl)
    (normalizer_sup_zpowers_le_of_standard hnonab hF d hZ e φ hφsurj hφproj (Or.inl rfl)) w₀
    (Fr.leviData 0) hq hB₀
  have hO₁ := commutator_oddCore_Ebar_of_caseB_of_normalizer hf d hR (Or.inr rfl)
    (normalizer_sup_zpowers_le_of_standard hnonab hF d hZ e φ hφsurj hφproj (Or.inr rfl)) w₁
    (Fr.leviData 1) hq hB₁
  exact false_of_caseB_of_frameData Fr e hf hq w₀ w₁ hB₀ hB₁ hO₀ hO₁
    (fun P₁ P₂ _ _ h₁₂ hZ' he₁ he₂ ht₁ ht₂ =>
      false_of_nonswap_of_mulEquiv (d := d) e hf hq h₁₂ hZ' he₁ he₂ ht₁ ht₂)

theorem false_of_standard_of_cover
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hF : 16 ≤ Nat.card F)
    {f : ℕ} (hq : Nat.card F = 2 ^ f) (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A) (hZ : Odd (Nat.card (center A)))
    (e : (A ⧸ center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (center A))).comp φ = LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ centralizer (A : Set G)) :
    False := by
  obtain ⟨d, _, -, hdV, hR⟩ := exists_datum_with_standard_unipotent_radicals hnonab hF A hA hZ
    e φ hφsurj hφproj hcyc t ht htC
  rw [hq] at hR
  exact false_of_standard_of_datum hK hnonab hF d hZ e φ hφsurj hφproj hq hdV hR

end CFSG.ComponentClassification.GS79bSec5
