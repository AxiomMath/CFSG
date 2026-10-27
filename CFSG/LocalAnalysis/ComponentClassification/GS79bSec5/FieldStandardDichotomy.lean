module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowSylowExtension
public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoSeven
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardCaseA
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardColumnTransport
import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27Main
import CFSG.GroupTheory.ElemAbelianClosure

public section

open Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {F : Type} [Field F] [Finite F]
  [CharP F 2]

private theorem not_isSylowOf_normalizer_of_standard_row
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hF : 16 ≤ Nat.card F) {A : Subgroup G} (d : Datum A)
    (hZ : Odd (Nat.card (center A))) (e : (A ⧸ center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (center A))).comp φ = LinearFlag.proj 3 F)
    {f : ℕ} (hq : Nat.card F = 2 ^ f) {Vi : Subgroup G}
    (hVi : Vi = (FieldFourCover.unipOne F).map (A.subtype.comp φ)) (w : WData d Vi (2 ^ f))
    (S : Subgroup G) (hS : IsSylowOf 2 S (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G))) :
    ¬ IsSylowOf 2 S (normalizer (w.W : Set G)) := by
  subst hVi
  have hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S := fun S => by
    have := d.sector.cyclic
    exact isCyclic_of_surjective (Sylow.equiv d.R S).toMonoidHom (Sylow.equiv d.R S).surjective
  have H := exists_proper_sylow_extension_of_standard_row hnonab hF A d.sector.standard hZ e φ
    hφsurj hφproj hcyc d.t d.sector.t_order (CFSG.OddStandard.t_mem_centralizer d.sector)
  dsimp only at H
  obtain ⟨-, -, -, -, -, _, -, -, -, -, -, -, -, Q, hQX, hQ2, -, -, -, -, -, -, -, -, -, -, -,
    _, -, -, -, -, -, W, ⟨hWQ, hWe, hWc, -, -, -, -, -, -, -, -, -, -, -, -, -⟩, hP⟩ := H
  have hWw : W = w.W := w.unique W (hWQ.trans (w.le_sup_of_isPGroup Q hQ2 hQX))
    (fun a ha b hb => hWe.comm ha hb) (by rw [hWc, hq])
  rw [← hWw]
  exact (hP S hS).2.2.2.2.2.1

theorem not_isSylowOf_normalizer_of_standard
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hF : 16 ≤ Nat.card F) {A : Subgroup G} (d : Datum A)
    (hZ : Odd (Nat.card (center A))) (e : (A ⧸ center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (center A))).comp φ = LinearFlag.proj 3 F)
    {f : ℕ} (hq : Nat.card F = 2 ^ f) {Vi : Subgroup G}
    (hVi : Vi = (FieldFourCover.unipOne F).map (A.subtype.comp φ) ∨
      Vi = (FieldFourCover.unipTwo F).map (A.subtype.comp φ))
    (w : WData d Vi (2 ^ f)) (S : Subgroup G)
    (hS : IsSylowOf 2 S (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G))) :
    ¬ IsSylowOf 2 S (normalizer (w.W : Set G)) := by
  rcases hVi with hVi | hVi
  · exact not_isSylowOf_normalizer_of_standard_row hnonab hF d hZ e φ hφsurj hφproj hq hVi w S hS
  · obtain ⟨e', φ', hsurj', hproj', hmap⟩ := exists_column_standard_cover e φ hφsurj hφproj
    have hE : (FieldFourCover.unipOne F).map (A.subtype.comp φ') =
        (FieldFourCover.unipTwo F).map (A.subtype.comp φ) := by
      rw [← Subgroup.map_map, hmap, Subgroup.map_map]
    exact not_isSylowOf_normalizer_of_standard_row hnonab hF d hZ e' φ' hsurj' hproj' hq
      (hVi.trans hE.symm) w S hS

theorem caseA_or_caseB_of_standard_of_cover
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F) {A : Subgroup G} (hZ : Odd (Nat.card (center A)))
    (e : (A ⧸ center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (center A))).comp φ = LinearFlag.proj 3 F)
    {f : ℕ} (hq : Nat.card F = 2 ^ f) (t : G) :
    ∀ d : Datum A, d.t = t → d.V = (FieldFourCover.unipAll F).map (A.subtype.comp φ) →
      Radicals d.V ((FieldFourCover.unipOne F).map (A.subtype.comp φ))
        ((FieldFourCover.unipTwo F).map (A.subtype.comp φ)) (2 ^ f) →
      ∀ {Vi : Subgroup G}, (Vi = (FieldFourCover.unipOne F).map (A.subtype.comp φ) ∨
        Vi = (FieldFourCover.unipTwo F).map (A.subtype.comp φ)) →
      ∀ (w : WData d Vi (2 ^ f)) (D : LeviData A Vi F),
        w.CaseA f D.lev.range ∨ w.CaseB D.lev.range := by
  intro d _ _ hR Vi hVi w D
  have hf4 : 4 ≤ f := by
    by_contra h
    have h2 : 2 ^ f ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hN := normalizer_sup_zpowers_le_of_standard hnonab hF d hZ e φ hφsurj hφproj hVi
  exact w.caseA_or_caseB_of_layerOutcome (by omega) hR hVi hN
    (not_isSylowOf_normalizer_of_standard hnonab hF d hZ e φ hφsurj hφproj hq hVi w) D hq
    (fun hlayer _ hmodel => Hyp.not_lieModel_PSL3 (by omega) d hR hVi hN w D hq hlayer hmodel)
    (fun hf3 => absurd hf3 (by omega))
    fun hO hstd hS2 => gmsLinearStandardLayerListKRankOne w.Ntil
      ((isKGroupCat_of_section_of_kProper hK (w.N_ne_top hnonab (by omega)) w.WN).quotient _) hO
      f _ hstd hS2

end CFSG.ComponentClassification.GS79bSec5
