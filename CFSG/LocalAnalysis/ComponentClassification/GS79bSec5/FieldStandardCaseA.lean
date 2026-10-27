module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoSeven
import CFSG.LocalAnalysis.EvenBN.LinearThree.MainCaseA
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowElementary
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardColumnTransport

public section

open Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77 (Datum)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem normalizer_sup_zpowers_le_of_standard (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F) {A : Subgroup G} (d : Datum A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
      LinearFlag.proj 3 F) {Vi : Subgroup G}
    (hVi : Vi = (FieldFourCover.unipOne F).map (A.subtype.comp φ) ∨
      Vi = (FieldFourCover.unipTwo F).map (A.subtype.comp φ)) :
    normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G) := by
  have htC := CFSG.OddStandard.t_mem_centralizer d.sector
  have hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S := fun S => by
    have := d.sector.cyclic
    exact isCyclic_of_surjective (Sylow.equiv d.R S).toMonoidHom (Sylow.equiv d.R S).surjective
  have hrow := fun e' φ' hs' hp' =>
    exists_elementary_extension_of_standard_row hnonab hF A d.sector.standard hZ e' φ' hs' hp'
      hcyc d.t d.sector.t_order htC
  rcases hVi with rfl | rfl
  · exact (hrow e φ hφsurj hφproj).2.2.2.2.1
  · obtain ⟨e', φ', hsurj', hproj', hmap⟩ := exists_column_standard_cover e φ hφsurj hφproj
    have hE : (FieldFourCover.unipOne F).map (A.subtype.comp φ') =
        (FieldFourCover.unipTwo F).map (A.subtype.comp φ) := by
      rw [← Subgroup.map_map, hmap, Subgroup.map_map]
    have h := (hrow e' φ' hsurj' hproj').2.2.2.2.1
    rwa [hE] at h

theorem false_of_caseA_of_standard
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hF : 16 ≤ Nat.card F)
    {A : Subgroup G} (d : Datum A) (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
      LinearFlag.proj 3 F) {f : ℕ} (hq : Nat.card F = 2 ^ f)
    (hR : Radicals d.V ((FieldFourCover.unipOne F).map (A.subtype.comp φ))
      ((FieldFourCover.unipTwo F).map (A.subtype.comp φ)) (2 ^ f)) {Vi : Subgroup G}
    (hVi : Vi = (FieldFourCover.unipOne F).map (A.subtype.comp φ) ∨
      Vi = (FieldFourCover.unipTwo F).map (A.subtype.comp φ))
    (w : WData d Vi (2 ^ f)) {K : Type} [Field K] [Finite K] (D : LeviData A Vi K)
    (hK : Nat.card K = 2 ^ f) (hA : w.CaseA f D.lev.range) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 3 ≤ f := by
    by_contra h
    have h2 : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have htC := CFSG.OddStandard.t_mem_centralizer d.sector
  have hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S := fun S => by
    have := d.sector.cyclic
    exact isCyclic_of_surjective (Sylow.equiv d.R S).toMonoidHom (Sylow.equiv d.R S).surjective
  have hrow := fun e' φ' hs' hp' =>
    exists_elementary_extension_of_standard_row hnonab hF A d.sector.standard hZ e' φ' hs' hp'
      hcyc d.t d.sector.t_order htC
  have hN := normalizer_sup_zpowers_le_of_standard hnonab hF d hZ e φ hφsurj hφproj hVi
  have hsyl : ∀ Vj : Subgroup G, (Vj = (FieldFourCover.unipOne F).map (A.subtype.comp φ) ∨
      Vj = (FieldFourCover.unipTwo F).map (A.subtype.comp φ)) →
      CFSG.ABGLocalTools.IsSylowOf 2 (Vj ⊔ zpowers d.t)
        (centralizer ((Vj ⊔ zpowers d.t : Subgroup G) : Set G)) := by
    rintro Vj (rfl | rfl)
    · exact (hrow e φ hφsurj hφproj).2.2.1
    · exact isSylowOf_centralizer_column_of_standard hnonab hF A d.sector.standard hZ e φ hφsurj
        hφproj hcyc d.t d.sector.t_order htC
  have : Group.IsPerfect A := Group.IsPerfect.mk d.sector.standard.1.1
  have hFf : FusionFacts A (2 ^ f) := by
    have h := fusionFacts_of_odd_central_psl_three hF A hZ e hcyc
    rwa [hq] at h
  obtain ⟨F', _, _, _, hF', ⟨C⟩⟩ := Hyp.exists_caseAData hf d hR hVi hN w D hK hA
    (Hyp.commutator_oddCore_Ebar_of_caseA hf d hR hVi hN w D hK hA)
  exact C.false hnonab hf hFf hR hsyl hVi w.elem w.card w.comm_onto hF'

end CFSG.ComponentClassification.GS79bSec5
