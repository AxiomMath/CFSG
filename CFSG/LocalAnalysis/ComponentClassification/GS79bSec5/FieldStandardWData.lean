module

import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowElementary
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardColumnTransport
public import CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal

public section

open Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77 (Datum)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem nonempty_WData_of_standard_row (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F) {A : Subgroup G} (d : Datum A) (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
      LinearFlag.proj 3 F) :
    Nonempty (WData d ((FieldFourCover.unipOne F).map (A.subtype.comp φ)) (Nat.card F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC := CFSG.OddStandard.t_mem_centralizer d.sector
  have hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S := fun S => by
    have := d.sector.cyclic
    exact isCyclic_of_surjective (Sylow.equiv d.R S).toMonoidHom (Sylow.equiv d.R S).surjective
  have H := exists_elementary_extension_of_standard_row hnonab hF A d.sector.standard hZ e φ
    hφsurj hφproj hcyc d.t d.sector.t_order htC
  dsimp only at H
  obtain ⟨-, -, -, -, -, O, -, -, -, -, -, -, -, Q, hQX, -, -, -, hQuniq, -, -, -, -, -, -, -,
    ⟨κQ, hκ, -, hκsurj⟩, S, -, -, -, -, -, W, hWQ, hWe, hWc, hEW, htW, hQW, hor, -, hNW,
    hfix, -, -, -, -, -, huniq⟩ := H
  refine ⟨{
    W := W
    elem := hWe
    card := hWc
    lt := hEW
    t_not_mem := htW
    t_norm := hNW (le_normalizer (mem_sup_right (mem_zpowers _)))
    fix := hfix
    comm_mem := ?_
    comm_onto := ?_
    normal := hNW
    levi_norm := ?_
    sup_le_inf_centralizer := ?_
    le_sup_of_isPGroup := ?_
    unique := fun W' hW' hc hcard => huniq W' (hQW ▸ hW') hc hcard }⟩
  · intro w hw
    have h1 := (κQ ⟨w, hWQ hw⟩).2
    rw [hκ] at h1
    simpa only [mul_assoc] using h1
  · intro v hv
    obtain ⟨x, hx⟩ := hκsurj ⟨v, hv⟩
    have hxv := hκ x
    rw [hx] at hxv
    rcases hor x x.2 with hxW | hxW
    · exact ⟨x, hxW, by rw [show (v : G) = _ from hxv]; simp only [mul_assoc]⟩
    · refine ⟨x * d.t, hxW, ?_⟩
      rw [show (v : G) = _ from hxv]
      group
  · rintro x ⟨hxA, hxE⟩
    apply hNW
    have hxt : x ∈ normalizer ((zpowers d.t : Subgroup G) : Set G) := by
      refine mem_normalizer_fintype fun n hn => ?_
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      have hc : Commute x d.t := mem_centralizer_iff.mp htC x hxA
      rw [(hc.zpow_right k).mul_inv_cancel]
      exact zpow_mem (mem_zpowers _) k
    exact mem_normalizer_fintype fun n hn =>
      conj_mem_sup_of_mem_inf_normalizer_of_mem_inf ⟨hxE, hxt⟩ n hn
  · rw [← hQW]
    exact hQX
  · intro P hP hPX
    obtain ⟨S', hS'⟩ :=
      (hP.comap_subtype : IsPGroup 2 (P.comap (normalizer
        (((FieldFourCover.unipOne F).map (A.subtype.comp φ) ⊔ zpowers d.t : Subgroup G) :
          Set G) ⊓ centralizer (((FieldFourCover.unipOne F).map (A.subtype.comp φ) :
            Subgroup G) : Set G)).subtype)).exists_le_sylow
    have hR := hQuniq _ ⟨S', rfl⟩
    rw [← hQW, ← hR]
    intro x hx
    exact ⟨⟨x, hPX hx⟩, hS' (mem_comap.mpr hx), rfl⟩

theorem nonempty_WData_of_standard_column (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F) {A : Subgroup G} (d : Datum A) (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
      LinearFlag.proj 3 F) :
    Nonempty (WData d ((FieldFourCover.unipTwo F).map (A.subtype.comp φ)) (Nat.card F)) := by
  obtain ⟨e', φ', hsurj', hproj', hmap⟩ := exists_column_standard_cover e φ hφsurj hφproj
  have hE : (FieldFourCover.unipOne F).map (A.subtype.comp φ') =
      (FieldFourCover.unipTwo F).map (A.subtype.comp φ) := by
    rw [← Subgroup.map_map, hmap, Subgroup.map_map]
  rw [← hE]
  exact nonempty_WData_of_standard_row hnonab hF d hZ e' φ' hsurj' hproj'

end CFSG.ComponentClassification.GS79bSec5
