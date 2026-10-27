module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardFusionModel
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardFusionPinning
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardFusionRadicals
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Fusion
public import CFSG.Monster.B.Recog.GenericZStar

public section

open Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_seitz_fusion_configuration_of_standard
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F)
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (Subgroup.zpowers t)
        (Subgroup.centralizer (A : Set G)) ∧
      ∃ g : G,
        g⁻¹ * t * g =
          t * (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 1 0) : G) ∧
        (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 1 0) : G) ∈
          A.map (MulAut.conj g⁻¹).toMonoidHom ∧
        (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 0 1) : G) ∈
          A.map (MulAut.conj g⁻¹).toMonoidHom := by
  classical
  have hq : 4 < Nat.card F := by omega
  have hAperfect : Group.IsPerfect A := Group.IsPerfect.mk hA.1.1
  let F0 := @fusionFacts_of_odd_central_psl_three G _ _ F _ _ _ hF A hAperfect hZ e hcyc
  obtain ⟨d, hdt, hzC, hvV⟩ :=
    exists_datum_pinned_to_standard_roots (G := G) (F := F) A hA hZ e φ hφproj hcyc t ht htC
  obtain ⟨V₁, V₂, hR⟩ :=
    exists_radicals_of_sl_three_cover (G := G) (F := F) A e φ hφsurj hφproj d.V d.V_isSylow
  let z : G := (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 1 0) : G)
  let v : G := (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 0 1) : G)
  have hzA : z ∈ A := (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 1 0)).2
  have hz2 : z * z = 1 := by
    have hy : (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 1 0) : A) *
        (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 1 0) : A) = 1 := by
      have h := congrArg φ (CFSG.ComponentClassification.RankTwoL3Even.unipU_mul_self
        (F := F) (a := 0) (b := 1) (c := 0))
      simpa [CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU_zero] using h
    simpa [z] using congrArg A.subtype hy
  obtain ⟨b, hbne, hbcomm⟩ :=
    CFSG.Monster.B.Recog.exists_conj_ne_commute (G := G) hnonab ht
  have hZstar : ∃ k : G, k⁻¹ * d.t * k ≠ d.t ∧
      k⁻¹ * d.t * k * d.t = d.t * (k⁻¹ * d.t * k) := by
    refine ⟨b⁻¹, ?_, ?_⟩
    · simpa [hdt] using hbne
    · simpa [hdt] using hbcomm
  have hα : d.Alpha :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.Facts.alpha F0 d hq hR hZstar
  have hsg : CFSG.OddStandard.sg A d.R = Subgroup.zpowers d.t :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.Facts.sg_eq_zpowers F0 d hq hR hα
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (Subgroup.zpowers t)
      (Subgroup.centralizer (A : Set G)) := by
    have h : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.OddStandard.sg A d.R)
        (Subgroup.centralizer (A : Set G)) := ⟨d.R, rfl⟩
    simpa [hsg, hdt] using h
  have hconj : IsConj d.t (z * d.t) :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.Facts.isConj_mul_t F0 d hq hR hα hzA hz2
  obtain ⟨a, ha⟩ := isConj_iff.mp hconj
  let g : G := a⁻¹
  have hgconj : g⁻¹ * d.t * g = z * d.t := by
    simpa [g] using ha
  have hfirst : g⁻¹ * t * g = t * z := by
    rw [← hdt]
    calc g⁻¹ * d.t * g = z * d.t := hgconj
      _ = d.t * z := d.comm_t_of_mem hzA
  have hg : g⁻¹ * d.t * g ∈ d.P ⊓ Subgroup.centralizer (d.P : Set G) := by
    rw [hgconj]
    exact ⟨d.P.mul_mem hzC.1 d.t_mem_center_P.1,
      Subgroup.mul_mem (Subgroup.centralizer (d.P : Set G)) hzC.2 d.t_mem_center_P.2⟩
  have hzV : z ∈ d.V := ⟨hzC.1, hzA⟩
  have hgzA : g * z * g⁻¹ ∈ A :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.Facts.conj_V_le_A F0 d hq hR hα hg hzV
  have hgvA : g * v * g⁻¹ ∈ A :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.Facts.conj_V_le_A F0 d hq hR hα hg hvV
  refine ⟨hSyl, g, hfirst, ?_, ?_⟩
  · change z ∈ A.map (MulAut.conj g⁻¹).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨g * z * g⁻¹, hgzA, by simp; group⟩
  · change v ∈ A.map (MulAut.conj g⁻¹).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨g * v * g⁻¹, hgvA, by simp; group⟩

end CFSG.ComponentClassification.GS79bSec5

end
