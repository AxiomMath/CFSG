module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3Dvd
public import CFSG.LocalAnalysis.AGL81I.Section3.SL3BorelOvergroups
public import CFSG.LocalAnalysis.AGL81I.Section3.GL3BorelNormalizer

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (ThreeTenTorusExclusion)
open scoped MatrixGroups

theorem dvd_card_sub_one_of_isPGroup_le_borelSL3 {p d : ℕ} [Fact p.Prime]
    {E : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))}
    (hE : E ≤ upperTriangular 3 (ZMod p)) (hEbot : E ≠ ⊥)
    (hEpg : IsPGroup d E) (hd : d.Prime) (hdp : d ≠ p) : d ∣ p - 1 := by
  let F : Subgroup (GL (Fin 3) (ZMod p)) :=
    E.map Matrix.SpecialLinearGroup.toGL
  have hFle : F ≤ borelGL3 (ZMod p) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_borelGL3]
    intro i j hij
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hE hx i j hij
  have hFne : F ≠ ⊥ := by
    intro hbot
    apply hEbot
    exact (Subgroup.map_eq_bot_iff_of_injective (f := Matrix.SpecialLinearGroup.toGL)
      E Matrix.SpecialLinearGroup.toGL_injective).mp hbot
  have hFpg : IsPGroup d F := hEpg.map Matrix.SpecialLinearGroup.toGL
  have h := dvd_card_sub_one_of_isPGroup_le_borel_of_ne_bot
    (K := ZMod p) (p := p) (d := d) hd hdp hFpg hFle hFne
  simpa [Nat.card_zmod] using h

theorem borel_case_impossible {H : Type} [Group H] [Finite H]
    {I D P Y B : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (htor : ThreeTenTorusExclusion p d)
    (hB : B = Y ⊓ I)
    (hBn : B = Subgroup.normalizer (P : Set H) ⊓ I) : False := by
  have hhyp' : ThreeTenHyp I D P Y p d := hhyp
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact d.Prime := ⟨hd⟩
  have hPI : P ≤ I := p_sylow_le_of_oPPrimeHull_eq hp hI hP
  have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  have hdvdI : d ∣ Nat.card ↥I :=
    dvd_card_of_threeTenHyp_of_isSLType hhyp' e htor
  have hEne : D ⊓ I ≠ ⊥ := inf_ne_bot_of_dvd_card hD hInormal hdvdI
  have hDY : D ≤ Y := d_le_Y_of_threeTenHyp hhyp'
  have hE_le_B : D ⊓ I ≤ B := by
    rw [hB]
    exact le_inf (inf_le_left.trans hDY) inf_le_right
  let E : Subgroup H := D ⊓ I
  let EI : Subgroup ↥I := E.subgroupOf I
  have hEIne : EI ≠ ⊥ := by
    intro hbot
    apply hEne
    have h : ((D ⊓ I).subgroupOf I).map I.subtype = ⊥ := by
      change EI.map I.subtype = ⊥
      rw [hbot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : D ⊓ I ≤ I)] at h
  have hBnsub : B.subgroupOf I = Subgroup.normalizer (P.subgroupOf I : Set ↥I) := by
    rw [hBn, Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_normalizer_eq hPI]
  have hEInorm : EI ≤ Subgroup.normalizer (P.subgroupOf I : Set ↥I) := by
    rw [← hBnsub]
    exact Subgroup.subgroupOf_mono I hE_le_B
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P I := hP.of_le hPI le_top
  obtain ⟨Q₀, hQ₀⟩ := hPsyl.exists_sylow_eq_subgroupOf
  let Q : Sylow p (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    Q₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQeq : (Q : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))) =
      (P.subgroupOf I).map e.toMonoidHom := by
    change (Q₀ : Subgroup ↥I).map e.toMonoidHom =
      (P.subgroupOf I).map e.toMonoidHom
    rw [hQ₀]
  obtain ⟨g, hg⟩ := exists_conj_borel_eq_normalizer Q
  have hEImapN : EI.map e.toMonoidHom ≤
      Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 3) (ZMod p))) := by
    calc EI.map e.toMonoidHom
        ≤ (Subgroup.normalizer (P.subgroupOf I : Set ↥I)).map e.toMonoidHom :=
          Subgroup.map_mono hEInorm
      _ = Subgroup.normalizer ((P.subgroupOf I).map e.toMonoidHom) :=
          Subgroup.map_equiv_normalizer_eq _ e
      _ = Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 3) (ZMod p))) := by
          exact congrArg (fun S : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) =>
            Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 3) (ZMod p))))
            hQeq.symm
  have hcancel : ((upperTriangular 3 (ZMod p)).map
      (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
      upperTriangular 3 (ZMod p) := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (SpecialLinearGroup (Fin 3) (ZMod p)) := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  let E' : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) := EI.map e.toMonoidHom
  let F : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    E'.map (MulAut.conj g⁻¹).toMonoidHom
  have hFle : F ≤ upperTriangular 3 (ZMod p) := by
    calc F = (EI.map e.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := rfl
      _ ≤ (Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 3) (ZMod p)))).map
            (MulAut.conj g⁻¹).toMonoidHom :=
          Subgroup.map_mono hEImapN
      _ = ((upperTriangular 3 (ZMod p)).map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj g⁻¹).toMonoidHom := by
          exact congrArg (fun S : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) =>
            S.map (MulAut.conj g⁻¹).toMonoidHom) hg
      _ = upperTriangular 3 (ZMod p) := hcancel
  have hFne : F ≠ ⊥ := by
    intro hbot
    change E'.map (MulAut.conj g⁻¹).toMonoidHom = ⊥ at hbot
    have hE'ne : E' ≠ ⊥ := by
      intro hbot'
      exact hEIne ((Subgroup.map_eq_bot_iff_of_injective
        (f := e.toMonoidHom) EI e.injective).mp hbot')
    exact hE'ne ((Subgroup.map_eq_bot_iff_of_injective
      (f := (MulAut.conj g⁻¹).toMonoidHom) E'
      (MulAut.conj g⁻¹).injective).mp hbot)
  have hFpg : IsPGroup d F := by
    have hEpg : IsPGroup d E := hD.isPGroup.to_le inf_le_left
    have hEIpg : IsPGroup d EI := hEpg.comap_subtype
    exact (hEIpg.map e.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
  have hdvd : d ∣ p - 1 :=
    dvd_card_sub_one_of_isPGroup_le_borelSL3 (p := p) (d := d) (E := F)
      hFle hFne hFpg hd hdp
  exact htor.1 hdvd

end CFSG.LocalAnalysis.AGL81I.Section3
