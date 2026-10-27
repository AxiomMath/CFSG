module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriLab
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate8117
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate18000

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo CFSG.PGLModel

set_option linter.unusedSectionVars false


theorem triCanon_PGL_true_label (hRig : GGLabelRigidInput) {X : Type} [Group X] [Finite X]
    {C J : Subgroup X} {labJ : GLALabel} {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F]
    (hF : Sec4.PiField true 2 f F) (e : ↥C ≃* ↥(projImage (Sec4.glPi true 3 (2 ^ f) F)))
    (hJ : GLAPComponent 3 C J) (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) :
    canonLabel labJ = ⟨.A, 2, f⟩ := by
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI := hF.finite
  set G := projImage (Sec4.glPi true 3 (2 ^ f) F) with hG
  have hcomm := Sec13.commutator_projImage_glPi hF hq2
  have hSP : projImage (Sec4.slPi true 3 (2 ^ f) F) ≤ G :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun h => absurd h (by decide)))
  haveI hPs : IsSimpleGroup ↥(projImage (Sec4.slPi true 3 (2 ^ f) F)) :=
    Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hF hq2
  have eP : ↥(commutator ↥G) ≃* ↥(projImage (Sec4.slPi true 3 (2 ^ f) F)) :=
    (MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hSP)
  haveI hs : IsSimpleGroup ↥(commutator ↥G) := eP.isSimpleGroup
  obtain ⟨eJ₀⟩ := Y10GTri.triComponent_equiv e hs hJ
  have eS : CFSG.Assembly.LowTwoRank.StatedProj (StatedSL 3 F) ≃*
      ↥(projImage (Sec4.slPi true 3 (2 ^ f) F)) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjEquivProjImage (StatedSL 3 F) rfl
  let eJ : ↥J ≃* CFSG.Assembly.LowTwoRank.StatedProj (StatedSL 3 F) := (eJ₀.trans eP).trans eS.symm
  haveI : IsSimpleGroup ↥J := (eJ₀.trans eP).isSimpleGroup
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  obtain ⟨eQ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_quotCenter_equiv eJ
  have h := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig ↥J labJ 3 f F
    (by norm_num) (by rw [hF.card]; rfl) hlabJ ⟨eQ⟩
  simpa using h

theorem triCanon_PGL_false_label (hRig : GGLabelRigidInput) {X : Type} [Group X] [Finite X]
    {C J : Subgroup X} {labJ : GLALabel} {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F]
    (hF : Sec4.PiField false 2 f F) (e : ↥C ≃* ↥(projImage (Sec4.glPi false 3 (2 ^ f) F)))
    (hJ : GLAPComponent 3 C J) (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) :
    canonLabel labJ = ⟨.twA, 2, f⟩ := by
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI := hF.finite
  set G := projImage (Sec4.glPi false 3 (2 ^ f) F) with hG
  have hcomm := Sec13.commutator_projImage_glPi hF hq2
  have hSP : projImage (Sec4.slPi false 3 (2 ^ f) F) ≤ G :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hF.unitary))
  haveI hPs : IsSimpleGroup ↥(projImage (Sec4.slPi false 3 (2 ^ f) F)) :=
    Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hF hq2
  have eP : ↥(commutator ↥G) ≃* ↥(projImage (Sec4.slPi false 3 (2 ^ f) F)) :=
    (MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hSP)
  haveI hs : IsSimpleGroup ↥(commutator ↥G) := eP.isSimpleGroup
  obtain ⟨eJ₀⟩ := Y10GTri.triComponent_equiv e hs hJ
  have eS : CFSG.Assembly.LowTwoRank.StatedProj (StatedSU 3 (2 ^ f) F) ≃*
      ↥(projImage (Sec4.slPi false 3 (2 ^ f) F)) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjEquivProjImage (StatedSU 3 (2 ^ f) F) rfl
  let eJ : ↥J ≃* CFSG.Assembly.LowTwoRank.StatedProj (StatedSU 3 (2 ^ f) F) :=
    (eJ₀.trans eP).trans eS.symm
  haveI : IsSimpleGroup ↥J := (eJ₀.trans eP).isSimpleGroup
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  have hE : Nat.card F = (2 ^ f) ^ 2 := by rw [hF.card]; rfl
  have hlam : LargeEvenInLambda2 (⟨.twA, 2, f⟩ : GLALabel) :=
    Y10GInnUni.largeEvenInLambda2_twA (by omega) le_rfl (fun _ => hf)
  have hGH : GGHasLabel (⟨.twA, 2, f⟩ : GLALabel)
      (CFSG.Assembly.LowTwoRank.StatedProj (StatedSU 3 (2 ^ f) F)) :=
    Y10GInnUni.ggHasLabel_twA (b := 2) hE (MulEquiv.refl _)
  have h := Y10GTri.triCanon_of_equiv hRig hlabJ eJ hlam hGH
  rw [h]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.I167

end
