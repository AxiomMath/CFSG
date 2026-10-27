module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthTail
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GTri

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem triGGHasLabel_congr {lab : LargeEvenLabel} {R R' : Type} [Group R] [Group R']
    (h : GGHasLabel lab R) (e : R ≃* R') : GGHasLabel lab R' :=
  CFSG.StandardType.largeEvenRawDatum_mono (fun _ _ _ _ hQ => ⟨e.symm.trans hQ.some⟩) h

theorem triPComp_eq_derived {X : Type} [Group X] [Finite X] {p : ℕ} {C J : Subgroup X}
    (hJ : GLAPComponent p C J) (hs : IsSimpleGroup ↥(⁅C, C⁆ : Subgroup X)) : J = ⁅C, C⁆ := by
  have hJC : (⁅C, C⁆ : Subgroup X) ≤ C := Subgroup.commutator_le_self C
  haveI : (⁅C, C⁆.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left C C)
  have hsolv : Group.IsSolvable (↥C ⧸ (⁅C, C⁆ : Subgroup X).subgroupOf C) := by
    haveI : Group.IsSolvable (↥C ⧸ commutator ↥C) := inferInstance
    let e := QuotientGroup.quotientMulEquivOfEq (CFSG.StandardType.ggCommutator_subgroupOf C)
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth.FOB.eq_of_component hJC hsolv hs hJ

noncomputable def triDerivedEquiv {X G : Type} [Group X] [Group G] {C : Subgroup X} (e : ↥C ≃* G) :
    ↥(⁅C, C⁆ : Subgroup X) ≃* ↥(commutator G) :=
  (ggCommutatorEquiv C).trans (ggCommutatorCongr e)

theorem triCommutator_eq_top {G : Type*} [Group G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have h1 : ⁅a, b⁆ ∈ commutator G := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · exact h

theorem triCanon_of_equiv (hRig : GGLabelRigidInput) {J : Type} [Group J] {labJ : GLALabel}
    (hlabJ : HasLabel J (fun l : GLALabel => l = labJ)) [IsSimpleGroup J] [Group.IsPerfect J]
    {R₀ : Type} [Group R₀] (eJ : J ≃* R₀) {lab' : GLALabel} (hlam' : LargeEvenInLambda2 lab')
    (hGH : GGHasLabel lab' R₀) : canonLabel labJ = canonLabel lab' := by
  obtain ⟨eQ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_quotCenter_equiv eJ
  have hGJ : GGHasLabel lab' (J ⧸ Subgroup.center J) := triGGHasLabel_congr hGH eQ.symm
  obtain ⟨hlamJ, -, hGlabJ⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlabJ
  exact Y10GInnLin.canonLabel_eq_of_ggLabelIso
    (hRig labJ lab' (J ⧸ Subgroup.center J) hlamJ hlam' hGlabJ hGJ)

theorem triComponent_equiv {X G : Type} [Group X] [Finite X] [Group G] {C J : Subgroup X} {p : ℕ}
    (e : ↥C ≃* G) (hs : IsSimpleGroup ↥(commutator G)) (hJ : GLAPComponent p C J) :
    Nonempty (↥J ≃* ↥(commutator G)) := by
  have e' := triDerivedEquiv e
  haveI := hs
  haveI : IsSimpleGroup ↥(⁅C, C⁆ : Subgroup X) := e'.isSimpleGroup
  have hJeq : J = ⁅C, C⁆ := triPComp_eq_derived hJ inferInstance
  exact ⟨(MulEquiv.subgroupCongr hJeq).trans e'⟩

theorem tri_nonabelian_of_center_bot {G : Type*} [Group G] [Nontrivial G]
    (hZ : Subgroup.center G = ⊥) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  haveI : IsMulCommutative G := ⟨⟨fun a b => hcomm a b⟩⟩
  have hc : Subgroup.center G = ⊤ := Subgroup.center_eq_top
  rw [hZ] at hc
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  have ha : a ∈ (⊥ : Subgroup G) := hc ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup G) := hc ▸ Subgroup.mem_top b
  exact hab ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hb).symm)

theorem triComponent_equiv_simple {X G : Type} [Group X] [Finite X] [Group G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {C J : Subgroup X} {p : ℕ} (e : ↥C ≃* G)
    (hJ : GLAPComponent p C J) : Nonempty (↥J ≃* G) := by
  have hcomm : commutator G = ⊤ := triCommutator_eq_top hna
  haveI : IsSimpleGroup ↥(commutator G) :=
    (MulEquiv.subgroupCongr hcomm).isSimpleGroup_congr.2 (Subgroup.topEquiv.isSimpleGroup_congr.2 inferInstance)
  obtain ⟨eJ₀⟩ := triComponent_equiv e inferInstance hJ
  exact ⟨(eJ₀.trans (MulEquiv.subgroupCongr hcomm)).trans Subgroup.topEquiv⟩

section G2


theorem tri_g2_simple {f : ℕ} (hf : 2 ≤ f) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ f) :
    IsSimpleGroup ↥(adjointGroup Tag.G2 F₀) ∧ ∃ a b : ↥(adjointGroup Tag.G2 F₀), a * b ≠ b * a := by
  have h3 : 3 ≤ Nat.card F₀ := by
    rw [hF₀]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hG : IsSimpleGroup ↥(adjointGroup Tag.G2 F₀) :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.isSimpleGroup_g2 h3
  haveI := hG.toNontrivial
  exact ⟨hG, tri_nonabelian_of_center_bot CFSG.LieType.Chevalley.center_adjointGroup_eq_bot⟩

theorem triCanon_G2 (hRig : GGLabelRigidInput) {X : Type} [Group X] [Finite X] {C J : Subgroup X}
    {labJ : GLALabel} {f : ℕ} (hf : 2 ≤ f) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ f) (e : ↥C ≃* ↥(adjointGroup Tag.G2 F₀)) (hJ : GLAPComponent 3 C J)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) : canonLabel labJ = ⟨.G2, 0, f⟩ := by
  obtain ⟨hG, hna⟩ := tri_g2_simple hf hF₀
  haveI := hG
  obtain ⟨eJ⟩ := triComponent_equiv_simple hna e hJ
  haveI : IsSimpleGroup ↥J := eJ.isSimpleGroup
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  have hlam : LargeEvenInLambda2 (⟨.G2, 0, f⟩ : GLALabel) := ⟨(by show 1 ≤ f; omega), rfl, hf⟩
  have hGH : GGHasLabel (⟨.G2, 0, f⟩ : GLALabel)
      (CFSG.StandardType.TableBExc.RecipeGroup Tag.G2 F₀) :=
    ⟨F₀, inferInstance, inferInstance, hF₀, ⟨MulEquiv.refl _⟩⟩
  have := triCanon_of_equiv hRig hlabJ (eJ.trans (CFSG.StandardType.TableBExc.recipeEquiv Tag.G2 F₀).symm)
    hlam hGH
  rw [this]
  rfl

end G2

section PGL

open CFSG.RankThree.PartTwo CFSG.PGLModel

theorem triCanon_PGL_true (hRig : GGLabelRigidInput) {X : Type} [Group X] [Finite X] {C J : Subgroup X}
    {labJ : GLALabel} {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] (hF : Sec4.PiField true 2 f F)
    (e : ↥C ≃* ↥(projImage (Sec4.glPi true 3 (2 ^ f) F))) (hJ : GLAPComponent 3 C J)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) : (canonLabel labJ).n = f := by
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
  obtain ⟨eJ₀⟩ := triComponent_equiv e hs hJ
  have eS : CFSG.Assembly.LowTwoRank.StatedProj (StatedSL 3 F) ≃*
      ↥(projImage (Sec4.slPi true 3 (2 ^ f) F)) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjEquivProjImage (StatedSL 3 F) rfl
  let eJ : ↥J ≃* CFSG.Assembly.LowTwoRank.StatedProj (StatedSL 3 F) := (eJ₀.trans eP).trans eS.symm
  haveI : IsSimpleGroup ↥J := (eJ₀.trans eP).isSimpleGroup
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  obtain ⟨eQ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_quotCenter_equiv eJ
  have h := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig ↥J labJ 3 f F (by norm_num)
    (by rw [hF.card]; rfl) hlabJ ⟨eQ⟩
  rw [h]

theorem triCanon_PGL_false (hRig : GGLabelRigidInput) {X : Type} [Group X] [Finite X] {C J : Subgroup X}
    {labJ : GLALabel} {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] (hF : Sec4.PiField false 2 f F)
    (e : ↥C ≃* ↥(projImage (Sec4.glPi false 3 (2 ^ f) F))) (hJ : GLAPComponent 3 C J)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) : (canonLabel labJ).n = f := by
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
  obtain ⟨eJ₀⟩ := triComponent_equiv e hs hJ
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
  have := triCanon_of_equiv hRig hlabJ eJ hlam hGH
  rw [this]
  rfl

end PGL

end CFSG.LocalAnalysis.GLTheoremA.Y10GTri
