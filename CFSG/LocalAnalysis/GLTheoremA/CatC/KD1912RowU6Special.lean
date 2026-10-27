module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowU6Nine
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.RankThree.PartOne.FOC.UnitarySplit
public import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Nine

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.Fischer
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm)
open CFSG.RankThree.PartOne.FOC
open CFSG.ClassicalGroups.UnitaryFlag
open Polynomial

private noncomputable def nineBlock (A : GL (Fin 6) F4) (a : F4[X]) :
    Subgroup ↥(gramSU hF4 (idGram F4 6)) :=
  (specialBlock (idForm hF4 6) (xOf A) a).comap (toLinSU hF4 6)

private theorem nineBlock_le_fix (A : primeFormUnitary hF4 (idGram F4 6)) (a : F4[X]) :
    nineBlock (A : GL (Fin 6) F4) a ≤
      fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A) := by
  intro g hg
  have hg' : toLinSU hF4 6 g ∈ specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a := hg
  exact (mem_fixSubgroup_primeFormConjSU_iff A rfl g).mpr
    (specialBlock_le_unitaryCentralizer hg').2

private theorem nineBlock_normal (A : primeFormUnitary hF4 (idGram F4 6)) (a : F4[X]) :
    (nineBlock (A : GL (Fin 6) F4) a).subgroupOf
      (fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A)) |>.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : toLinSU hF4 6 n.1 ∈ specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a := hn
  have hg' : toLinSU hF4 6 g.1 ∈
      unitaryCentralizer (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) :=
    toLinSU_mem_unitaryCentralizer A rfl g.2
  have h := conj_mem_specialBlock hg' hn'
  show toLinSU hF4 6 ((g * n * g⁻¹ : ↥(fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A))) :
    ↥(gramSU hF4 (idGram F4 6))) ∈
      specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a
  rw [show ((g * n * g⁻¹ : ↥(fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A))) :
      ↥(gramSU hF4 (idGram F4 6))) = g.1 * n.1 * g.1⁻¹ by simp [Subgroup.coe_mul, Subgroup.coe_inv],
    map_mul, map_mul, map_inv]
  exact h

private theorem exists_nineBlock_equiv_statedProjSL2
    (A : primeFormUnitary hF4 (idGram F4 6))
    (H : UnitaryPrimaryData hF4.bar (idForm hF4 6) (xOf (A : GL (Fin 6) F4)))
    (a : primaryFactors ((xOf (A : GL (Fin 6) F4)) : Module.End F4 (Fin 6 → F4)))
    (hgood : IsGoodBlock hF4 (xOf (A : GL (Fin 6) F4)) a)
    (hself : dualPoly hF4.bar (a : F4[X]) = a)
    (hmult : primaryMultiplicity ((xOf (A : GL (Fin 6) F4)) : Module.End F4 (Fin 6 → F4))
      (a : F4[X]) = 2)
    (hdeg : (a : F4[X]).natDegree = 3) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 8 ∧
      Nonempty (↥(nineBlock (A : GL (Fin 6) F4) (a : F4[X])) ≃*
        StatedProj (StatedSL 2 E)) := by
  have hq : 2 ≤ 2 ^ 1 := by norm_num
  haveI : Finite F4 := hF4.finite
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e2⟩⟩ :=
    nonempty_specialBlock_mulEquiv_sesqSU (hK := hF4) (B := idForm hF4 6)
      (x := xOf (A : GL (Fin 6) F4)) (a := a) hself (selfDualPrimaryBlock H a hself)
  obtain ⟨e3⟩ :=
    CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl
      (by exact hmult)
  haveI : Finite hE.fixedField := inferInstance
  letI : Fintype hE.fixedField := Fintype.ofFinite _
  have hcardF : Fintype.card hE.fixedField = 2 ^ (1 * (a : F4[X]).natDegree) := by
    rw [← Nat.card_eq_fintype_card]
    exact hE.card_fixedField
  have hF8 : Nat.card hE.fixedField = 8 := by
    rw [Nat.card_eq_fintype_card, hcardF, hdeg]
    norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP hE.fixedField 2 := charP_of_card_eq_prime_pow hcardF
  let eS := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 hE.fixedField
  let eP : StatedProj (StatedSL 2 hE.fixedField) ≃* StatedSL 2 hE.fixedField :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot).trans
      QuotientGroup.quotientBot
  have hSBle : specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) (a : F4[X]) ≤
      (toLinSU hF4 6).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a hgood hg)
  have hFmap : (nineBlock (A : GL (Fin 6) F4) (a : F4[X])).map (toLinSU hF4 6) =
      specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) (a : F4[X]) :=
    Subgroup.map_comap_eq_self hSBle
  let eK : ↥(nineBlock (A : GL (Fin 6) F4) (a : F4[X])) ≃*
      ↥(specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) (a : F4[X])) :=
    (Subgroup.equivMapOfInjective _ (toLinSU hF4 6) toLinSU_injective).trans
      (MulEquiv.subgroupCongr hFmap)
  exact ⟨hE.fixedField, inferInstance, inferInstance, hF8,
    ⟨((eK.trans e2).trans e3).trans (eS.trans eP.symm)⟩⟩

private theorem isSimpleGroup_nineBlock
    (A : primeFormUnitary hF4 (idGram F4 6))
    (H : UnitaryPrimaryData hF4.bar (idForm hF4 6) (xOf (A : GL (Fin 6) F4)))
    (a : primaryFactors ((xOf (A : GL (Fin 6) F4)) : Module.End F4 (Fin 6 → F4)))
    (hgood : IsGoodBlock hF4 (xOf (A : GL (Fin 6) F4)) a)
    (hself : dualPoly hF4.bar (a : F4[X]) = a)
    (hmult : primaryMultiplicity ((xOf (A : GL (Fin 6) F4)) : Module.End F4 (Fin 6 → F4))
      (a : F4[X]) = 2)
    (hdeg : (a : F4[X]).natDegree = 3) :
    IsSimpleGroup ↥(nineBlock (A : GL (Fin 6) F4) (a : F4[X])) := by
  obtain ⟨E, hField, hFinite, hcard, ⟨eKP⟩⟩ :=
    exists_nineBlock_equiv_statedProjSL2 A H a hgood hself hmult hdeg
  letI := hField
  letI := hFinite
  haveI : IsSimpleGroup (StatedProj (StatedSL 2 E)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 2) E le_rfl
      (Or.inr (by rw [hcard]; norm_num)) (Or.inr (by rw [hcard]; norm_num))
  exact eKP.isSimpleGroup

private theorem three_dvd_card_nineBlock
    (A : primeFormUnitary hF4 (idGram F4 6))
    (H : UnitaryPrimaryData hF4.bar (idForm hF4 6) (xOf (A : GL (Fin 6) F4)))
    (a : primaryFactors ((xOf (A : GL (Fin 6) F4)) : Module.End F4 (Fin 6 → F4)))
    (hgood : IsGoodBlock hF4 (xOf (A : GL (Fin 6) F4)) a)
    (hself : dualPoly hF4.bar (a : F4[X]) = a)
    (hmult : primaryMultiplicity ((xOf (A : GL (Fin 6) F4)) : Module.End F4 (Fin 6 → F4))
      (a : F4[X]) = 2)
    (hdeg : (a : F4[X]).natDegree = 3) :
    3 ∣ Nat.card ↥(nineBlock (A : GL (Fin 6) F4) (a : F4[X])) := by
  obtain ⟨E, hField, hFinite, hcard, ⟨eKP⟩⟩ :=
    exists_nineBlock_equiv_statedProjSL2 A H a hgood hself hmult hdeg
  letI := hField
  letI := hFinite
  have h504 : Nat.card ↥(nineBlock (A : GL (Fin 6) F4) (a : F4[X])) = 504 := by
    rw [Nat.card_congr eKP.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := E) (n := 2) (by norm_num),
      hcard, show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton]
    norm_num
  rw [h504]
  norm_num

private theorem pow_nine_mem_nineBlock
    (A : primeFormUnitary hF4 (idGram F4 6))
    (H : UnitaryPrimaryData hF4.bar (idForm hF4 6) (xOf (A : GL (Fin 6) F4)))
    (a : primaryFactors ((xOf (A : GL (Fin 6) F4)) : Module.End F4 (Fin 6 → F4)))
    (huniq : ∀ b : primaryFactors ((xOf (A : GL (Fin 6) F4)) : Module.End F4 (Fin 6 → F4)),
      (b : F4[X]) = (a : F4[X]))
    (hself : dualPoly hF4.bar (a : F4[X]) = a)
    (hdeg : (a : F4[X]).natDegree = 3)
    {g : ↥(gramSU hF4 (idGram F4 6))}
    (hg : g ∈ fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A)) :
    g ^ 9 ∈ nineBlock (A : GL (Fin 6) F4) (a : F4[X]) := by
  have hgU : toLinSU hF4 6 g ∈
      unitaryCentralizer (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) :=
    toLinSU_mem_unitaryCentralizer A rfl hg
  have horbit : orbitFactor (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) (a : F4[X]) =
      unitaryCentralizer (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) := by
    rw [orbitFactor_eq_supportedUnitary_of_selfDual hself]
    ext y
    constructor
    · intro h
      exact h.1
    · intro hy
      refine ⟨hy, fun b hb hbS v hv => ?_⟩
      exfalso
      exact hbS (by simpa using huniq ⟨b, hb⟩)
  have hgO : toLinSU hF4 6 g ∈
      orbitFactor (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) (a : F4[X]) := by
    rw [horbit]
    exact hgU
  have hmap9 : toLinSU hF4 6 (g ^ 9) = (toLinSU hF4 6 g) ^ 9 := map_pow _ g 9
  show toLinSU hF4 6 (g ^ 9) ∈
    specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) (a : F4[X])
  rw [hmap9]
  refine mem_specialBlock.mpr ⟨?_, ?_, ?_⟩
  · rw [horbit]
    exact pow_mem hgU 9
  · exact pow_mem hgU.2 9
  · have h9 := selfDual_det_pow (hK := hF4) (B := idForm hF4 6)
      (x := xOf (A : GL (Fin 6) F4)) (a := a) hself (selfDualPrimaryBlock H a hself) hgO
    have hpow : (2 ^ 1) ^ (a : F4[X]).natDegree + 1 = 9 := by
      rw [hdeg]; norm_num
    rw [hpow] at h9
    have hunit : (blockDetHom (xOf (A : GL (Fin 6) F4)) (a : F4[X])
        ⟨toLinSU hF4 6 g, hgU.2⟩ : (AdjoinRoot (a : F4[X]))ˣ) ^ 9 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h9
    have hcomp : (⟨(toLinSU hF4 6 g) ^ 9, pow_mem hgU.2 9⟩ :
        gl_centralizer (xOf (A : GL (Fin 6) F4))) =
        (⟨toLinSU hF4 6 g, hgU.2⟩ : gl_centralizer (xOf (A : GL (Fin 6) F4))) ^ 9 := rfl
    rw [hcomp, map_pow, hunit]

private theorem structure_nineBlock (A : primeFormUnitary hF4 (idGram F4 6)) {c : F4ˣ}
    (hc : c ≠ 1)
    (hA : (A : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    ∃ K : Subgroup ↥(gramSU hF4 (idGram F4 6)),
      K ≤ fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A) ∧
      (K.subgroupOf (fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A))).Normal ∧
      IsSimpleGroup ↥K ∧ 3 ∣ Nat.card ↥K ∧
      ∀ x ∈ fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A), x ^ 9 ∈ K := by
  obtain ⟨H, a, huniq, hself, hmult, hdeg⟩ := data_of_nine A hc hA
  have hgood : IsGoodBlock hF4 (xOf (A : GL (Fin 6) F4)) a :=
    ⟨by omega, fun _ => by simp [hmult, hdeg]⟩
  have huniq' : ∀ b : primaryFactors ((xOf (A : GL (Fin 6) F4)) : Module.End F4
      (Fin 6 → F4)), (b : F4[X]) = (a : F4[X]) := fun b =>
    congrArg Subtype.val (huniq b)
  refine ⟨nineBlock (A : GL (Fin 6) F4) (a : F4[X]), nineBlock_le_fix A (a : F4[X]),
    nineBlock_normal A (a : F4[X]), isSimpleGroup_nineBlock A H a hgood hself hmult hdeg,
    three_dvd_card_nineBlock A H a hgood hself hmult hdeg, ?_⟩
  intro x hx
  exact pow_nine_mem_nineBlock A H a huniq' hself hdeg hx

theorem u6TwoNineSpecial_holds : U6TwoNineSpecial := by
  intro B c hB hc1 hBc
  obtain ⟨K, hKle, hKn, hKsimple, h3K, hpow⟩ := structure_nineBlock ⟨B, hB⟩ hc1 hBc
  have hfix : (CenD B).map eGram6.toMonoidHom =
      fixSubgroup (primeFormConjSU hF4 (idGram F4 6) (⟨B, hB⟩ : primeFormUnitary hF4
        (idGram F4 6))) := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_CenD, mem_fixSubgroup]
    change (y : GL (Fin 6) F4) * B = B * y ↔
      (⟨B * (y : GL (Fin 6) F4) * B⁻¹, _⟩ : ↥(gramSU hF4 (idGram F4 6))) = y
    rw [Subtype.ext_iff]
    change _ ↔ B * (y : GL (Fin 6) F4) * B⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  let e : ↥(CenD B) ≃* ↥(fixSubgroup (primeFormConjSU hF4 (idGram F4 6) (⟨B, hB⟩ :
      primeFormUnitary hF4 (idGram F4 6)))) :=
    (Subgroup.equivMapOfInjective (CenD B) eGram6.toMonoidHom eGram6.injective).trans
      (MulEquiv.subgroupCongr hfix)
  let Kfix : Subgroup ↥(fixSubgroup (primeFormConjSU hF4 (idGram F4 6) (⟨B, hB⟩ :
      primeFormUnitary hF4 (idGram F4 6)))) :=
    K.subgroupOf (fixSubgroup (primeFormConjSU hF4 (idGram F4 6) (⟨B, hB⟩ :
      primeFormUnitary hF4 (idGram F4 6))))
  have hKfixn : Kfix.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKsimple
  let T : Subgroup ↥(CenD B) := Kfix.map e.symm.toMonoidHom
  have eT : ↥T ≃* ↥K :=
    ((Subgroup.equivMapOfInjective Kfix e.symm.toMonoidHom e.symm.injective).symm).trans
      (Subgroup.subgroupOfEquivOfLe hKle)
  refine ⟨T, hKfixn.map e.symm.toMonoidHom e.symm.surjective, eT.isSimpleGroup, ?_, ?_⟩
  · rw [Nat.card_congr eT.toEquiv]
    exact h3K
  · intro x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, map_pow]
    exact hpow (e x).1 (e x).2

theorem u6TwoNineCore_holds : U6TwoNineCore :=
  u6TwoNineCore_of_special u6TwoNineSpecial_holds

end CFSG.LocalAnalysis.GLTheoremA.KD1912
