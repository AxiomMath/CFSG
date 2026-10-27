module

import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
import CFSG.Models.PGLSimple
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Big

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

open Polynomial CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem irreducible_X_pow_three_sub_C {c : F4} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    Irreducible (X ^ 3 - C c : F4[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [natDegree_X_pow_sub_C]
    simp
  · intro y hy
    have h1 : y ^ 3 = c := by
      have := hy
      simp [IsRoot, sub_eq_zero] at this
      exact this
    have h2 : ∀ y : F4, y ^ 3 = 0 ∨ y ^ 3 = 1 := by decide
    rcases h2 y with h | h
    · rw [h] at h1
      subst h1
      exact absurd hc3 (by decide)
    · exact hc1 (h1.symm.trans h)

abbrev xOf (A : GL (Fin 6) F4) : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4) :=
  Matrix.GeneralLinearGroup.toLin A

theorem F4unit_cube (c : F4ˣ) : (c : F4) ^ 3 = 1 := by
  revert c
  decide

section Nine

variable {A : GL (Fin 6) F4} {c : F4ˣ} (hc : c ≠ 1)
  (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
include hA

theorem aeval_xOf : aeval ((xOf A : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
    Module.End F4 (Fin 6 → F4)) (X ^ 3 - C (c : F4) : F4[X]) = 0 := by
  have h1 : ((xOf A : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
      Module.End F4 (Fin 6 → F4)) = Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) F4) := rfl
  rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hA]
  ext v i
  by_cases hi : i = v <;> simp [hi]

include hc

theorem minpoly_xOf : minpoly F4 ((xOf A : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
    Module.End F4 (Fin 6 → F4)) = X ^ 3 - C (c : F4) := by
  have hc3 : (c : F4) ^ 3 = 1 := F4unit_cube c
  have hc1 : (c : F4) ≠ 1 := fun h => hc (Units.ext h)
  exact (minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_three_sub_C hc3 hc1)
    (aeval_xOf hA) (monic_X_pow_sub_C _ (by norm_num))).symm

theorem primaryFactors_xOf : primaryFactors ((xOf A : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
    Module.End F4 (Fin 6 → F4)) = {X ^ 3 - C (c : F4)} := by
  have hc3 : (c : F4) ^ 3 = 1 := F4unit_cube c
  have hc1 : (c : F4) ≠ 1 := fun h => hc (Units.ext h)
  have hirr := irreducible_X_pow_three_sub_C hc3 hc1
  have hmon : (X ^ 3 - C (c : F4) : F4[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨mem_primaryFactors.2 ⟨hirr, hmon, ?_⟩, fun b hb => ?_⟩
  · rw [minpoly_xOf hc hA]
  · obtain ⟨hbirr, hbmon, hbdvd⟩ := mem_primaryFactors.1 hb
    rw [minpoly_xOf hc hA] at hbdvd
    exact eq_of_monic_of_associated hbmon hmon (hbirr.associated_of_dvd hirr hbdvd)

end Nine

theorem data_of_nine (A : primeFormUnitary hF4 (idGram F4 6)) {c : F4ˣ} (hc : c ≠ 1)
    (hA : (A : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    ∃ H : UnitaryPrimaryData hF4.bar (idForm hF4 6) (xOf (A : GL (Fin 6) F4)),
    ∃ a : primaryFactors ((xOf (A : GL (Fin 6) F4) : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
      Module.End F4 (Fin 6 → F4)),
      (∀ b : primaryFactors ((xOf (A : GL (Fin 6) F4) : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
        Module.End F4 (Fin 6 → F4)), b = a) ∧
      dualPoly hF4.bar (a : F4[X]) = a ∧
      primaryMultiplicity ((xOf (A : GL (Fin 6) F4) : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
        Module.End F4 (Fin 6 → F4)) (a : F4[X]) = 2 ∧
      (a : F4[X]).natDegree = 3 := by
  have H := primaryData_toLin' hF4 A.2 Nat.prime_three (by norm_num) hA
  have hprim := primaryFactors_xOf hc hA
  have hmem : (X ^ 3 - C (c : F4) : F4[X]) ∈ primaryFactors ((xOf (A : GL (Fin 6) F4) :
      LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) : Module.End F4 (Fin 6 → F4)) := by
    rw [hprim]; exact Finset.mem_singleton_self _
  have huniq := (Finset.eq_singleton_iff_unique_mem.1 hprim).2
  refine ⟨H, ⟨_, hmem⟩, fun b => Subtype.ext (huniq b.1 b.2), ?_, ?_, natDegree_X_pow_sub_C⟩
  · exact huniq _ (dualPoly_mem_primaryFactors H hmem)
  · show primaryMultiplicity _ (X ^ 3 - C (c : F4)) = 2
    have hdim := finrank_eq_sum_degree_mul_multiplicity H.squarefree
    rw [Module.finrank_fin_fun,
      Finset.sum_coe_sort (primaryFactors ((xOf (A : GL (Fin 6) F4) :
        LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) : Module.End F4 (Fin 6 → F4)))
        (fun a => (a : F4[X]).natDegree * primaryMultiplicity ((xOf (A : GL (Fin 6) F4) :
          LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) : Module.End F4 (Fin 6 → F4)) a),
      hprim, Finset.sum_singleton, natDegree_X_pow_sub_C] at hdim
    omega

@[expose] def ppEight : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩

theorem isChevSimple_three_L2 (F : Type) [Field F] [Finite F] (hF8 : Nat.card F = 8) :
    IsChevSimple 3 (StatedProj (StatedSL 2 F)) := by
  haveI : Fact ppEight.p.Prime := ⟨ppEight.prime_p⟩
  have hv : (TauCeti.LieTypeIndex.A 1 ppEight).Valid := by
    simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, ppEight, TauCeti.PrimePower.card_def]
  have hamb : ambiguousChev 3 (TauCeti.CFSGIndex.lie ⟨.A 1 ppEight, hv⟩) :=
    Or.inr ⟨by norm_num [ppEight, TauCeti.PrimePower.card_def], rfl⟩
  have e : StatedProj (StatedSL 2 F) ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 ppEight, hv⟩).Group :=
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 3 (by norm_num)
      (by rw [hF8] <;> norm_num)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ppEight hv).symm
  exact Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.A 1 ppEight, hv⟩, hamb, ⟨e⟩⟩

theorem level_of_nine_gram (A : primeFormUnitary hF4 (idGram F4 6)) {c : F4ˣ} (hc : c ≠ 1)
    (hA : (A : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {J : Subgroup ↥(gramSU hF4 (idGram F4 6))}
    (hJ : GLAPComponent 3 (fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A)) J) :
    kLevel 3 (PSimple 3 J) ≤ 2 := by
  obtain ⟨H, a, huniq, hself, hmult, hdeg⟩ := data_of_nine A hc hA
  have hq : 2 ≤ 2 ^ 1 := by norm_num
  have hgood : IsGoodBlock hF4 (xOf (A : GL (Fin 6) F4)) a :=
    ⟨by omega, fun _ => by simp [hmult, hdeg]⟩
  let α := primeFormConjSU hF4 (idGram F4 6) A
  let K₀ : Subgroup ↥(gramSU hF4 (idGram F4 6)) :=
    (specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a).comap (toLinSU hF4 6)
  have hSBle : specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a ≤ (toLinSU hF4 6).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a hgood hg)
  have hFmap : K₀.map (toLinSU hF4 6) = specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a :=
    Subgroup.map_comap_eq_self hSBle
  have hK₀C : K₀ ≤ fixSubgroup α := fun g hg =>
    (mem_fixSubgroup_primeFormConjSU_iff A rfl g).mpr
      (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg)).2
  let eK : ↥K₀ ≃* ↥(specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a) :=
    (Subgroup.equivMapOfInjective K₀ (toLinSU hF4 6) toLinSU_injective).trans
      (MulEquiv.subgroupCongr hFmap)
  have hKq : CFSG.IsQuasisimple ↥K₀ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm
      ((specialBlockFacts_of_good H hq a hgood).quasisimple hgood.1)
  have hperf := glaPComponent_perfect hJ
  have hJC : J ≤ fixSubgroup α := hJ.1
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hperf
  have hJK₀ : J ≤ K₀ := by
    intro g hg
    rw [Subgroup.mem_comap, mem_specialBlock]
    have hgC : g ∈ fixSubgroup α := hJC hg
    refine ⟨⟨toLinSU_mem_unitaryCentralizer A rfl hgC, fun b hb hbS v hv => ?_⟩, ?_⟩
    · exact absurd (Or.inl (congrArg Subtype.val (huniq ⟨b, hb⟩))) hbS
    · refine ⟨(mem_fixSubgroup_primeFormConjSU_iff A rfl g).mp hgC, ?_⟩
      let φ : ↥(fixSubgroup α) →* gl_centralizer (xOf (A : GL (Fin 6) F4)) :=
        ((toLinSU hF4 6).comp (fixSubgroup α).subtype).codRestrict _ fun g =>
          (mem_fixSubgroup_primeFormConjSU_iff A rfl g.1).mp g.2
      let ψ : ↥J →* (AdjoinRoot (a : F4[X]))ˣ :=
        (blockDetHom (xOf (A : GL (Fin 6) F4)) (a : F4[X])).comp
          (φ.comp (Subgroup.inclusion hJC))
      exact perfect_hom_trivial ψ ⟨g, hg⟩
  have hsub : CFSG.Open.IsSubnormal J K₀ := by
    have h := hJ.2.1.inf_of_le hK₀C
    rwa [inf_eq_left.2 hJK₀] at h
  have hJeq : J = K₀ := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hKq
      hsub.subgroupOf with h | h
    · exact le_antisymm hJK₀ (Subgroup.subgroupOf_eq_top.1 h)
    · exfalso
      have hcomm : ∀ x y : ↥J, x * y = y * x := by
        intro x y
        have := Subgroup.mem_center_iff.1
          (h (show (⟨x.1, hJK₀ x.2⟩ : ↥K₀) ∈ J.subgroupOf K₀ from x.2)) ⟨y.1, hJK₀ y.2⟩
        have h2 := congrArg (fun z : ↥K₀ => (z : ↥(gramSU hF4 (idGram F4 6)))) this.symm
        exact Subtype.ext h2
      haveI : IsMulCommutative ↥J := ⟨⟨hcomm⟩⟩
      haveI : Subsingleton ↥J := Group.IsPerfect.subsingleton_of_isMulCommutative
      exact glaPComponent_ne_bot' hJ (Subgroup.eq_bot_iff_forall _ |>.2 fun x hx =>
        congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥J) 1))
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e2⟩⟩ :=
    nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
  obtain ⟨e3⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl
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
  let eKP : ↥K₀ ≃* StatedProj (StatedSL 2 hE.fixedField) :=
    ((eK.trans e2).trans e3).trans (eS.trans eP.symm)
  haveI hsimpP : IsSimpleGroup (StatedProj (StatedSL 2 hE.fixedField)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 2) _ le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  haveI : IsSimpleGroup ↥K₀ := eKP.isSimpleGroup
  have hJ' : GLAPComponent 3 (fixSubgroup α) K₀ := hJeq ▸ hJ
  obtain ⟨ePS⟩ := nonempty_pSimple_equiv_of_simple hJ'
  rw [hJeq, kLevel_congr 3 ePS, kLevel_congr 3 eKP]
  exact kLevel_le_two_of_chev (isChevSimple_three_L2 hE.fixedField hF8)

theorem level_of_nine (B : primeFormUnitary hF4 (idGram F4 6)) {c : F4ˣ} (hc : c ≠ 1)
    (hB : (B : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {J : Subgroup M6} (hJ : GLAPComponent 3 (CenD (B : GL (Fin 6) F4)) J) :
    kLevel 3 (PSimple 3 J) ≤ 2 := by
  have hmap := glaPComponent_map_mulEquiv Nat.prime_three eGram6 hJ
  have hfix : (CenD (B : GL (Fin 6) F4)).map eGram6.toMonoidHom =
      fixSubgroup (primeFormConjSU hF4 (idGram F4 6) B) := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_CenD, mem_fixSubgroup]
    change (y : GL (Fin 6) F4) * B = B * y ↔
      (⟨(B : GL (Fin 6) F4) * y * (B : GL (Fin 6) F4)⁻¹, _⟩ : ↥(gramSU hF4 (idGram F4 6))) = y
    rw [Subtype.ext_iff]
    change _ ↔ (B : GL (Fin 6) F4) * y * (B : GL (Fin 6) F4)⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hfix] at hmap
  have h := level_of_nine_gram B hc hB hmap
  obtain ⟨e⟩ := pSimple_map_equiv 3 eGram6 J
  rw [← kLevel_congr 3 e]
  exact h

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
