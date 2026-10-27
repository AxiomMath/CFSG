module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Nine
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTGen
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open Polynomial CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

theorem catalogIs_L2eight_of_sl2 (F : Type) [Field F] [Finite F] (hF8 : Nat.card F = 8) :
    catalogIs (StatedProj (StatedSL 2 F)) S10.isL2eight := by
  haveI : Fact ppEight.p.Prime := ⟨ppEight.prime_p⟩
  have hv : (TauCeti.LieTypeIndex.A 1 ppEight).Valid := by
    simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, ppEight, TauCeti.PrimePower.card_def]
  have e : StatedProj (StatedSL 2 F) ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 ppEight, hv⟩).Group :=
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 3 (by norm_num)
      (by rw [hF8] <;> norm_num)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ppEight hv).symm
  refine ⟨TauCeti.CFSGIndex.lie ⟨.A 1 ppEight, hv⟩, ?_, ⟨e⟩⟩
  show ppEight.card = 8
  norm_num [ppEight, TauCeti.PrimePower.card_def]

theorem typed_nine_gram (A : primeFormUnitary hF4 (idGram F4 6)) {c : F4ˣ} (hc : c ≠ 1)
    (hA : (A : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {J : Subgroup ↥(gramSU hF4 (idGram F4 6))}
    (hJ : GLAPComponent 3 (fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A)) J) :
    catalogIs (PSimple 3 J) S10.isL2eight := by
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
  rw [hJeq]
  exact catalogIs_of_mulEquiv (ePS.trans eKP).symm (catalogIs_L2eight_of_sl2 hE.fixedField hF8)

theorem typed_nine (B : primeFormUnitary hF4 (idGram F4 6)) {c : F4ˣ} (hc : c ≠ 1)
    (hB : (B : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {J : Subgroup M6} (hJ : GLAPComponent 3 (CenD (B : GL (Fin 6) F4)) J) :
    catalogIs (PSimple 3 J) S10.isL2eight := by
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
  have h := typed_nine_gram B hc hB hmap
  obtain ⟨e⟩ := pSimple_map_equiv 3 eGram6 J
  exact catalogIs_of_mulEquiv e h

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
