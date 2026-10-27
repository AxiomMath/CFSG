module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Nine
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Polynomial CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

namespace U4InnU6

theorem perfect_card_nine_gram (A : primeFormUnitary hF4 (idGram F4 6)) {c : F4ˣ} (hc : c ≠ 1)
    (hA : (A : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {J : Subgroup ↥(gramSU hF4 (idGram F4 6))}
    (hJC : J ≤ fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A))
    (hperf : Group.IsPerfect ↥J) : Nat.card J ∣ 504 := by
  obtain ⟨H, a, huniq, hself, hmult, hdeg⟩ := data_of_nine A hc hA
  have hq : 2 ≤ 2 ^ 1 := by norm_num
  have hgood : IsGoodBlock hF4 (xOf (A : GL (Fin 6) F4)) a :=
    ⟨by omega, fun _ => by simp [hmult, hdeg]⟩
  let α := primeFormConjSU hF4 (idGram F4 6) A
  let K₀ : Subgroup ↥(gramSU hF4 (idGram F4 6)) :=
    (specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a).comap (toLinSU hF4 6)
  have hSBle : specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a ≤
      (toLinSU hF4 6).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a hgood hg)
  have hFmap : K₀.map (toLinSU hF4 6) = specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a :=
    Subgroup.map_comap_eq_self hSBle
  let eK : ↥K₀ ≃* ↥(specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a) :=
    (Subgroup.equivMapOfInjective K₀ (toLinSU hF4 6) toLinSU_injective).trans
      (MulEquiv.subgroupCongr hFmap)
  haveI : Group.IsPerfect ↥J := hperf
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
  have hcard : Nat.card ↥K₀ = 504 := by
    rw [Nat.card_congr ((eK.trans e2).trans e3).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF8]
    norm_num
  exact (Subgroup.card_dvd_of_le hJK₀).trans (dvd_of_eq hcard)

theorem perfect_card_nine (B : primeFormUnitary hF4 (idGram F4 6)) {c : F4ˣ} (hc : c ≠ 1)
    (hB : (B : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {L : Subgroup M6} (hLC : L ≤ CenD (B : GL (Fin 6) F4)) (hperf : Group.IsPerfect ↥L) :
    Nat.card L ∣ 504 := by
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
  have hmap : L.map eGram6.toMonoidHom ≤ fixSubgroup (primeFormConjSU hF4 (idGram F4 6) B) := by
    rw [← hfix]
    exact Subgroup.map_mono hLC
  have hperf' : Group.IsPerfect ↥(L.map eGram6.toMonoidHom) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperf]
  have := perfect_card_nine_gram B hc hB hmap hperf'
  rwa [Subgroup.card_map_of_injective eGram6.injective] at this

end U4InnU6

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
