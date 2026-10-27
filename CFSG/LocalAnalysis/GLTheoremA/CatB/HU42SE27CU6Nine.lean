module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Defs
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Nine

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open Polynomial CFSG.Open CFSG.Fischer
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

private theorem perfect_le_specialBlock_comap
    (A : primeFormUnitary hF4 (idGram F4 6))
    {a : primaryFactors ((xOf (A : GL (Fin 6) F4) : LinearMap.GeneralLinearGroup F4
      (Fin 6 → F4)) : Module.End F4 (Fin 6 → F4))}
    (huniq : ∀ b : primaryFactors ((xOf (A : GL (Fin 6) F4) : LinearMap.GeneralLinearGroup F4
      (Fin 6 → F4)) : Module.End F4 (Fin 6 → F4)), b = a)
    {J : Subgroup ↥(gramSU hF4 (idGram F4 6))}
    (hJC : J ≤ fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A))
    (hJperf : ⁅J, J⁆ = J) :
    J ≤ (specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a).comap (toLinSU hF4 6) := by
  intro g hg
  rw [Subgroup.mem_comap, mem_specialBlock]
  have hgC : g ∈ fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A) := hJC hg
  refine ⟨⟨toLinSU_mem_unitaryCentralizer A rfl hgC, fun b hb hbS v hv => ?_⟩, ?_⟩
  · exact absurd (Or.inl (congrArg Subtype.val (huniq ⟨b, hb⟩))) hbS
  · refine ⟨(mem_fixSubgroup_primeFormConjSU_iff A rfl g).mp hgC, ?_⟩
    haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJperf
    let φ : ↥(fixSubgroup (primeFormConjSU hF4 (idGram F4 6) A)) →*
        gl_centralizer (xOf (A : GL (Fin 6) F4)) :=
      ((toLinSU hF4 6).comp (fixSubgroup _).subtype).codRestrict _ fun g =>
        (mem_fixSubgroup_primeFormConjSU_iff A rfl g.1).mp g.2
    let ψ : ↥J →* (AdjoinRoot (a : F4[X]))ˣ :=
      (blockDetHom (xOf (A : GL (Fin 6) F4)) (a : F4[X])).comp
        (φ.comp (Subgroup.inclusion hJC))
    exact perfect_hom_trivial ψ ⟨g, hg⟩

private theorem card_specialBlock_comap
    (A : primeFormUnitary hF4 (idGram F4 6))
    (H : UnitaryPrimaryData hF4.bar (idForm hF4 6) (xOf (A : GL (Fin 6) F4)))
    {a : primaryFactors ((xOf (A : GL (Fin 6) F4) : LinearMap.GeneralLinearGroup F4
      (Fin 6 → F4)) : Module.End F4 (Fin 6 → F4))}
    (hself : dualPoly hF4.bar (a : F4[X]) = a)
    (hmult : primaryMultiplicity ((xOf (A : GL (Fin 6) F4) : LinearMap.GeneralLinearGroup F4
      (Fin 6 → F4)) : Module.End F4 (Fin 6 → F4)) (a : F4[X]) = 2)
    (hdeg : (a : F4[X]).natDegree = 3) :
    Nat.card ↥((specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a).comap
      (toLinSU hF4 6)) = 504 := by
  have hq : 2 ≤ 2 ^ 1 := by norm_num
  have hgood : IsGoodBlock hF4 (xOf (A : GL (Fin 6) F4)) a :=
    ⟨by omega, fun _ => by simp [hmult, hdeg]⟩
  have hSBle : specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a ≤
      (toLinSU hF4 6).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a hgood hg)
  have hFmap : ((specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a).comap
      (toLinSU hF4 6)).map (toLinSU hF4 6) =
      specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a :=
    Subgroup.map_comap_eq_self hSBle
  let K₀ : Subgroup ↥(gramSU hF4 (idGram F4 6)) :=
    (specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a).comap (toLinSU hF4 6)
  let eK : ↥K₀ ≃* ↥(specialBlock (idForm hF4 6) (xOf (A : GL (Fin 6) F4)) a) :=
    (Subgroup.equivMapOfInjective K₀ (toLinSU hF4 6) toLinSU_injective).trans
      (MulEquiv.subgroupCongr hFmap)
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e2⟩⟩ :=
    nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
  obtain ⟨e3⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf
    hHfl (by exact hmult)
  haveI : Finite hE.fixedField := inferInstance
  letI : Fintype hE.fixedField := Fintype.ofFinite _
  have hcardF : Fintype.card hE.fixedField = 2 ^ (1 * (a : F4[X]).natDegree) := by
    rw [← Nat.card_eq_fintype_card]
    exact hE.card_fixedField
  have hF8 : Nat.card hE.fixedField = 8 := by
    rw [Nat.card_eq_fintype_card, hcardF, hdeg]
    norm_num
  let eS := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 hE.fixedField
  let eKP : ↥K₀ ≃* StatedSL 2 hE.fixedField := ((eK.trans e2).trans e3).trans eS
  rw [Nat.card_congr eKP.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF8]
  norm_num

theorem u6NineFact_holds : U6NineFact := by
  intro B c hc hB J hJC hJperf
  obtain ⟨H, a, huniq, hself, hmult, hdeg⟩ := data_of_nine B hc hB
  let K₀ : Subgroup ↥(gramSU hF4 (idGram F4 6)) :=
    (specialBlock (idForm hF4 6) (xOf (B : GL (Fin 6) F4)) a).comap (toLinSU hF4 6)
  let J' : Subgroup ↥(gramSU hF4 (idGram F4 6)) := J.map eGram6.toMonoidHom
  have hfix : (CenD (B : GL (Fin 6) F4)).map eGram6.toMonoidHom =
      fixSubgroup (primeFormConjSU hF4 (idGram F4 6) B) := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_CenD, mem_fixSubgroup]
    change (y : GL (Fin 6) F4) * B = B * y ↔
      (⟨(B : GL (Fin 6) F4) * y * (B : GL (Fin 6) F4)⁻¹, _⟩ :
        ↥(gramSU hF4 (idGram F4 6))) = y
    rw [Subtype.ext_iff]
    change _ ↔ (B : GL (Fin 6) F4) * y * (B : GL (Fin 6) F4)⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hJ'C : J' ≤ fixSubgroup (primeFormConjSU hF4 (idGram F4 6) B) := by
    rw [← hfix]
    exact Subgroup.map_mono hJC
  have hJ'perf : ⁅J', J'⁆ = J' := by
    show ⁅J.map eGram6.toMonoidHom, J.map eGram6.toMonoidHom⁆ = J.map eGram6.toMonoidHom
    rw [← Subgroup.map_commutator, hJperf]
  have hJ'K : J' ≤ K₀ := perfect_le_specialBlock_comap B huniq hJ'C hJ'perf
  have hKcard : Nat.card ↥K₀ = 504 := card_specialBlock_comap B H hself hmult hdeg
  have hJ'dvd : Nat.card ↥J' ∣ 504 := by
    rw [← hKcard]
    exact Subgroup.card_dvd_of_le hJ'K
  have hcard : Nat.card ↥J = Nat.card ↥J' :=
    (Subgroup.card_map_of_injective (K := J) (f := eGram6.toMonoidHom) eGram6.injective).symm
  rw [hcard]
  exact hJ'dvd

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
