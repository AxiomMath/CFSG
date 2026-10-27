module

public import CFSG.LieType.AschbacherSeitz.ExceptionalInvolutionsDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Classes
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.LieType.AschbacherSeitz

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Balance
  CFSG.ComponentClassification.RankTwoExceptional CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
  CFSG.StandardType

private lemma pinnedFamilySign_cast_eq_one (K : Type) [Field K] [CharP K 2]
    (γ : Fin Tag.F4.rank → ℤ) :
    (((rootOperatorFamily Tag.F4).pinnedFamilySign γ : ℤ) : K) = 1 := by
  rcases (rootOperatorFamily Tag.F4).pinnedFamilySign_eq γ with h | h
  · rw [h]; norm_num
  · rw [h]; simpa using (CharTwo.neg_eq (1 : K))

private lemma f4Rep_eq_xPar (K : Type) [Field K] [CharP K 2] (p : ℕ) (hp : 24 ≤ p ∧ p ≤ 47) :
    f4Rep K [p] = xPar (rootOperatorFamily Tag.F4) (orbitCertRoot Tag.F4 p) 1 := by
  have hγ := (f4_isRoot_pos hp).1
  refine Subtype.ext ?_
  calc ((f4Rep K [p] : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)
      = pinnedX Tag.F4 K (orbitCertRoot Tag.F4 p) 1 := by
        simp [f4Rep, coe_f4Rep_singleton, f4x]
    _ = pinnedX Tag.F4 K (orbitCertRoot Tag.F4 p)
          (((rootOperatorFamily Tag.F4).pinnedFamilySign (orbitCertRoot Tag.F4 p) : ℤ) * (1 : K)) := by
        rw [pinnedFamilySign_cast_eq_one, one_mul]
    _ = ((xPar (rootOperatorFamily Tag.F4) (orbitCertRoot Tag.F4 p) 1 : adjointGroup Tag.F4 K) :
          ModGL Tag.F4 K) := (coe_xPar_eq_pinnedX hγ 1).symm

private lemma f4Rep_mem_rootGroup (K : Type) [Field K] [CharP K 2] (p : ℕ)
    (hp : 24 ≤ p ∧ p ≤ 47) :
    f4Rep K [p] ∈ (f4Datum K).rootGroup (orbitCertRoot Tag.F4 p) := by
  have hγ := (f4_isRoot_pos hp).1
  rw [f4Rep_eq_xPar K p hp]
  exact xPar_mem hγ 1

def F4ASClass (Z : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  ∃ L ∈ asClassList StatedLieTag.F4, Z = {β | List.ofFn β ∈ L}


theorem f4_universal_model (f : ℕ) (s : adjointGroup Tag.F4 (GaloisField 2 f))
    (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    ∃ g : adjointGroup Tag.F4 (GaloisField 2 f), ∃ Z : Set (Fin Tag.F4.rank → ℤ),
      F4ASClass Z ∧
      g * s * g⁻¹ ∈ ⨆ β ∈ Z, (f4Datum (GaloisField 2 f)).rootGroup β := by
  let Z1 : Set (Fin Tag.F4.rank → ℤ) := {β | List.ofFn β ∈ [[2, 3, 4, 2]]}
  let Z2 : Set (Fin Tag.F4.rank → ℤ) := {β | List.ofFn β ∈ [[1, 2, 3, 2]]}
  let Z3 : Set (Fin Tag.F4.rank → ℤ) :=
    {β | List.ofFn β ∈ [[2, 3, 4, 2], [1, 2, 3, 2]]}
  let Z4 : Set (Fin Tag.F4.rank → ℤ) :=
    {β | List.ofFn β ∈ [[1, 2, 2, 1], [1, 2, 4, 2]]}
  have hZ1 : F4ASClass Z1 := ⟨[[2, 3, 4, 2]], by simp [asClassList], rfl⟩
  have hZ2 : F4ASClass Z2 := ⟨[[1, 2, 3, 2]], by simp [asClassList], rfl⟩
  have hZ3 : F4ASClass Z3 :=
    ⟨[[2, 3, 4, 2], [1, 2, 3, 2]], by simp [asClassList], rfl⟩
  have hZ4 : F4ASClass Z4 :=
    ⟨[[1, 2, 2, 1], [1, 2, 4, 2]], by simp [asClassList], rfl⟩
  have h47 : List.ofFn (orbitCertRoot Tag.F4 47) = [2, 3, 4, 2] := by decide +kernel
  have h44 : List.ofFn (orbitCertRoot Tag.F4 44) = [1, 2, 3, 2] := by decide +kernel
  have h41 : List.ofFn (orbitCertRoot Tag.F4 41) = [1, 2, 2, 1] := by decide +kernel
  have h45 : List.ofFn (orbitCertRoot Tag.F4 45) = [1, 2, 4, 2] := by decide +kernel
  have hmem47 : orbitCertRoot Tag.F4 47 ∈ Z1 := by
    simp only [Z1, Set.mem_setOf_eq]; rw [h47]; simp
  have hmem44 : orbitCertRoot Tag.F4 44 ∈ Z2 := by
    simp only [Z2, Set.mem_setOf_eq]; rw [h44]; simp
  have hmem44' : orbitCertRoot Tag.F4 44 ∈ Z3 := by
    simp only [Z3, Set.mem_setOf_eq]; rw [h44]; simp
  have hmem47' : orbitCertRoot Tag.F4 47 ∈ Z3 := by
    simp only [Z3, Set.mem_setOf_eq]; rw [h47]; simp
  have hmem41 : orbitCertRoot Tag.F4 41 ∈ Z4 := by
    simp only [Z4, Set.mem_setOf_eq]; rw [h41]; simp
  have hmem45 : orbitCertRoot Tag.F4 45 ∈ Z4 := by
    simp only [Z4, Set.mem_setOf_eq]; rw [h45]; simp
  have hM47 : f4Rep (GaloisField 2 f) [47] ∈
      (f4Datum (GaloisField 2 f)).rootGroup (orbitCertRoot Tag.F4 47) :=
    f4Rep_mem_rootGroup (GaloisField 2 f) 47 ⟨by norm_num, by norm_num⟩
  have hM44 : f4Rep (GaloisField 2 f) [44] ∈
      (f4Datum (GaloisField 2 f)).rootGroup (orbitCertRoot Tag.F4 44) :=
    f4Rep_mem_rootGroup (GaloisField 2 f) 44 ⟨by norm_num, by norm_num⟩
  have hM41 : f4Rep (GaloisField 2 f) [41] ∈
      (f4Datum (GaloisField 2 f)).rootGroup (orbitCertRoot Tag.F4 41) :=
    f4Rep_mem_rootGroup (GaloisField 2 f) 41 ⟨by norm_num, by norm_num⟩
  have hM45 : f4Rep (GaloisField 2 f) [45] ∈
      (f4Datum (GaloisField 2 f)).rootGroup (orbitCertRoot Tag.F4 45) :=
    f4Rep_mem_rootGroup (GaloisField 2 f) 45 ⟨by norm_num, by norm_num⟩
  obtain ⟨y, hy, c, hc⟩ :=
    classesCover_AS (K := GaloisField 2 f) s hs2 hs1
  have hys : (↑c)⁻¹ * s * ((↑c)⁻¹)⁻¹ = y := by
    have h1 : s * ↑c = ↑c * y := hc.symm
    calc (↑c)⁻¹ * s * ((↑c)⁻¹)⁻¹ = (↑c)⁻¹ * (s * ↑c) := by group
      _ = (↑c)⁻¹ * (↑c * y) := by rw [h1]
      _ = y := by group
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · refine ⟨(↑c)⁻¹, Z1, hZ1, ?_⟩
    rw [hys]
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hmem47 hM47)
  · refine ⟨(↑c)⁻¹, Z2, hZ2, ?_⟩
    rw [hys]
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hmem44 hM44)
  · refine ⟨(↑c)⁻¹, Z3, hZ3, ?_⟩
    rw [hys, f4Rep_pair]
    exact Subgroup.mul_mem _
      (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hmem47' hM47))
      (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hmem44' hM44))
  · refine ⟨(↑c)⁻¹, Z4, hZ4, ?_⟩
    rw [hys, f4Rep_pair]
    exact Subgroup.mul_mem _
      (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hmem41 hM41))
      (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hmem45 hM45))

theorem ggExcKUniversalInvolutionsAt_F4 : GGExcKUniversalInvolutionsAt StatedLieTag.F4 := by
  intro n f _ hf s hs1 hs2
  obtain ⟨g, Z, hZ, hmem⟩ := f4_universal_model f s hs1 hs2
  exact ⟨g, Z, hZ, hmem⟩

end CFSG.LieType.AschbacherSeitz

end
