module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate118
public import Certificates.Certificate122

import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceLevi
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFaceD4Rank
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviChar
import CFSG.LinearAlgebra.LinearGroups.SLConjugationEmb
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

local notation "Γ₂" F => ModGL TwistTag.E6.tag F



private lemma pow_eq_self_of_pow_three_eq_one {M : Type*} [Group M] {q : ℕ} (hq : q % 3 = 2)
    {μ : M} (hμq : μ ^ q = μ) (hμ3 : μ ^ 3 = 1) : μ = 1 := by
  have hqeq : q = 3 * (q / 3) + 2 := by
    have h := Nat.mod_add_div q 3
    omega
  have hμ2 : μ ^ q = μ ^ 2 := by
    rw [hqeq, pow_add, pow_mul, hμ3, one_pow, one_mul]
  have hμeq : μ = μ ^ 2 := hμq.symm.trans hμ2
  have h : μ * 1 = μ * μ := by simpa [pow_two] using hμeq
  exact (mul_left_cancel h).symm

theorem TwFace.rootDiagUnit_eq_one_of_twistHom_eq {F : Type} [Field F] {q : ℕ} (hq : q % 3 = 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q) (b : Fin TwistTag.E6.tag.rank → Fˣ)
    (hb : ∀ i : Fin TwistTag.E6.tag.rank, i.val ≠ 3 → b i = 1)
    (hφ : twistHom TwistTag.E6 F σ.toRingHom (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b)
    (h3 : rootDiagUnit TwistTag.E6.tag b ^ 3 = 1) : rootDiagUnit TwistTag.E6.tag b = 1 := by
  have hb_eq : (fun i : Fin TwistTag.E6.tag.rank =>
      Units.map σ.toRingHom.toMonoidHom (b (TwistTag.E6.perm.symm i))) = b := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [← twistHom_rootDiagUnit_eq (b := b)]
    exact hφ
  have hfix : TwistTag.E6.perm.symm (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) =
      ⟨3, by decide⟩ := by decide +kernel
  have hμσ : Units.map σ.toRingHom.toMonoidHom (b ⟨3, by decide⟩) = b ⟨3, by decide⟩ := by
    have h := congr_fun hb_eq (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank)
    rwa [hfix] at h
  have hμq : (b ⟨3, by decide⟩) ^ q = b ⟨3, by decide⟩ := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hσ (b ⟨3, by decide⟩ : F)]
    exact congrArg Units.val hμσ
  have hb3 : b ^ 3 = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    change rootDiagUnitHom TwistTag.E6.tag F (b ^ 3) = rootDiagUnitHom TwistTag.E6.tag F 1
    rw [map_pow, map_one]
    exact h3
  have hμ3 : (b ⟨3, by decide⟩) ^ 3 = 1 := by
    have h := congr_fun hb3 (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank)
    simpa using h
  have hμ1 : b ⟨3, by decide⟩ = 1 := pow_eq_self_of_pow_three_eq_one hq hμq hμ3
  have hb1 : b = 1 := by
    funext i
    by_cases hi : i.val = 3
    · have hii : i = (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) := Fin.ext hi
      rw [hii, hμ1]
      rfl
    · simpa using hb i hi
  rw [hb1, rootDiagUnit_one]

private def twFaceS1 : Set (Fin TwistTag.E6.tag.rank) :=
  {⟨0, by decide⟩, ⟨2, by decide⟩}

private def twFaceS2 : Set (Fin TwistTag.E6.tag.rank) :=
  {⟨4, by decide⟩, ⟨5, by decide⟩}

private def twFaceS3 : Set (Fin TwistTag.E6.tag.rank) :=
  {⟨1, by decide⟩}

private lemma mem_twFaceS1 {i : Fin TwistTag.E6.tag.rank} :
    i ∈ twFaceS1 ↔ i.val = 0 ∨ i.val = 2 := by
  fin_cases i <;>
    simp only [twFaceS1, Set.mem_insert_iff, Set.mem_singleton_iff] <;> decide

private lemma mem_twFaceS2 {i : Fin TwistTag.E6.tag.rank} :
    i ∈ twFaceS2 ↔ i.val = 4 ∨ i.val = 5 := by
  fin_cases i <;>
    simp only [twFaceS2, Set.mem_insert_iff, Set.mem_singleton_iff] <;> decide

private lemma mem_twFaceS3 {i : Fin TwistTag.E6.tag.rank} :
    i ∈ twFaceS3 ↔ i.val = 1 := by
  fin_cases i <;>
    simp only [twFaceS3, Set.mem_insert_iff, Set.mem_singleton_iff] <;> decide

private lemma disjoint_twFaceS1_S2 : Disjoint twFaceS1 twFaceS2 := by
  rw [Set.disjoint_left]
  intro i hi hj
  rw [mem_twFaceS1] at hi
  rw [mem_twFaceS2] at hj
  omega

private lemma disjoint_twFaceS1_S3 : Disjoint twFaceS1 twFaceS3 := by
  rw [Set.disjoint_left]
  intro i hi hj
  rw [mem_twFaceS1] at hi
  rw [mem_twFaceS3] at hj
  omega

private lemma disjoint_twFaceS2_S3 : Disjoint twFaceS2 twFaceS3 := by
  rw [Set.disjoint_left]
  intro i hi hj
  rw [mem_twFaceS2] at hi
  rw [mem_twFaceS3] at hj
  omega

private lemma disjoint_twFaceS1_union : Disjoint twFaceS1 (twFaceS2 ∪ twFaceS3) := by
  rw [Set.disjoint_union_right]
  exact ⟨disjoint_twFaceS1_S2, disjoint_twFaceS1_S3⟩

private lemma disjoint_twFaceS3_union : Disjoint twFaceS3 (twFaceS1 ∪ twFaceS2) := by
  rw [Set.disjoint_union_right]
  exact ⟨disjoint_twFaceS1_S3.symm, disjoint_twFaceS2_S3.symm⟩

private lemma cartan_twFaceS1_S2 :
    ∀ i ∈ twFaceS1, ∀ j ∈ twFaceS2, TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  rw [mem_twFaceS1] at hi
  rw [mem_twFaceS2] at hj
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma cartan_twFaceS1_S3 :
    ∀ i ∈ twFaceS1, ∀ j ∈ twFaceS3, TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  rw [mem_twFaceS1] at hi
  rw [mem_twFaceS3] at hj
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma cartan_twFaceS2_S3 :
    ∀ i ∈ twFaceS2, ∀ j ∈ twFaceS3, TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  rw [mem_twFaceS2] at hi
  rw [mem_twFaceS3] at hj
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma cartan_twFaceS1_union :
    ∀ i ∈ twFaceS1, ∀ j ∈ twFaceS2 ∪ twFaceS3, TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  rw [mem_twFaceS1] at hi
  rw [Set.mem_union, mem_twFaceS2, mem_twFaceS3] at hj
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma cartan_twFaceS3_union :
    ∀ i ∈ twFaceS3, ∀ j ∈ twFaceS1 ∪ twFaceS2, TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  rw [mem_twFaceS3] at hi
  rw [Set.mem_union, mem_twFaceS1, mem_twFaceS2] at hj
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma orbitUnion_twFace_eq :
    TwistTag.E6.orbitUnion twE6MaxA2A1 = twFaceS1 ∪ twFaceS2 ∪ twFaceS3 := by
  rw [orbitUnion_twE6MaxA2A1]
  ext i
  simp only [twFaceS1, twFaceS2, twFaceS3, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_union, Set.mem_ofPred_eq]
  revert i
  decide

private lemma perm_image_twFaceS1 : TwistTag.E6.perm '' twFaceS1 = twFaceS2 := by
  ext i
  fin_cases i <;>
    simp only [twFaceS1, twFaceS2, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff] <;>
    decide

private lemma mod_three_of_dvd_two_pow_add_one {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) :
    2 ^ n % 3 = 2 := by
  have h := Nat.mod_eq_zero_of_dvd h3
  omega

private lemma four_le_card_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) : 4 ≤ Nat.card F := by
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 4 ≤ (2 ^ n) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2n 2
  omega

private lemma three_ne_zero_of_charP_two {F : Type} [Field F] [CharP F 2] :
    (3 : F) ≠ 0 := by
  intro h
  exact absurd ((CharP.cast_eq_zero_iff F 2 3).mp h) (by norm_num)

private lemma ringChar_ne_three_of_charP_two {F : Type} [Field F] [CharP F 2] :
    ringChar F ≠ 3 := by
  rw [ringChar.eq F 2]
  norm_num

private lemma not_dvd_cartan_twFaceS1 :
    ∃ k : Fin TwistTag.E6.tag.rank,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 (0 : Fin TwistTag.E6.tag.rank) k +
        2 * Tag.cartan .E6 (2 : Fin TwistTag.E6.tag.rank) k := by
  refine ⟨⟨3, by decide⟩, ?_⟩
  have h : (Tag.cartan .E6 (0 : Fin TwistTag.E6.tag.rank) ⟨3, by decide⟩ +
      2 * Tag.cartan .E6 (2 : Fin TwistTag.E6.tag.rank) ⟨3, by decide⟩ : ℤ) = -2 := by
    decide
  have hneg : ¬ (3 : ℤ) ∣ (-2 : ℤ) := by
    intro hd
    have hmod : (-2 : ℤ) % 3 = 0 := Int.dvd_iff_emod_eq_zero.mp hd
    rw [show (-2 : ℤ) % 3 = 1 by norm_num] at hmod
    exact one_ne_zero hmod
  exact h.symm ▸ hneg

private lemma not_dvd_cartan_twFaceS2 :
    ∃ k : Fin TwistTag.E6.tag.rank,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 (4 : Fin TwistTag.E6.tag.rank) k +
        2 * Tag.cartan .E6 (5 : Fin TwistTag.E6.tag.rank) k := by
  refine ⟨⟨3, by decide⟩, ?_⟩
  have h : (Tag.cartan .E6 (4 : Fin TwistTag.E6.tag.rank) ⟨3, by decide⟩ +
      2 * Tag.cartan .E6 (5 : Fin TwistTag.E6.tag.rank) ⟨3, by decide⟩ : ℤ) = -1 := by
    decide
  have hneg : ¬ (3 : ℤ) ∣ (-1 : ℤ) := by
    intro hd
    have hmod : (-1 : ℤ) % 3 = 0 := Int.dvd_iff_emod_eq_zero.mp hd
    rw [show (-1 : ℤ) % 3 = 2 by norm_num] at hmod
    norm_num at hmod
  exact h.symm ▸ hneg

private lemma centralizer_twFaceS1_le_twFaceS2 {F : Type} [Field F] (σ : F ≃+* F)
    {f₁ : TwFace.LeviFactor F 3 twFaceS1} {f₂ : TwFace.LeviFactor F 3 twFaceS2}
    {x : Γ₂ F} (hx : x ∈ Subgroup.centralizer (f₁.ι.range : Set (Γ₂ F)))
    (hxF : twistHom TwistTag.E6 F σ.toRingHom x = x) :
    x ∈ Subgroup.centralizer (f₂.ι.range : Set (Γ₂ F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ (subsystemGroup TwistTag.E6.tag F twFaceS1).map
      (twistHom TwistTag.E6 F σ.toRingHom) := by
    have hsub := TwFace.subsystemGroup_image_perm_le_map_twistHom (F := F) σ twFaceS1
    rw [perm_image_twFaceS1] at hsub
    exact hsub (by rw [← f₂.range_eq]; exact hy)
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
  have hz' : z ∈ f₁.ι.range := by rw [f₁.range_eq]; exact hz
  have hxz : z * x = x * z := Subgroup.mem_centralizer_iff.mp hx z hz'
  calc y * x = twistHom TwistTag.E6 F σ.toRingHom z * x := by rw [← hzy]
    _ = twistHom TwistTag.E6 F σ.toRingHom z * twistHom TwistTag.E6 F σ.toRingHom x := by
        rw [hxF]
    _ = twistHom TwistTag.E6 F σ.toRingHom (z * x) := by rw [← map_mul]
    _ = twistHom TwistTag.E6 F σ.toRingHom (x * z) := by rw [hxz]
    _ = twistHom TwistTag.E6 F σ.toRingHom x * twistHom TwistTag.E6 F σ.toRingHom z := by
        rw [map_mul]
    _ = x * y := by rw [hxF, hzy]

private lemma eq_one_of_mem_twFace_centralizers {F : Type} [Field F] {q : ℕ} (hq : q % 3 = 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q)
    {f₁ : TwFace.LeviFactor F 3 twFaceS1} {f₂ : TwFace.LeviFactor F 3 twFaceS2}
    {f₃ : TwFace.LeviFactor F 2 twFaceS3} {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1 ⊔
      twistedE6DiagGL F σ)
    (hEel : IsElemAbelian 3 E) {x : Γ₂ F} (hxE : x ∈ E)
    (hc₁ : x ∈ Subgroup.centralizer (f₁.ι.range : Set (Γ₂ F)))
    (hc₂ : x ∈ Subgroup.centralizer (f₂.ι.range : Set (Γ₂ F)))
    (hc₃ : x ∈ Subgroup.centralizer (f₃.ι.range : Set (Γ₂ F))) : x = 1 := by
  obtain ⟨b, hb_eq, hb_one⟩ := TwFace.exists_rootDiagUnit_eq_of_mem_levi_sup_diag σ
    f₁ f₂ f₃ disjoint_twFaceS1_S2 disjoint_twFaceS1_S3 disjoint_twFaceS2_S3
    cartan_twFaceS1_S2 cartan_twFaceS1_S3 cartan_twFaceS2_S3 orbitUnion_twFace_eq
    (hE hxE) hc₁ hc₂ hc₃
  have hb' : ∀ i : Fin TwistTag.E6.tag.rank, i.val ≠ 3 → b i = 1 := by
    intro i hi
    exact hb_one i (by rw [← orbitUnion_twFace_eq, orbitUnion_twE6MaxA2A1]; exact hi)
  have hφ : twistHom TwistTag.E6 F σ.toRingHom (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
    have h := levi_sup_diag_le_eqLocus σ twE6MaxA2A1 (hE hxE)
    rwa [hb_eq] at h
  have hord : rootDiagUnit TwistTag.E6.tag b ^ 3 = 1 := by
    have h := hEel.2 x hxE
    rwa [hb_eq] at h
  rw [hb_eq, TwFace.rootDiagUnit_eq_one_of_twistHom_eq hq σ hσ b hb' hφ hord]

private lemma card_le_mul_card_inf_centralizers {F : Type} [Field F] [Finite F]
    (σ : F ≃+* F) (h3F : (3 : F) ≠ 0) (hrc : ringChar F ≠ 3) (h4F : 4 ≤ Nat.card F)
    {f₁ : TwFace.LeviFactor F 3 twFaceS1} {f₃ : TwFace.LeviFactor F 2 twFaceS3}
    {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1 ⊔
      twistedE6DiagGL F σ)
    (hEel : IsElemAbelian 3 E) [Finite ↥E] :
    Nat.card ↥E ≤ 9 * (3 * Nat.card ↥((E ⊓ Subgroup.centralizer
      (f₁.ι.range : Set (Γ₂ F))) ⊓ Subgroup.centralizer (f₃.ι.range : Set (Γ₂ F)))) := by
  let C₁ : Subgroup (Γ₂ F) := Subgroup.centralizer (f₁.ι.range : Set (Γ₂ F))
  let C₃ : Subgroup (Γ₂ F) := Subgroup.centralizer (f₃.ι.range : Set (Γ₂ F))
  change Nat.card ↥E ≤ 9 * (3 * Nat.card ↥((E ⊓ C₁) ⊓ C₃))
  haveI : Finite ↥(E ⊓ C₁) :=
    Finite.of_injective (fun x : ↥(E ⊓ C₁) => (⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩ : ↥E))
      (fun x y h => Subtype.ext (congrArg (fun z : ↥E => (z : Γ₂ F)) h))
  have h₁ : Nat.card ↥E ≤ 9 * Nat.card ↥(E ⊓ C₁) :=
    CFSG.LinearGroups.card_le_nine_mul_card_inf_centralizer_of_sl3 (E := E) h3F f₁.ι
      f₁.injective hEel
      (fun x hx => TwFace.LeviFactor.exists_conj_of_mem_levi_sup_diag (J := twE6MaxA2A1) σ f₁
        disjoint_twFaceS1_union cartan_twFaceS1_union
        (by rw [orbitUnion_twFace_eq, Set.union_assoc]) (hE hx))
  have h₂ : Nat.card ↥(E ⊓ C₁) ≤ 3 * Nat.card ↥((E ⊓ C₁) ⊓ C₃) :=
    CFSG.LinearGroups.card_le_three_mul_card_inf_centralizer_of_sl2 (E := E ⊓ C₁) hrc h4F f₃.ι
      f₃.injective (IsElemAbelian.mono hEel inf_le_left)
      (fun x hx => TwFace.LeviFactor.exists_conj_of_mem_levi_sup_diag (J := twE6MaxA2A1) σ f₃
        disjoint_twFaceS3_union cartan_twFaceS3_union
        (by rw [orbitUnion_twFace_eq]; exact Set.union_comm _ _) (hE hx.1))
  calc Nat.card ↥E ≤ 9 * Nat.card ↥(E ⊓ C₁) := h₁
    _ ≤ 9 * (3 * Nat.card ↥((E ⊓ C₁) ⊓ C₃)) := Nat.mul_le_mul_left 9 h₂

private lemma eq_bot_inf_centralizers {F : Type} [Field F] {q : ℕ} (hq : q % 3 = 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q)
    {f₁ : TwFace.LeviFactor F 3 twFaceS1} {f₂ : TwFace.LeviFactor F 3 twFaceS2}
    {f₃ : TwFace.LeviFactor F 2 twFaceS3} {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1 ⊔
      twistedE6DiagGL F σ)
    (hEel : IsElemAbelian 3 E)
    (hC₂ : E ⊓ Subgroup.centralizer (f₁.ι.range : Set (Γ₂ F)) ≤
      Subgroup.centralizer (f₂.ι.range : Set (Γ₂ F))) :
    (E ⊓ Subgroup.centralizer (f₁.ι.range : Set (Γ₂ F))) ⊓
      Subgroup.centralizer (f₃.ι.range : Set (Γ₂ F)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact eq_one_of_mem_twFace_centralizers hq σ hσ hE hEel hx.1.1 hx.1.2 (hC₂ hx.1) hx.2

theorem card_le_pow_three_of_le_levi_sup_diag_A2A1 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1 ⊔
      twistedE6DiagGL F σ)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 3 := by
  classical
  by_cases hfin : Finite ↥E
  · haveI := hfin
    have hn : 1 ≤ n := by
      have h := CFSG.SeitzReduction.LinearPilot.one_le_of_card_eq_two_pow
        (K := F) (f := n * 2) (by rw [hF, pow_mul])
      omega
    haveI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hn hF
    have hq : 2 ^ n % 3 = 2 := mod_three_of_dvd_two_pow_add_one h3
    have h3F : (3 : F) ≠ 0 := three_ne_zero_of_charP_two
    have hrc : ringChar F ≠ 3 := ringChar_ne_three_of_charP_two
    have h4F : 4 ≤ Nat.card F := four_le_card_of_card_sq hn hF
    obtain ⟨f₁, -⟩ := TwFace.exists_leviFactor_sl3 (F := F) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) (by decide) (by decide) (by decide) not_dvd_cartan_twFaceS1
    obtain ⟨f₂, -⟩ := TwFace.exists_leviFactor_sl3 (F := F) (i := ⟨4, by decide⟩)
      (j := ⟨5, by decide⟩) (by decide) (by decide) (by decide) not_dvd_cartan_twFaceS2
    obtain ⟨f₃, -⟩ := TwFace.exists_leviFactor_sl2 (F := F) ⟨1, by decide⟩
    let C₁ : Subgroup (Γ₂ F) := Subgroup.centralizer (f₁.ι.range : Set (Γ₂ F))
    let C₂ : Subgroup (Γ₂ F) := Subgroup.centralizer (f₂.ι.range : Set (Γ₂ F))
    let C₃ : Subgroup (Γ₂ F) := Subgroup.centralizer (f₃.ι.range : Set (Γ₂ F))
    have hC₂ : E ⊓ C₁ ≤ C₂ := fun x hx =>
      centralizer_twFaceS1_le_twFaceS2 (f₁ := f₁) (f₂ := f₂) σ hx.2
        (levi_sup_diag_le_eqLocus σ twE6MaxA2A1 (hE hx.1))
    have hbound := card_le_mul_card_inf_centralizers (f₁ := f₁) (f₃ := f₃) (E := E)
      σ h3F hrc h4F hE hEel
    have hbot : (E ⊓ C₁) ⊓ C₃ = ⊥ :=
      eq_bot_inf_centralizers (f₁ := f₁) (f₂ := f₂) (f₃ := f₃) (E := E) hq σ hσ hE hEel hC₂
    have hcard : Nat.card ↥((E ⊓ C₁) ⊓ C₃) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    calc Nat.card ↥E ≤ 9 * (3 * Nat.card ↥((E ⊓ C₁) ⊓ C₃)) := hbound
      _ = 3 ^ 3 := by rw [hcard]; norm_num
  · haveI : Infinite ↥E := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite (α := ↥E)]
    exact Nat.zero_le _

end CFSG.LocalAnalysis.GLTheoremA.T173O
