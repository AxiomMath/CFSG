module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate118
public import Certificates.Certificate122

import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceLevi
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceTwist
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFaceD4Rank
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviChar
import CFSG.LinearAlgebra.LinearGroups.SLConjugationEmb
import Mathlib.RingTheory.RootsOfUnity.Basic
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
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

local notation "Γ₂" F => ModGL TwistTag.E6.tag F

local instance : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩


private lemma apply_four_eq_map_apply_two {F : Type} [Field F] (σ : F ≃+* F)
    {b : Fin TwistTag.E6.tag.rank → Fˣ}
    (hφ : twistHom TwistTag.E6 F σ.toRingHom (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b) :
    b ⟨4, by decide⟩ = Units.map σ.toRingHom.toMonoidHom (b ⟨2, by decide⟩) := by
  have hb_eq : (fun i : Fin TwistTag.E6.tag.rank =>
      Units.map σ.toRingHom.toMonoidHom (b (TwistTag.E6.perm.symm i))) = b := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [← twistHom_rootDiagUnit_eq (b := b)]
    exact hφ
  have hfix : TwistTag.E6.perm.symm (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) =
      ⟨2, by decide⟩ := by decide +kernel
  have h := congr_fun hb_eq (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank)
  rw [hfix] at h
  exact h.symm

private lemma apply_two_pow_three {F : Type} [Field F]
    {b : Fin TwistTag.E6.tag.rank → Fˣ}
    (h3 : rootDiagUnit TwistTag.E6.tag b ^ 3 = 1) :
    (b ⟨2, by decide⟩) ^ 3 = 1 := by
  have hb3 : b ^ 3 = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    change rootDiagUnitHom TwistTag.E6.tag F (b ^ 3) = rootDiagUnitHom TwistTag.E6.tag F 1
    rw [map_pow, map_one]
    exact h3
  have h := congr_fun hb3 (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank)
  simpa using h

private lemma eq_of_apply_two_eq {F : Type} [Field F] (σ : F ≃+* F)
    {b b' : Fin TwistTag.E6.tag.rank → Fˣ}
    (hb : ∀ i : Fin TwistTag.E6.tag.rank, i.val ≠ 2 → i.val ≠ 4 → b i = 1)
    (hb' : ∀ i : Fin TwistTag.E6.tag.rank, i.val ≠ 2 → i.val ≠ 4 → b' i = 1)
    (h4 : b ⟨4, by decide⟩ = Units.map σ.toRingHom.toMonoidHom (b ⟨2, by decide⟩))
    (h4' : b' ⟨4, by decide⟩ = Units.map σ.toRingHom.toMonoidHom (b' ⟨2, by decide⟩))
    (h2 : b ⟨2, by decide⟩ = b' ⟨2, by decide⟩) : b = b' := by
  funext i
  by_cases hi2 : i.val = 2
  · have hii : i = (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) := Fin.ext hi2
    rw [hii, h2]
  · by_cases hi4 : i.val = 4
    · have hii : i = (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) := Fin.ext hi4
      rw [hii, h4, h4', h2]
    · rw [hb i hi2 hi4, hb' i hi2 hi4]

theorem TwFace.card_le_three_of_forall_rootDiagUnit {F : Type} [Field F] (σ : F ≃+* F)
    {E : Subgroup (Γ₂ F)}
    (hE : ∀ x ∈ E, ∃ b : Fin TwistTag.E6.tag.rank → Fˣ, x = rootDiagUnit TwistTag.E6.tag b ∧
      ∀ i : Fin TwistTag.E6.tag.rank, i.val ≠ 2 → i.val ≠ 4 → b i = 1)
    (hφ : ∀ x ∈ E, twistHom TwistTag.E6 F σ.toRingHom x = x) (h3 : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 3 := by
  classical
  let b : E → (Fin TwistTag.E6.tag.rank → Fˣ) := fun x => (hE x.val x.property).choose
  have hb : ∀ x : E, x.val = rootDiagUnit TwistTag.E6.tag (b x) ∧
      ∀ i : Fin TwistTag.E6.tag.rank, i.val ≠ 2 → i.val ≠ 4 → b x i = 1 :=
    fun x => (hE x.val x.property).choose_spec
  have hφb : ∀ x : E, twistHom TwistTag.E6 F σ.toRingHom (rootDiagUnit TwistTag.E6.tag (b x)) =
      rootDiagUnit TwistTag.E6.tag (b x) := fun x => by
    have h := hφ x.val x.property
    rwa [(hb x).1] at h
  have h3b : ∀ x : E, rootDiagUnit TwistTag.E6.tag (b x) ^ 3 = 1 := fun x => by
    have h := h3 x.val x.property
    rwa [(hb x).1] at h
  let f : E → rootsOfUnity 3 F := fun x =>
    ⟨b x ⟨2, by decide⟩, show (b x ⟨2, by decide⟩) ^ 3 = 1 from
      apply_two_pow_three (h3b x)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h2 : b x ⟨2, by decide⟩ = b y ⟨2, by decide⟩ := by
      simpa [f] using congrArg (fun z : rootsOfUnity 3 F => (z : Fˣ)) hxy
    have hbxy : b x = b y := eq_of_apply_two_eq σ (hb x).2 (hb y).2
      (apply_four_eq_map_apply_two σ (hφb x)) (apply_four_eq_map_apply_two σ (hφb y)) h2
    exact Subtype.ext (by rw [(hb x).1, (hb y).1, hbxy])
  exact (Nat.card_le_card_of_injective f hf).trans (card_rootsOfUnity F 3)

private theorem one_le_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have h1 : Nat.card F = 1 := by simpa using hF
    exact absurd h1 (Finite.one_lt_card (α := F)).ne'
  · exact h0

private theorem four_le_card_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) : 4 ≤ Nat.card F := by
  have hn := one_le_of_card_sq hF
  have h : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 2 * 2 ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul h h
  rw [hF, pow_two]
  simpa using h2

private theorem two_pow_mod_three {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) : 2 ^ n % 3 = 2 := by
  have h := Nat.mod_eq_zero_of_dvd h3
  omega

private theorem orbitUnion_A1A2_13_05 :
    TwistTag.E6.orbitUnion twE6MaxA1A2 =
      ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank)} : Set _) ∪
        ({(0 : Fin TwistTag.E6.tag.rank), (5 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [orbitUnion_twE6MaxA1A2]
  ext i
  fin_cases i <;> decide

private theorem orbitUnion_A1A2_0_135 :
    TwistTag.E6.orbitUnion twE6MaxA1A2 =
      ({(0 : Fin TwistTag.E6.tag.rank)} : Set _) ∪
        ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank),
          (5 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [orbitUnion_twE6MaxA1A2]
  ext i
  fin_cases i <;> decide

private theorem orbitUnion_A1A2_13_0_5 :
    TwistTag.E6.orbitUnion twE6MaxA1A2 =
      ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank)} : Set _) ∪
        ({(0 : Fin TwistTag.E6.tag.rank)} : Set _) ∪
          ({(5 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [orbitUnion_twE6MaxA1A2]
  ext i
  fin_cases i <;> decide

private theorem perm_image_zero :
    TwistTag.E6.perm '' ({(0 : Fin TwistTag.E6.tag.rank)} : Set _) =
      ({(5 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [Set.image_singleton]
  congr 1

private theorem disjoint_13_05 :
    Disjoint ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank)} : Set _)
      ({(0 : Fin TwistTag.E6.tag.rank), (5 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with hj | hj <;> exact absurd hj (by decide)

private theorem disjoint_0_135 :
    Disjoint ({(0 : Fin TwistTag.E6.tag.rank)} : Set _)
      ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank),
        (5 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl
  rcases hj with hj | hj | hj <;> exact absurd hj (by decide)

private theorem disjoint_13_0 :
    Disjoint ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank)} : Set _)
      ({(0 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> exact absurd hj (by decide)

private theorem disjoint_13_5 :
    Disjoint ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank)} : Set _)
      ({(5 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> exact absurd hj (by decide)

private theorem disjoint_0_5 :
    Disjoint ({(0 : Fin TwistTag.E6.tag.rank)} : Set _)
      ({(5 : Fin TwistTag.E6.tag.rank)} : Set _) := by
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl
  exact absurd hj (by decide)

private theorem cartan_13_05 :
    ∀ i ∈ ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank)} : Set _),
      ∀ j ∈ ({(0 : Fin TwistTag.E6.tag.rank), (5 : Fin TwistTag.E6.tag.rank)} : Set _),
        TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> decide

private theorem cartan_0_135 :
    ∀ i ∈ ({(0 : Fin TwistTag.E6.tag.rank)} : Set _),
      ∀ j ∈ ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank),
        (5 : Fin TwistTag.E6.tag.rank)} : Set _),
        TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl <;> rcases hj with rfl | rfl | rfl <;> decide

private theorem cartan_13_0 :
    ∀ i ∈ ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank)} : Set _),
      ∀ j ∈ ({(0 : Fin TwistTag.E6.tag.rank)} : Set _),
        TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl <;> decide

private theorem cartan_13_5 :
    ∀ i ∈ ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank)} : Set _),
      ∀ j ∈ ({(5 : Fin TwistTag.E6.tag.rank)} : Set _),
        TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl <;> decide

private theorem cartan_0_5 :
    ∀ i ∈ ({(0 : Fin TwistTag.E6.tag.rank)} : Set _),
      ∀ j ∈ ({(5 : Fin TwistTag.E6.tag.rank)} : Set _),
        TwistTag.E6.tag.cartan i j = 0 := by
  intro i hi j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl <;> rcases hj with rfl <;> decide

private theorem card_le_three_mul_card_inf_centralizer_sl3_A1A2 {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
      twistedE6DiagGL F σ)
    (hEel : IsElemAbelian 3 E) (f : TwFace.LeviFactor F 3 ({1, 3} : Set _))
    (hf : ∀ c : F, f.ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F 1 c ∧
      f.ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F 1 c ∧
      f.ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F 3 c ∧
      f.ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F 3 c) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (f.ι.range : Set (Γ₂ F))) := by
  have hq : 2 ^ n % 3 = 2 := two_pow_mod_three h3
  have hφι : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
      twistHom TwistTag.E6 F σ.toRingHom (f.ι g) = f.ι (slFieldAut (Fin 3) F σ g) :=
    fun g => TwFace.twistHom_comp_eq_slFieldAut (F := F) σ
      (i := (1 : Fin TwistTag.E6.tag.rank)) (j := (3 : Fin TwistTag.E6.tag.rank))
      (by decide) (by decide) f.ι hf g
  have hφE : ∀ x ∈ E, twistHom TwistTag.E6 F σ.toRingHom x = x :=
    fun x hx => levi_sup_diag_le_eqLocus σ twE6MaxA1A2 (hE hx)
  have hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin 3) F,
      ∀ g, x * f.ι g * x⁻¹ = f.ι (slConjugation 3 F A g) :=
    fun x hx => TwFace.LeviFactor.exists_conj_of_mem_levi_sup_diag
      (T := ({(0 : Fin TwistTag.E6.tag.rank), (5 : Fin TwistTag.E6.tag.rank)} : Set _))
      σ f disjoint_13_05 cartan_13_05 orbitUnion_A1A2_13_05 (hE hx)
  exact CFSG.LinearGroups.card_le_three_mul_card_inf_centralizer_of_sl3_frob
    hF hq σ hσ f.ι f.injective (twistHom TwistTag.E6 F σ.toRingHom) hφι hEel hφE hconj

private theorem card_le_three_mul_card_inf_centralizer_sl2_A1A2 {F : Type} [Field F] [Finite F]
    (σ : F ≃+* F) {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
      twistedE6DiagGL F σ)
    (hEel : IsElemAbelian 3 E) (f₀ : TwFace.LeviFactor F 2 ({0} : Set _))
    (hrc : ringChar F ≠ 3) (h4 : 4 ≤ Nat.card F) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (f₀.ι.range : Set (Γ₂ F))) := by
  have hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
      ∀ g, x * f₀.ι g * x⁻¹ = f₀.ι (slConjugation 2 F A g) :=
    fun x hx => TwFace.LeviFactor.exists_conj_of_mem_levi_sup_diag
      (T := ({(1 : Fin TwistTag.E6.tag.rank), (3 : Fin TwistTag.E6.tag.rank),
        (5 : Fin TwistTag.E6.tag.rank)} : Set _))
      σ f₀ disjoint_0_135 cartan_0_135 orbitUnion_A1A2_0_135 (hE hx)
  exact CFSG.LinearGroups.card_le_three_mul_card_inf_centralizer_of_sl2
    hrc h4 f₀.ι f₀.injective hEel hconj

private theorem inf_centralizer_sl2_le_centralizer_sl2_A1A2 {F : Type} [Field F] (σ : F ≃+* F)
    {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
      twistedE6DiagGL F σ)
    (f₀ : TwFace.LeviFactor F 2 ({0} : Set _)) (f₅ : TwFace.LeviFactor F 2 ({5} : Set _)) :
    E ⊓ Subgroup.centralizer (f₀.ι.range : Set (Γ₂ F)) ≤
      Subgroup.centralizer (f₅.ι.range : Set (Γ₂ F)) := by
  intro x hx
  have hxE : x ∈ E := (Subgroup.mem_inf.mp hx).1
  have hxfix : twistHom TwistTag.E6 F σ.toRingHom x = x :=
    levi_sup_diag_le_eqLocus σ twE6MaxA1A2 (hE hxE)
  have hxc₀ : x ∈ Subgroup.centralizer (f₀.ι.range : Set (Γ₂ F)) := (Subgroup.mem_inf.mp hx).2
  have hxmap : x ∈ (Subgroup.centralizer (f₀.ι.range : Set (Γ₂ F))).map
      (twistHom TwistTag.E6 F σ.toRingHom) := ⟨x, hxc₀, hxfix⟩
  have hle := Subgroup.map_centralizer_le_centralizer_image
    (f₀.ι.range : Set (Γ₂ F)) (twistHom TwistTag.E6 F σ.toRingHom)
  have hcent : x ∈ Subgroup.centralizer
      (((f₀.ι.range).map (twistHom TwistTag.E6 F σ.toRingHom) : Subgroup (Γ₂ F)) :
        Set (Γ₂ F)) := by
    simpa only [Subgroup.coe_map] using hle hxmap
  have hsub : (f₅.ι.range : Set (Γ₂ F)) ⊆
      (((f₀.ι.range).map (twistHom TwistTag.E6 F σ.toRingHom) : Subgroup (Γ₂ F)) :
        Set (Γ₂ F)) := by
    rw [f₅.range_eq, f₀.range_eq, ← perm_image_zero, Subgroup.coe_map]
    exact TwFace.subsystemGroup_image_perm_le_map_twistHom σ ({0} : Set _)
  exact Subgroup.centralizer_le hsub hcent

private theorem card_le_three_of_centralizer_A1A2 {F : Type} [Field F] (σ : F ≃+* F)
    {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
      twistedE6DiagGL F σ)
    (hEel : IsElemAbelian 3 E) (f : TwFace.LeviFactor F 3 ({1, 3} : Set _))
    (f₀ : TwFace.LeviFactor F 2 ({0} : Set _)) (f₅ : TwFace.LeviFactor F 2 ({5} : Set _))
    (hc₁ : E ≤ Subgroup.centralizer (f.ι.range : Set (Γ₂ F)))
    (hc₂ : E ≤ Subgroup.centralizer (f₀.ι.range : Set (Γ₂ F)))
    (hc₃ : E ≤ Subgroup.centralizer (f₅.ι.range : Set (Γ₂ F))) :
    Nat.card E ≤ 3 := by
  refine TwFace.card_le_three_of_forall_rootDiagUnit (F := F) σ ?_ ?_ ?_
  · intro x hx
    obtain ⟨b, hb, hb1⟩ := TwFace.exists_rootDiagUnit_eq_of_mem_levi_sup_diag σ f f₀ f₅
      disjoint_13_0 disjoint_13_5 disjoint_0_5
      cartan_13_0 cartan_13_5 cartan_0_5
      orbitUnion_A1A2_13_0_5 (hE hx) (hc₁ hx) (hc₂ hx) (hc₃ hx)
    refine ⟨b, hb, ?_⟩
    intro i hi2 hi4
    exact hb1 i (by fin_cases i <;> simp_all <;> decide)
  · intro x hx
    exact levi_sup_diag_le_eqLocus σ twE6MaxA1A2 (hE hx)
  · intro x hx
    exact hEel.2 x hx

theorem card_le_pow_three_of_le_levi_sup_diag_A1A2 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {E : Subgroup (Γ₂ F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
      twistedE6DiagGL F σ)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 3 := by
  have hn : 1 ≤ n := one_le_of_card_sq hF
  haveI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hn hF
  have hrc : ringChar F ≠ 3 := by
    have hrc2 : ringChar F = 2 :=
      CharP.ringChar_of_prime_eq_zero Nat.prime_two (CharP.cast_eq_zero F 2)
    rw [hrc2]
    norm_num
  have h4 : 4 ≤ Nat.card F := four_le_card_of_card_sq hF
  obtain ⟨f, hf⟩ := TwFace.exists_leviFactor_sl3 (F := F)
    (i := (1 : Fin TwistTag.E6.tag.rank)) (j := (3 : Fin TwistTag.E6.tag.rank))
    (by decide) (by decide) (by decide)
    ⟨(2 : Fin TwistTag.E6.tag.rank), by decide⟩
  obtain ⟨f₀, _⟩ := TwFace.exists_leviFactor_sl2 (F := F) (0 : Fin TwistTag.E6.tag.rank)
  obtain ⟨f₅, _⟩ := TwFace.exists_leviFactor_sl2 (F := F) (5 : Fin TwistTag.E6.tag.rank)
  let E₁ : Subgroup (Γ₂ F) := E ⊓ Subgroup.centralizer (f.ι.range : Set (Γ₂ F))
  let E₂ : Subgroup (Γ₂ F) := E₁ ⊓ Subgroup.centralizer (f₀.ι.range : Set (Γ₂ F))
  have hE₁le : E₁ ≤ E := inf_le_left
  have hE₂le₁ : E₂ ≤ E₁ := inf_le_left
  have hE₁el : IsElemAbelian 3 E₁ := CFSG.Open.IsElemAbelian.mono hEel hE₁le
  have hE₂el : IsElemAbelian 3 E₂ := CFSG.Open.IsElemAbelian.mono hE₁el hE₂le₁
  have h1 : Nat.card E ≤ 3 * Nat.card E₁ := by
    simpa only [E₁] using
      card_le_three_mul_card_inf_centralizer_sl3_A1A2 hF σ hσ h3 hE hEel f hf
  have h2 : Nat.card E₁ ≤ 3 * Nat.card E₂ := by
    have hle : E₁ ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
        twistedE6DiagGL F σ := hE₁le.trans hE
    simpa only [E₂] using
      card_le_three_mul_card_inf_centralizer_sl2_A1A2 σ hle hE₁el f₀ hrc h4
  have h3 : Nat.card E₂ ≤ 3 := by
    have hle : E₂ ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
        twistedE6DiagGL F σ := hE₂le₁.trans (hE₁le.trans hE)
    exact card_le_three_of_centralizer_A1A2 σ hle hE₂el f f₀ f₅
      (fun x hx => (Subgroup.mem_inf.mp (hE₂le₁ hx)).2)
      (fun x hx => (Subgroup.mem_inf.mp hx).2)
      (inf_centralizer_sl2_le_centralizer_sl2_A1A2 σ (hE₁le.trans hE) f₀ f₅)
  calc Nat.card E ≤ 3 * Nat.card E₁ := h1
    _ ≤ 3 * (3 * Nat.card E₂) := Nat.mul_le_mul_left 3 h2
    _ ≤ 3 * (3 * 3) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 3 h3)
    _ = 3 ^ 3 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.T173O
