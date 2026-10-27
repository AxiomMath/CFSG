module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKDiagDef
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidWeights
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Triality
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Center
public import CFSG.ClassicalInvolution.RouteD.GapsFrLie
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.LieType.SeitzGeneration.RootPairSL2
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.D4Rigid
  CFSG.ClassicalInvolution.G2D4Models.Twin

local notation "𝔽₃" => GaloisField 3 1

private lemma fk_diag_vec (d : Fin 4 ⊕ Fin 4 → 𝔽₃ˣ) (m : Fin 4) (s : Bool) :
    fkDiag d ((fr 𝔽₃).vec m s) = (d (idx m s) : 𝔽₃) • (fr 𝔽₃).vec m s := by
  funext ν
  rw [fkDiag_apply, Pi.smul_apply, vec_eq, Pi.single_apply]
  by_cases h : ν = idx m s
  · subst h; simp
  · simp [h]

private lemma fk_diag_smul_vec (d : Fin 4 ⊕ Fin 4 → 𝔽₃ˣ) (m : Fin 4) (s : Bool) (c : 𝔽₃) :
    fkDiag d (c • (fr 𝔽₃).vec m s) = (c * d (idx m s) : 𝔽₃) • (fr 𝔽₃).vec m s := by
  rw [map_smul, fk_diag_vec, smul_smul]

private lemma fk_diag_conj_longRoot (d : Fin 4 ⊕ Fin 4 → 𝔽₃ˣ) (μ : 𝔽₃)
    (hμ : ∀ m : Fin 4, (d (.inl m) : 𝔽₃) * d (.inr m) = μ)
    {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : 𝔽₃) :
    fkDiag d * spinAction (quadPlus 4 𝔽₃) ((fr 𝔽₃).longRoot hij s t (.ofAdd c)) *
        (fkDiag d)⁻¹ =
      spinAction (quadPlus 4 𝔽₃) ((fr 𝔽₃).longRoot hij s t
        (.ofAdd ((d (idx i s) : 𝔽₃) * d (idx j t) / μ * c))) := by
  have hμ0 : μ ≠ 0 := by
    rw [← hμ 0]
    exact mul_ne_zero (d (.inl 0)).ne_zero (d (.inr 0)).ne_zero
  have hQ : ∀ v, quadPlus 4 𝔽₃ (fkDiag d v) = μ * quadPlus 4 𝔽₃ v :=
    quadPlus_fkDiag d μ hμ
  rw [(fr 𝔽₃).spinAction_longRoot_eq_eichler hij s t c,
    (fr 𝔽₃).spinAction_longRoot_eq_eichler hij s t
      ((d (idx i s) : 𝔽₃) * d (idx j t) / μ * c),
    CFSG.LieType.SeitzGeneration.RootPairOrth.eichler_conj_similarity hμ0 hQ
      ((fr 𝔽₃).vec j t) (c • (fr 𝔽₃).vec i s),
    fk_diag_vec, fk_diag_smul_vec,
    CFSG.ClassicalGroups.Orthogonal.eichler_smul_left, smul_smul, smul_smul]
  have hc : ((d (idx j t) : 𝔽₃) * μ⁻¹) * (c * (d (idx i s) : 𝔽₃)) =
      (d (idx i s) : 𝔽₃) * d (idx j t) / μ * c := by
    rw [div_eq_mul_inv]; ring
  rw [hc]

private lemma fk_longRoot_pow_three {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : 𝔽₃) :
    ((fr 𝔽₃).longRoot hij s t (.ofAdd c)) ^ 3 = 1 := by
  have h3 : ((3 : ℕ) : 𝔽₃) = 0 := CharP.cast_eq_zero 𝔽₃ 3
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, h3, zero_mul, ofAdd_zero, map_one]

theorem fk_diag_longRoot (κ : MulAut (spinGroup (quadPlus 4 (GaloisField 3 1))))
    (d : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ) (μ : GaloisField 3 1)
    (hμ : ∀ m : Fin 4, (d (.inl m) : GaloisField 3 1) * d (.inr m) = μ)
    (hκ : ∀ x, spinAction (quadPlus 4 (GaloisField 3 1)) (κ x) =
      fkDiag d * spinAction (quadPlus 4 (GaloisField 3 1)) x * (fkDiag d)⁻¹)
    {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : GaloisField 3 1) :
    κ ((fr (GaloisField 3 1)).longRoot hij s t (.ofAdd c)) =
      (fr (GaloisField 3 1)).longRoot hij s t
        (.ofAdd ((d (idx i s) : GaloisField 3 1) * d (idx j t) / μ * c)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_of_charP (p := 3) (by norm_num)
  have hact : spinAction (quadPlus 4 𝔽₃) (κ ((fr 𝔽₃).longRoot hij s t (.ofAdd c))) =
      spinAction (quadPlus 4 𝔽₃) ((fr 𝔽₃).longRoot hij s t
        (.ofAdd ((d (idx i s) : 𝔽₃) * d (idx j t) / μ * c))) := by
    rw [hκ ((fr 𝔽₃).longRoot hij s t (.ofAdd c))]
    exact fk_diag_conj_longRoot d μ hμ hij s t c
  have hκ3 : (κ ((fr 𝔽₃).longRoot hij s t (.ofAdd c))) ^ 3 = 1 := by
    rw [← map_pow, fk_longRoot_pow_three hij s t c, map_one]
  exact eq_of_spinAction_eq_of_pow (n := 4) (p := 3) (by norm_num) h2 hact hκ3
    (fk_longRoot_pow_three hij s t ((d (idx i s) : 𝔽₃) * d (idx j t) / μ * c))

private lemma fk_root_map (κ : MulAut (spinGroup (quadPlus 4 𝔽₃)))
    (d : Fin 4 ⊕ Fin 4 → 𝔽₃ˣ) (μ : 𝔽₃)
    (hμ : ∀ m : Fin 4, (d (.inl m) : 𝔽₃) * d (.inr m) = μ)
    (hκ : ∀ x, spinAction (quadPlus 4 𝔽₃) (κ x) =
      fkDiag d * spinAction (quadPlus 4 𝔽₃) x * (fkDiag d)⁻¹)
    {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    ((fr 𝔽₃).longRoot hij s t).range.map κ.toMonoidHom =
      ((fr 𝔽₃).longRoot hij s t).range := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨m, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : 𝔽₃, m = Multiplicative.ofAdd a := ⟨m.toAdd, rfl⟩
    rw [ha]
    change κ ((fr 𝔽₃).longRoot hij s t (Multiplicative.ofAdd a)) ∈
      ((fr 𝔽₃).longRoot hij s t).range
    rw [fk_diag_longRoot κ d μ hμ hκ hij s t a]
    exact ⟨Multiplicative.ofAdd ((d (idx i s) : 𝔽₃) * d (idx j t) / μ * a), rfl⟩
  · rintro _ ⟨m, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : 𝔽₃, m = Multiplicative.ofAdd a := ⟨m.toAdd, rfl⟩
    rw [ha]
    have hμ0 : μ ≠ 0 := by
      rw [← hμ 0]
      exact mul_ne_zero (d (.inl 0)).ne_zero (d (.inr 0)).ne_zero
    have hs : (d (idx i s) : 𝔽₃) * d (idx j t) / μ ≠ 0 :=
      div_ne_zero (mul_ne_zero (d (idx i s)).ne_zero (d (idx j t)).ne_zero) hμ0
    refine ⟨(fr 𝔽₃).longRoot hij s t
      (.ofAdd (a / ((d (idx i s) : 𝔽₃) * d (idx j t) / μ))), ⟨_, rfl⟩, ?_⟩
    change κ ((fr 𝔽₃).longRoot hij s t
        (Multiplicative.ofAdd (a / ((d (idx i s) : 𝔽₃) * d (idx j t) / μ)))) =
      ((fr 𝔽₃).longRoot hij s t) (Multiplicative.ofAdd a)
    rw [fk_diag_longRoot κ d μ hμ hκ hij s t
        (a / ((d (idx i s) : 𝔽₃) * d (idx j t) / μ)),
      mul_div_cancel₀ a hs]

theorem fk_diag_map_node (κ : MulAut (spinGroup (quadPlus 4 (GaloisField 3 1))))
    (d : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ) (μ : GaloisField 3 1)
    (hμ : ∀ m : Fin 4, (d (.inl m) : GaloisField 3 1) * d (.inr m) = μ)
    (hκ : ∀ x, spinAction (quadPlus 4 (GaloisField 3 1)) (κ x) =
      fkDiag d * spinAction (quadPlus 4 (GaloisField 3 1)) x * (fkDiag d)⁻¹)
    {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    ((fr (GaloisField 3 1)).longSL2 hij s t).range.map κ.toMonoidHom =
      ((fr (GaloisField 3 1)).longSL2 hij s t).range := by
  rw [CFSG.ClassicalInvolution.RouteD.Gaps.longSL2_range_eq_sup (fr 𝔽₃) hij s t,
    Subgroup.map_sup, fk_root_map κ d μ hμ hκ hij s t,
    fk_root_map (i := j) (j := i) κ d μ hμ hκ hij.symm (!t) (!s)]

theorem fk_diag_fix_z (κ : MulAut (spinGroup (quadPlus 4 (GaloisField 3 1))))
    (d : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ) (μ : GaloisField 3 1)
    (hμ : ∀ m : Fin 4, (d (.inl m) : GaloisField 3 1) * d (.inr m) = μ)
    (hκ : ∀ x, spinAction (quadPlus 4 (GaloisField 3 1)) (κ x) =
      fkDiag d * spinAction (quadPlus 4 (GaloisField 3 1)) x * (fkDiag d)⁻¹) :
    κ (z0 (GaloisField 3 1)) = z0 (GaloisField 3 1) ∧
      κ (z2 (GaloisField 3 1)) = z2 (GaloisField 3 1) ∧
      κ (z3 (GaloisField 3 1)) = z3 (GaloisField 3 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_of_charP (p := 3) (by norm_num)
  have hfix : ∀ {i j : Fin 4} (hij : i ≠ j) (s t : Bool),
      κ ((fr 𝔽₃).longSL2 hij s t (-1)) = (fr 𝔽₃).longSL2 hij s t (-1) := by
    intro i j hij s t
    have hmem : κ ((fr 𝔽₃).longSL2 hij s t (-1)) ∈ ((fr 𝔽₃).longSL2 hij s t).range := by
      rw [← fk_diag_map_node κ d μ hμ hκ hij s t]
      exact ⟨(fr 𝔽₃).longSL2 hij s t (-1), ⟨-1, rfl⟩, rfl⟩
    have hord : orderOf (κ ((fr 𝔽₃).longSL2 hij s t (-1))) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact CFSG.LieType.HighestRoot.orderOf_longSL2_neg_one (fr 𝔽₃) hij s t h2
    exact CFSG.LieType.HighestRoot.eq_of_mem_range_longSL2_of_orderOf_eq_two (fr 𝔽₃) hij s t h2
      hmem hord
  exact ⟨hfix ne01 true false, hfix ne23 true false, hfix ne23 true true⟩

end CFSG.OddStandard.SmallF3.Omega
