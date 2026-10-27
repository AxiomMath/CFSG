module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOIdent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRecog
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ClassicalGroups
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOType
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.Sporadic.Schreier.TitsOther
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

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL isoOrthGL transportGL
  trans_commutator)
open CFSG.GroupTheory.WeirSylow (IsPlusType natCard_orthogonalGroup_odd
  natCard_orthogonalGroup_of_type)

theorem prime_ne_two_and_one_le {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {p f₀ : ℕ} (hp : p.Prime) (hKc : Nat.card K = p ^ f₀) : p ≠ 2 ∧ 1 ≤ f₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := f₀) (by rw [← Nat.card_eq_fintype_card]; exact hKc)
  refine ⟨fun h => hK (by rw [ringChar.eq K p, h]), ?_⟩
  by_contra h0
  have h1 : Nat.card K = 1 := by rw [hKc, show f₀ = 0 by omega, pow_zero]
  have := Finite.one_lt_card (α := K)
  omega

theorem factorization_eq_of_cast_eq {p f₀ : ℕ} (hp : p.Prime) {N a m : ℕ} {u q c : ℤ}
    (hq : q = (p : ℤ) ^ f₀) (hu : ¬ (p : ℤ) ∣ u) (hc : (p : ℤ) ∣ c)
    (hN : (N : ℤ) = u * q ^ a * ∏ i ∈ Finset.Icc 1 m, (c ^ i - 1)) :
    N.factorization p = f₀ * a := by
  have : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hfac : ∀ i ∈ Finset.Icc 1 m, ¬ (p : ℤ) ∣ c ^ i - 1 := by
    intro i hi h
    have hci : (p : ℤ) ∣ c ^ i := dvd_pow hc (by have := (Finset.mem_Icc.1 hi).1; omega)
    have h1 : (p : ℤ) ∣ c ^ i - (c ^ i - 1) := dvd_sub hci h
    rw [sub_sub_cancel] at h1
    exact hpZ.not_dvd_one h1
  have hX : ¬ (p : ℤ) ∣ ∏ i ∈ Finset.Icc 1 m, (c ^ i - 1) := fun h => by
    obtain ⟨i, hi, hdvd⟩ := hpZ.exists_mem_finset_dvd h
    exact hfac i hi hdvd
  have hu0 : u ≠ 0 := fun h => hu (h ▸ dvd_zero _)
  have hX0 : ∏ i ∈ Finset.Icc 1 m, (c ^ i - 1) ≠ 0 := fun h => hX (h ▸ dvd_zero _)
  have hpa : q ^ a = ((p ^ (f₀ * a) : ℕ) : ℤ) := by rw [hq, ← pow_mul, Nat.cast_pow]
  have hpa0 : q ^ a ≠ 0 := by
    rw [hpa]
    exact_mod_cast (pow_pos hp.pos _).ne'
  rw [Nat.factorization_def _ hp, ← padicValInt.of_nat, hN,
    padicValInt.mul (mul_ne_zero hu0 hpa0) hX0, padicValInt.mul hu0 hpa0,
    padicValInt.eq_zero_of_not_dvd hu, padicValInt.eq_zero_of_not_dvd hX, zero_add, add_zero, hpa,
    padicValInt.of_nat, padicValNat.prime_pow]

theorem factorization_card_orthogonalGroup {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hK : ringChar K ≠ 2) {p f₀ : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f₀) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hk : 1 ≤ Module.finrank K V) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
      f₀ * ((Module.finrank K V - 1) ^ 2 / 4) := by
  obtain ⟨hp2', hf₀⟩ := prime_ne_two_and_one_le hK hp hKc
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hq : (Nat.card K : ℤ) = (p : ℤ) ^ f₀ := by rw [hKc, Nat.cast_pow]
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) := by
    rw [hq]
    exact dvd_pow_self _ (by omega)
  have hpq2 : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 := dvd_pow hpq (by norm_num)
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
    have := hp.two_le
    omega
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' (Module.finrank K V)
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hdim : Module.finrank K V = 2 * (m + 1) := hn
    have hk' : (Module.finrank K V - 1) ^ 2 / 4 = m * (m + 1) := by
      rw [hdim, show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
        show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]
      omega
    rw [hk']
    have key : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
        (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
          2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - ε) *
            ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) →
        (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
          f₀ * (m * (m + 1)) := by
      intro ε hε hcard
      refine factorization_eq_of_cast_eq hp (m := m)
        (u := 2 * ((Nat.card K : ℤ) ^ (m + 1) - ε)) hq ?_ hpq2 (by rw [hcard]; ring)
      intro h
      rcases hpZ.dvd_or_dvd h with h | h
      · exact hp2 h
      · have hpm : (p : ℤ) ∣ (Nat.card K : ℤ) ^ (m + 1) := dvd_pow hpq (by omega)
        have h1 := dvd_sub hpm h
        rw [sub_sub_cancel] at h1
        rcases hε with rfl | rfl
        · exact hpZ.not_dvd_one h1
        · exact hpZ.not_dvd_one (dvd_neg.1 h1)
    by_cases hplus : IsPlusType Q
    · exact key 1 (Or.inl rfl) (natCard_orthogonalGroup_of_type hQ hdim (Or.inl ⟨rfl, hplus⟩))
    · exact key (-1) (Or.inr rfl)
        (natCard_orthogonalGroup_of_type hQ hdim (Or.inr ⟨rfl, hplus⟩))
  ·
    have hk' : (Module.finrank K V - 1) ^ 2 / 4 = n ^ 2 := by
      rw [hn, show 2 * n + 1 - 1 = 2 * n by omega, show (2 * n) ^ 2 = 4 * n ^ 2 by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hk']
    exact factorization_eq_of_cast_eq hp (u := 2) hq hp2 hpq2
      (natCard_orthogonalGroup_odd hK hQ hn)

theorem factorization_two_pow_mul {p : ℕ} (hp2 : p ≠ 2) (a N : ℕ) (hN : N ≠ 0) :
    (2 ^ a * N).factorization p = N.factorization p := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hN, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two,
    Finsupp.single_apply, ite_eq_right (Ne.symm hp2), smul_zero, zero_add]

theorem factorization_four_mul {p : ℕ} (hp2 : p ≠ 2) {N : ℕ} (hN : N ≠ 0) :
    (4 * N).factorization p = N.factorization p :=
  factorization_two_pow_mul hp2 2 N hN

theorem card_orthogonalGroup_eq_four_mul {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hK : ringChar K ≠ 2) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h7 : 7 ≤ Module.finrank K V) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      4 * Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Odd (Nat.card K) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨T, hT, hTQ⟩ : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
    by_contra hno
    have := CatalogueBOrthogonalAssembly.low_Witt_finrank_cases hodd Q hQ (by omega) hno
    omega
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ :=
    ClassicalGroups.Orthogonal.exists_three_hypPairs hQ hT.ge hTQ
  obtain ⟨hcard, -⟩ := ClassicalInvolution.orthogonalGroup_index_four hQ h12 h13 h23
  have hΩ :=
    ClassicalGroups.Orthogonal.commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero
      h2 hQ h12 h13 h23
  rw [hcard, ← hΩ, ← Subgroup.map_subtype_commutator,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

theorem card_blockP_eq {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {d : ℕ}
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {C : Finset (Fin d)} (hCc : Cᶜ.Nonempty) :
    Nat.card (blockP K hw C) = Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw C))))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨e⟩ := nonempty_projBlock_equiv hw h2 hCc (le_refl (omegaI hw C))
  rw [← blockP_eq_projBlock] at e
  rw [Nat.card_congr e.toEquiv]
  have hR : ((diagGL (wRes_ne_zero hw C) : GL (Fin C.card) K) :
      Matrix (Fin C.card) (Fin C.card) K)ᵀ = diagGL (wRes_ne_zero hw C) := by
    rw [coe_diagGL]
    exact diagonal_transpose _
  change Nat.card (⁅CatalogueBGraphForm.isometryGroup C.card K (diagGL (wRes_ne_zero hw C)),
    CatalogueBGraphForm.isometryGroup C.card K (diagGL (wRes_ne_zero hw C))⁆ :
      Subgroup (GL (Fin C.card) K)) = _
  rw [← trans_commutator (isoOrthGL hK _ hR), transportGL,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    Subgroup.card_map_of_injective (isoOrthGL hK _ hR).injective]

theorem pPrimeCore_blockP_eq_bot {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {d : ℕ}
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {C : Finset (Fin d)} (hCc : Cᶜ.Nonempty)
    (hNF : BlockNF w C) (hq : IsQuasisimple (blockP K hw C))
    (hnt : Nontrivial (↥(blockP K hw C) ⧸ pPrimeCore 2 ↥(blockP K hw C))) :
    pPrimeCore 2 ↥(blockP K hw C) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : pPrimeCore 2 ↥(blockP K hw C) ≠ ⊤ := fun h => by
    have : Subsingleton (↥(blockP K hw C) ⧸ pPrimeCore 2 ↥(blockP K hw C)) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact false_of_nontrivial_of_subsingleton (↥(blockP K hw C) ⧸ pPrimeCore 2 ↥(blockP K hw C))
  have hle : pPrimeCore 2 ↥(blockP K hw C) ≤ center ↥(blockP K hw C) :=
    (LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq _).resolve_right hne
  refine eq_bot_iff.2 fun z hz => ?_
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_center_blockP hw hK hCc hNF (hle hz)
  have hcop := LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore (p := 2) hz
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  rw [mem_bot]
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm h2)

theorem three_le_card_of_not_isSolvable_blockP {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {C : Finset (Fin d)}
    (hCc : Cᶜ.Nonempty) (hns : ¬ Group.IsSolvable (blockP K hw C)) : 3 ≤ C.card := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  by_contra h3
  obtain ⟨e⟩ := nonempty_projBlock_equiv hw h2 hCc (le_refl (omegaI hw C))
  rw [← blockP_eq_projBlock] at e
  have := isSolvable_omegaR_of_le_two (by omega : C.card ≤ 2) (wRes_ne_zero hw C)
  exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

theorem finite_linearEquiv (K : Type) [Field K] [Finite K] (n : ℕ) :
    Finite ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  Finite.of_injective (fun e : (Fin n → K) ≃ₗ[K] (Fin n → K) => (e : (Fin n → K) → Fin n → K))
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem false_of_psp_le_blockP {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {p f₀ f : ℕ} (hp : p.Prime) (hKc : Nat.card K = p ^ f₀) (hf : f = 2 * f₀) {d : ℕ}
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {C : Finset (Fin d)} (hCc : Cᶜ.Nonempty)
    (hNF : 3 ≤ C.card → BlockNF w C)
    {L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} (hLC : L ≤ blockP K hw C)
    (hL : IsPComponent 2 (L.subgroupOf (blockP K hw C)))
    (hLm : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_linearEquiv K C.card
  obtain ⟨hp2, hf₀⟩ := prime_ne_two_and_one_le hK hp hKc
  have hfacX := (CatLeafProof.X10Lin.lieOrder_of_lieModel_classical
    (Or.inr (Or.inr (Or.inl rfl))) hp2 (by norm_num) hLm).2
  have hS : CatLeaf.lieSylowExponent .PSp 2 = 4 := rfl
  rw [hS] at hfacX
  have hR : ((diagGL (wRes_ne_zero hw C) : GL (Fin C.card) K) :
      Matrix (Fin C.card) (Fin C.card) K)ᵀ = diagGL (wRes_ne_zero hw C) := by
    rw [coe_diagGL]
    exact diagonal_transpose _
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK _ hR
  have hdim : Module.finrank K (Fin C.card → K) = C.card := Module.finrank_fin_fun K
  have hcardP := card_blockP_eq hK hw hCc
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw C)) with hQdef
  have hns : ¬ Group.IsSolvable (blockP K hw C) := fun hsol =>
    not_le_of_isSolvable hLC hL hsol hLC
  have hk3 := three_le_card_of_not_isSolvable_blockP hK hw hCc hns
  have hdvd : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    refine ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hLC)).trans ?_
    rw [hcardP]
    exact Subgroup.card_subgroup_dvd_card _
  have hfacO := factorization_card_orthogonalGroup hK hp hKc hQnd (by rw [hdim]; omega)
  rw [hdim] at hfacO
  have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p
  rw [hfacX, hfacO, hf] at hle
  have hN8 : 8 ≤ (C.card - 1) ^ 2 / 4 := by
    have h1 : f₀ * 8 ≤ f₀ * ((C.card - 1) ^ 2 / 4) := by linarith
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hk7 : 7 ≤ C.card := by
    by_contra h7
    have : (C.card - 1) ^ 2 ≤ 25 := by
      calc (C.card - 1) ^ 2 ≤ 5 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 25 := by norm_num
    omega
  have hq : IsQuasisimple (blockP K hw C) := by
    rcases blockP_cases hw hK C hCc with hsol | hq | ⟨h4, -⟩
    · exact absurd hsol hns
    · exact hq
    · omega
  obtain rfl : L = blockP K hw C := eq_of_le_of_isQuasisimple hLC le_rfl hL hq
  have hs : IsSimpleGroup (↥(blockP K hw C) ⧸ pPrimeCore 2 ↥(blockP K hw C)) := by
    rcases hLm with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 p f h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hO := pPrimeCore_blockP_eq_bot hK hw hCc (hNF hk3) hq hs.toNontrivial
  have h4' := card_orthogonalGroup_eq_four_mul hK hQnd (by rw [hdim]; exact hk7)
  have hX : Nat.card (↥(blockP K hw C) ⧸ pPrimeCore 2 ↥(blockP K hw C)) =
      Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hO).trans
      QuotientGroup.quotientBot).toEquiv, hcardP]
  rw [h4', factorization_four_mul hp2 Nat.card_pos.ne'] at hfacO
  rw [hX, hfacO, hf] at hfacX
  have hN : (C.card - 1) ^ 2 / 4 = 8 := by
    have h1 : f₀ * ((C.card - 1) ^ 2 / 4) = f₀ * 8 := by linarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  rcases Nat.lt_or_ge (C.card - 1) 6 with h6 | h6
  · have : (C.card - 1) ^ 2 ≤ 25 := by
      calc (C.card - 1) ^ 2 ≤ 5 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 25 := by norm_num
    omega
  · have : 36 ≤ (C.card - 1) ^ 2 := by
      calc 36 = 6 ^ 2 := by norm_num
        _ ≤ (C.card - 1) ^ 2 := Nat.pow_le_pow_left h6 2
    omega

theorem eq_two_mul_of_blockP_four {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {p f₀ f : ℕ} (hp : p.Prime) (hKc : Nat.card K = p ^ f₀) {d : ℕ} {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty) (hI4 : I.card = 4)
    (hNF : BlockNF w I) (hq : IsQuasisimple (blockP K hw I))
    (hm : Blueprint.LieModel (↥(blockP K hw I) ⧸ pPrimeCore 2 ↥(blockP K hw I)) .PSL 2 p f) :
    f = 2 * f₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_linearEquiv K I.card
  obtain ⟨hp2, hf₀⟩ := prime_ne_two_and_one_le hK hp hKc
  have hadm : 1 ≤ f ∧ p ^ f ≠ 3 := by
    rcases hm with ⟨-, ⟨-, hf1, -, -, h23⟩, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact ⟨hf1, fun h => h23 (by rw [h])⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hs : IsSimpleGroup (↥(blockP K hw I) ⧸ pPrimeCore 2 ↥(blockP K hw I)) := by
    rcases hm with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact (LieType.Simplicity.fam_PSL_simplicity _ 2 p f h).2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hO := pPrimeCore_blockP_eq_bot hK hw hIc hNF hq hs.toNontrivial
  have hfacX := (CatLeafProof.X10Lin.lieOrder_of_lieModel_classical (Or.inl rfl) hp2
    (by norm_num) hm).2
  have hS : CatLeaf.lieSylowExponent .PSL 2 = 1 := rfl
  rw [hS, one_mul, Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hO).trans
    QuotientGroup.quotientBot).toEquiv, card_blockP_eq hK hw hIc] at hfacX
  have hR : ((diagGL (wRes_ne_zero hw I) : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K)ᵀ = diagGL (wRes_ne_zero hw I) := by
    rw [coe_diagGL]
    exact diagonal_transpose _
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK _ hR
  have hdim : Module.finrank K (Fin I.card → K) = 4 := by rw [Module.finrank_fin_fun, hI4]
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I)) with hQdef
  have hfacO := factorization_card_orthogonalGroup hK hp hKc hQnd (by rw [hdim]; omega)
  rw [hdim, show (4 - 1) ^ 2 / 4 = 2 by norm_num] at hfacO
  have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (Subgroup.card_subgroup_dvd_card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) p
  rw [hfacX, hfacO] at hle
  have hodd : Odd (Nat.card K) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  obtain ⟨-, hnexc, -⟩ :=
    LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage Q
      hQnd (Or.inl ⟨hodd, Or.inr (Or.inl hdim)⟩)
  by_cases hE : (Module.finrank K (Fin I.card → K) = 3 ∧ Nat.card K = 3) ∨
      ((Module.finrank K (Fin I.card → K) = 4 ∧
        ∃ S : Submodule K (Fin I.card → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
        (Nat.card K = 2 ∨ Nat.card K = 3))
  ·
    have hK3 : Nat.card K = 3 := by
      rcases hE with ⟨h3, -⟩ | ⟨-, h2 | h3⟩
      · rw [hdim] at h3
        omega
      · rw [h2] at hodd
        exact absurd hodd (by decide)
      · exact h3
    have hp3 : p = 3 := by
      have hdvd : p ∣ 3 := by
        rw [← hK3, hKc]
        exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
    subst hp3
    have hf₀1 : f₀ = 1 := by
      have h33 : 3 ^ f₀ = 3 ^ 1 := by rw [← hKc, hK3, pow_one]
      exact Nat.pow_right_injective (by norm_num) h33
    obtain ⟨hf1, hf3⟩ := hadm
    have hf1' : f ≠ 1 := fun h => hf3 (by rw [h, pow_one])
    rw [hf₀1] at hle ⊢
    omega
  ·
    obtain ⟨-, hP2, -⟩ := hnexc hE
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP2
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))
    rw [ha] at hcard
    rw [hcard, factorization_two_pow_mul hp2 a _ Nat.card_pos.ne', hfacX] at hfacO
    omega

end CFSG.ComponentClassification.GSThmB.QPUCl
