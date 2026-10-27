module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2LinAlg
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open scoped MatrixGroups

theorem closure_centralizers_G2_of_normalizes (X : Type) [Field X] [Finite X] (r p : ℕ)
    [Fact r.Prime] [Fact p.Prime] [CharP X r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup .G2 X)] (E₁ : Subgroup (adjointGroup .G2 X))
    [IsElementaryAbelian p E₁] (hcard : Nat.card E₁ = p ^ 2) (y : adjointGroup .G2 X)
    (R : Subgroup (ModGL .G2 X)) (hRC : R ≤ adjointGroup .G2 X) (hRr : IsPGroup r R)
    (hR : R ≠ ⊥)
    (hAR : (E₁.map (adjointGroup .G2 X).subtype).map
        (MulAut.conj (y : ModGL .G2 X)).toMonoidHom ≤
      Subgroup.normalizer (R : Set (ModGL .G2 X))) :
    Subgroup.closure {k' : adjointGroup .G2 X | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤ := by
  classical
  let C : Subgroup (ModGL .G2 X) := adjointGroup .G2 X
  let A : Subgroup (ModGL .G2 X) := E₁.map C.subtype
  have hAC : A ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have : IsElementaryAbelian p A := IsElementaryAbelian.map _
  let A' : Subgroup (ModGL .G2 X) := A.map (MulAut.conj (y : ModGL .G2 X)).toMonoidHom
  have hA'C : A' ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem y.2 (hAC ha)) (inv_mem y.2)
  have : IsElementaryAbelian p A' := IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card A' := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (y : ModGL .G2 X)).injective,
      Subgroup.card_map_of_injective C.subtype_injective, hcard]
  have hmain := ordinary_root_invariant_prime_subgroup_centralizer_generation .G2 X r p hrp A'
    hA'C hcard' R hRC hRr hR hAR
  have hmain' : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), C ⊓ Subgroup.centralizer ({a} : Set (ModGL .G2 X))) =
      C :=
    le_antisymm (iSup₂_le fun a _ => iSup_le fun _ => inf_le_left)
      (le_iSup_inf_centralizer_of_map_conj y.2 hmain.ge)
  exact closure_centralizers_of_iSup_eq C E₁ hmain'

theorem g2_closure_centralizers_three_split (K : Type) [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) [IsSimpleGroup (adjointGroup .G2 K)]
    (E : Subgroup (adjointGroup .G2 K)) [hE : IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {k : adjointGroup .G2 K | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set r := ringChar K with hr_def
  have hrK : CharP K r := ringChar.charP K
  obtain ⟨n, hr, hrn⟩ := FiniteField.card K r
  have : Fact r.Prime := ⟨hr⟩
  have hrn' : Nat.card K = r ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hrn
  have hr3 : r ≠ 3 := by
    rintro h
    have hq : 3 ∣ Nat.card K := by
      rw [hrn', h]
      exact dvd_pow_self 3 n.ne_zero
    have h1 : 3 ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hq h3
    rw [Nat.sub_sub_self (Nat.card_pos (α := K))] at h1
    omega
  obtain ⟨ω, hω1, hω3⟩ : ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 := by
    have h3' : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      exact h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3'
    refine ⟨(x : K), ?_, ?_⟩
    · intro h
      have : x = 1 := Units.ext h
      rw [this, orderOf_one] at hx
      omega
    · have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Units.val this |>.trans (by simp)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h0 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hω1)
  obtain ⟨ι, hι, -⟩ := exists_a2Hom_injective (K := K)
  have hEp : IsPGroup 3 E := IsElementaryAbelian.isPGroup 3 E
  obtain ⟨y, hy⟩ := exists_conj_le_range_of_three_dvd_sub_one h3 ι hι E hEp
  set Et : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
    (E.map (MulAut.conj y).toMonoidHom).comap ι with hEt
  have hmemEt : ∀ x, x ∈ Et ↔ ι x ∈ E.map (MulAut.conj y).toMonoidHom := fun x => Iff.rfl
  have hE3 : ∀ x ∈ Et, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := (hmemEt x).1 hx
    apply hι
    rw [map_pow, map_one, ← hxe]
    have h3e : e ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := E) (p := 3) e he
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, h3e, map_one]
  have hEcomm : ∀ x ∈ Et, ∀ x' ∈ Et, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨e, he, hxe⟩ := (hmemEt x).1 hx
    obtain ⟨e', he', hxe'⟩ := (hmemEt x').1 hx'
    apply hι
    rw [map_mul, map_mul, ← hxe, ← hxe']
    have hcomm : e * e' = e' * e := by
      have := hE.is_comm.comm (⟨e, he⟩ : E) ⟨e', he'⟩
      exact congrArg Subtype.val this
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hcomm]
  obtain ⟨R, hRr, hR1, hRn⟩ := exists_pGroup_normalized_of_commuting_cube_one r ω hω Et hE3 hEcomm
  let ιM : Matrix.SpecialLinearGroup (Fin 3) K →* ModGL .G2 K :=
    (adjointGroup .G2 K).subtype.comp ι
  have hιM : Function.Injective ιM := Subtype.val_injective.comp hι
  have hRC : R.map ιM ≤ adjointGroup .G2 K := by
    rintro _ ⟨x, -, rfl⟩
    exact (ι x).2
  have hRr' : IsPGroup r (R.map ιM) :=
    hRr.of_surjective (ιM.subgroupMap R) (ιM.subgroupMap_surjective R)
  have hR' : R.map ιM ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R hιM).1 h)
  have hAR : (E.map (adjointGroup .G2 K).subtype).map
      (MulAut.conj (y : ModGL .G2 K)).toMonoidHom ≤
        Subgroup.normalizer ((R.map ιM : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    obtain ⟨x, hx⟩ := hy ⟨e, he, rfl⟩
    have hxEt : x ∈ Et := by
      rw [hmemEt]
      exact ⟨e, he, hx.symm⟩
    have hval : (MulAut.conj (y : ModGL .G2 K)).toMonoidHom ((adjointGroup .G2 K).subtype e) =
        ιM x := by
      have := congrArg Subtype.val hx
      simpa [ιM] using this.symm
    rw [hval, Subgroup.mem_normalizer_iff]
    intro ρ
    constructor
    · rintro ⟨r0, hr0, rfl⟩
      refine ⟨x * r0 * x⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.1 (hRn hxEt) r0).1 hr0
    · rintro ⟨r1, hr1, h1⟩
      refine ⟨x⁻¹ * r1 * x, ?_, ?_⟩
      · have h2 := (Subgroup.mem_normalizer_iff.1 (hRn (inv_mem hxEt)) r1).1 hr1
        rwa [inv_inv] at h2
      · simp only [map_mul, map_inv, h1]
        group
  exact closure_centralizers_G2_of_normalizes K r 3 hr3 E hcard y (R.map ιM) hRC hRr' hR' hAR

end CFSG.GH74.GLS.Stage2.Bender.Thm1
