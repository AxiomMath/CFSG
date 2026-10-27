module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDefs
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsCentral
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
public import CFSG.LieType.HighestRoot.CentLinearModels
public import CFSG.LieType.HighestRoot.CentChevalleyModels
public import CFSG.LieType.HighestRoot.CentTrialityMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModel

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ClassicalInvolution.Generic CFSG.LieType.HighestRoot
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

theorem natCard_galoisField_three_one : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

theorem isClassicalMember3_of_sl2_three {K : Type} [Group K] {R : Subgroup K}
    (e : R ≃* SL(2, GaloisField 3 1))
    (hCN : Subgroup.centralizer ({((e.symm (-1) : R) : K)} : Set K) ≤
      Subgroup.normalizer (R : Set K)) :
    IsClassicalMember3 R ((e.symm (-1) : R) : K) := by
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [natCard_galoisField_three_one]; decide
  have hz2 : orderOf ((e.symm (-1) : R) : K) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mpr rfl
  have hRC : R ≤ Subgroup.centralizer ({((e.symm (-1) : R) : K)} : Set K) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (⟨r, hr⟩ : R) * e.symm (-1) = e.symm (-1) * ⟨r, hr⟩ := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mul_neg_one, neg_one_mul]
    exact congrArg Subtype.val h1
  obtain ⟨ε⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three natCard_galoisField_three_one
  let e' : R ≃* SL(2, ZMod 3) := e.trans ε
  have hO : classicalInvolutionOddCore R = ⊥ := by
    have h1 : (classicalInvolutionOddCore R).map e'.toMonoidHom =
        classicalInvolutionOddCore SL(2, ZMod 3) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e'
    rw [show classicalInvolutionOddCore SL(2, ZMod 3) = ⊥ from componentOddCore_sl2Three] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h1
  refine ⟨hz2, (e.symm (-1)).2, ?_, ⟨?_⟩⟩
  · exact isSubnormal_of_normal_subgroupOf hRC
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mpr hCN)
  · exact ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e'

theorem member3Three : Member3Three := by
  intro X _ _ _ t n ht hm
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hFT : IsFundTag t := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl | rfl, -⟩ <;> trivial
  have hne : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases ht with ⟨-, h | h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h | h, -⟩ <;> simp_all
  have hadm : StatedLieAdmissible t n 3 1 := by
    rcases hm with ⟨-, hc⟩ | ⟨rfl, -, he⟩ | ⟨rfl, -, hr⟩ | ⟨-, -, hs⟩
    · exact hc.1
    · exact he.1
    · exact hr.1
    · exact absurd hs.1 hp2
  obtain ⟨ψ, hψ, hker⟩ := Upgrade.lieModelCentralCover t n 3 1 hp hp2 hFT hadm X hm
  have : Finite (modelUniv t n 3 1 hp).K := ModelFacts.finite_modelUniv hp2 hp hFT hadm
  obtain ⟨γ, hγ, hCZ⟩ : ∃ γ, IsLongestRoot (modelUniv t n 3 1 hp).D γ ∧
      ∀ z ∈ rankOneGroup (modelUniv t n 3 1 hp).D γ, orderOf z = 2 →
        Subgroup.centralizer ({z} : Set (modelUniv t n 3 1 hp).K) ≤
          Subgroup.normalizer (rankOneGroup (modelUniv t n 3 1 hp).D γ : Set _) := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl | rfl, rfl⟩
    · obtain ⟨γ, hγR, hγl, hcc⟩ := highestRootCZ_modelUniv_PSL hp2 hadm
      exact ⟨γ, ⟨hγR, hγl⟩, fun z hz hz2 => (hcc z hz hz2).1⟩
    · obtain ⟨γ, hγR, hγl, hcc⟩ := highestRootCZ_modelUniv_PSU hp2 hadm
      exact ⟨γ, ⟨hγR, hγl⟩, fun z hz hz2 => (hcc z hz hz2).1⟩
    · obtain ⟨γ, hγR, hγl, hcc⟩ := highestRootCZ_modelUniv_PSp hp2 hadm
      exact ⟨γ, ⟨hγR, hγl⟩, fun z hz hz2 => (hcc z hz hz2).1⟩
    · obtain ⟨-, γ, hγR, hγl, hcc⟩ := g2InvolutionData_modelUniv 3 1 hp2
      exact ⟨γ, ⟨hγR, hγl⟩, fun z hz hz2 => (hcc z hz hz2).1⟩
    · obtain ⟨γ, hγR, hγl, hcc⟩ := highestRootCZ_modelUniv_trialityD4 3 1 0 hp2 le_rfl
      exact ⟨γ, ⟨hγR, hγl⟩, fun z hz hz2 => (hcc z hz hz2).1⟩
  obtain ⟨e⟩ := ComponentClassification.RankTwoOddLie.nonempty_rankOne_equiv hp2 hFT hadm hγ
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [natCard_galoisField_three_one]; decide
  have hz2 : orderOf ((e.symm (-1) : rankOneGroup (modelUniv t n 3 1 hp).D γ) :
      (modelUniv t n 3 1 hp).K) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mpr rfl
  have hmem := isClassicalMember3_of_sl2_three e (hCZ _ (e.symm (-1)).2 hz2)
  have hz1 : ψ ((e.symm (-1) : rankOneGroup (modelUniv t n 3 1 hp).D γ) :
      (modelUniv t n 3 1 hp).K) ≠ 1 := by
    intro h
    have hc := hker h
    have h1 := ModelFacts.fundNoncentral_generic 3 t n 1 hFT hadm hne
      (rankOneGroup (modelUniv t n 3 1 hp).D γ) ⟨1, γ, Or.inl hγ, (ModelFacts.map_conj_one _).symm⟩
      _ (e.symm (-1)).2 (fun y => by
        rw [← Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _)
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  exact ⟨_, _, IsClassicalMember3.map_central ψ hψ hker hmem hz1⟩

end CFSG.ClassicalInvolution.Q3.TA3
