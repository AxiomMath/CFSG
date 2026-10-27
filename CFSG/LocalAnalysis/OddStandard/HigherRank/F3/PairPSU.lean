module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockSU
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockEquiv

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Block

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def negOneSUFour : Su K p f 4 :=
  ⟨-1, by
    refine ⟨?_, ?_⟩
    · simp [Matrix.det_neg, show ((-1 : K) ^ 4 = 1) by norm_num]
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [conjTr]⟩

variable {K p f}

theorem suMat_negOneSUFour : suMat (negOneSUFour K p f) = -1 := by
  simp [negOneSUFour, suMat]

theorem negOneSUFour_mul_self : negOneSUFour K p f * negOneSUFour K p f = 1 :=
  suMat_injective (by simp [suMat_negOneSUFour])

theorem negOneSUFour_comm (A : Su K p f 4) :
    A * negOneSUFour K p f = negOneSUFour K p f * A :=
  suMat_injective (by simp [suMat_negOneSUFour])

theorem negOneSUFour_mem_center : negOneSUFour K p f ∈ center (Su K p f 4) :=
  Subgroup.mem_center_iff.mpr negOneSUFour_comm

theorem negOneSUFour_ne_one (h2 : (2 : K) ≠ 0) : negOneSUFour K p f ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg suMat h) 0) 0
  rw [suMat_negOneSUFour, suMat_one] at this
  exact neg_one_ne_one_of_two_ne_zero h2 (by simpa using this)

theorem orderOf_negOneSUFour (h2 : (2 : K) ≠ 0) : orderOf (negOneSUFour K p f) = 2 :=
  orderOf_eq_prime (by rw [pow_two, negOneSUFour_mul_self]) (negOneSUFour_ne_one h2)

theorem normal_blockEmb_four (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 4 ≤ n) :
    ((blockEmb K p f n 4 0 (by omega)).range.subgroupOf
      (centralizer ({blockEmb K p f n 4 0 (by omega) (negOneSUFour K p f)} :
        Set (Su K p f n)))).Normal := by
  set D : Matrix (Fin n) (Fin n) K := negBlockK K n 0 4 with hD
  have hrange : (blockEmb K p f n 4 0 (by omega)).range = longRootGroupSU K p f D := by
    rw [hD]
    exact range_blockEmb_eq_longRootGroupSU_gen h2 (by omega)
  have hsD : suMat (blockEmb K p f n 4 0 (by omega) (negOneSUFour K p f)) = D := by
    rw [suMat_blockEmb, suMat_negOneSUFour]
    rfl
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [hrange] at hx ⊢
  have hcomm : suMat (g : Su K p f n) * D = D * suMat (g : Su K p f n) := by
    have hg := Subgroup.mem_centralizer_singleton_iff.mp g.2
    have hg' := congrArg suMat hg
    simpa [suMat_mul, hsD] using hg'
  have hconj := conj_mem_longRootGroupSU_of_commute hcomm hx
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj

theorem eq_one_of_blockEmb_four_mem_scalars {n : ℕ} (hn : 5 ≤ n) {A : Su K p f 4}
    (hA : ((blockEmb K p f n 4 0 (by omega) A : Su K p f n) : GL (Fin n) K) ∈
      StatedScalars (Fin n) K) : A = 1 := by
  obtain ⟨c, hc⟩ := hA
  have ha : ¬ (0 ≤ (⟨4, by omega⟩ : Fin n).val ∧ (⟨4, by omega⟩ : Fin n).val < 0 + 4) := by
    simp
  have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
    hc) ⟨4, by omega⟩) ⟨4, by omega⟩
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, coe_coe_blockEmb, blockMat_apply_of_not_mem_left _ ha,
    Matrix.one_apply_eq] at h1
  have hc1 : c = 1 := Units.ext h1
  rw [hc1, map_one] at hc
  apply blockEmb_injective (K := K) (p := p) (f := f) (m := n) (k := 4) (i := 0) (by omega)
  rw [map_one]
  exact Subtype.ext hc.symm

theorem injective_mk_comp_blockEmb_four {n : ℕ} (hn : 5 ≤ n) :
    Function.Injective ((QuotientGroup.mk'
      ((StatedScalars (Fin n) K).subgroupOf (SUid (unitaryInvolution K p f) n))).comp
        (blockEmb K p f n 4 0 (by omega))) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hA
  exact eq_one_of_blockEmb_four_mem_scalars hn hA

end Block

section Assembly

theorem hasCleanFullClassBMember_statedProj_suid
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {K : Type} [Field K]
    [Finite K] [Fact (Nat.Prime 3)] [CharP K 3] (hK : Nat.card K = 9) {n : ℕ} (hn : 5 ≤ n)
    [IsSimpleGroup (StatedProj (SUid (unitaryInvolution K 3 1) n))] :
    HasCleanFullClassBMember (StatedProj (SUid (unitaryInvolution K 3 1) n)) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) (p := 3) (by norm_num)
  have hF : Nat.card K = (3 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI hHfin : Finite (Su K 3 1 n) := inferInstance
  haveI hQfin : Finite (StatedProj (SUid (unitaryInvolution K 3 1) n)) := inferInstance
  haveI hXfin : Finite (Su K 3 1 4) := inferInstance
  have hX : BlockData (Su K 3 1 4) :=
    BlockData.of_mulEquiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hF 4).symm)
      (blockData_statedSU hGA hK (Or.inl rfl))
  exact hasCleanFullClassBMember_of_block
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (SUid (unitaryInvolution K 3 1) n)))
    (QuotientGroup.mk'_surjective _)
    (by
      rw [QuotientGroup.ker_mk']
      exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    (blockEmb K 3 1 n 4 0 (by omega))
    (injective_mk_comp_blockEmb_four hn)
    (c := negOneSUFour K 3 1)
    (orderOf_negOneSUFour h2)
    negOneSUFour_mem_center
    (normal_blockEmb_four h2 (by omega))
    hX

theorem hasCleanFullClassBMember_psu
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 9) {n : ℕ} (hn : 5 ≤ n)
    [IsSimpleGroup (StatedProj (StatedSU n 3 K))] :
    HasCleanFullClassBMember (StatedProj (StatedSU n 3 K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 3 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hF : Nat.card K = (3 ^ 1) ^ 2 := by rw [hK]; norm_num
  have key : ∀ S : Subgroup (GL (Fin n) K), SUid (unitaryInvolution K 3 1) n = S →
      IsSimpleGroup (StatedProj S) → HasCleanFullClassBMember (StatedProj S) := by
    intro S hS hsimple
    subst hS
    exact hasCleanFullClassBMember_statedProj_suid hGA hK hn
  exact key _ (SUid_eq_statedSU hF n) inferInstance

theorem hasCleanFullClassBMember_of_lieModel_psu
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q] {n : ℕ} (hn : 5 ≤ n)
    (h : CFSG.Blueprint.LieModel Q .PSU n 3 1) : HasCleanFullClassBMember Q := by
  have hcm := h.statedClassicalModel (by decide)
  unfold CFSG.Open.StatedClassicalModel at hcm
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hcm
  have hK : Nat.card K = 9 := by simpa using hKcard
  haveI : IsSimpleGroup (StatedProj (StatedSU n 3 K)) := e.symm.isSimpleGroup
  exact HasCleanFullClassBMember.of_mulEquiv e.symm (hasCleanFullClassBMember_psu hGA hK hn)

end Assembly

end CFSG.OddStandard.HigherRank.F3
