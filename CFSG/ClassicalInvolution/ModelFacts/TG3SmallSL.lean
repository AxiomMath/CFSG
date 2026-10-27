module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Small
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSL
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSLGen
public import CFSG.ClassicalInvolution.ModelFacts.TG3F3
public import CFSG.ClassicalInvolution.Models.Transfer.Linear

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Struct

theorem mul_self_eq_one_of_central_ratio {G : Type*} [Group G] {i₁ i₂ : G} (h₁ : i₁ * i₁ = 1)
    (h₂ : i₂ * i₂ = 1) (hc : i₂ * i₁⁻¹ ∈ Subgroup.center G) :
    (i₂ * i₁⁻¹) * (i₂ * i₁⁻¹) = 1 := by
  have hinv : i₁⁻¹ = i₁ := inv_eq_of_mul_eq_one_right h₁
  rw [hinv] at hc ⊢
  have hcomm := Subgroup.mem_center_iff.mp hc i₁
  have h12 : i₁ * i₂ = i₂ * i₁ := by
    calc i₁ * i₂ = i₁ * i₂ * (i₁ * i₁) := by rw [h₁, mul_one]
      _ = (i₁ * (i₂ * i₁)) * i₁ := by group
      _ = (i₂ * i₁ * i₁) * i₁ := by rw [hcomm]
      _ = i₂ * (i₁ * i₁) * i₁ := by group
      _ = i₂ * i₁ := by rw [h₁, mul_one]
  calc (i₂ * i₁) * (i₂ * i₁) = i₂ * (i₁ * i₂) * i₁ := by group
    _ = i₂ * (i₂ * i₁) * i₁ := by rw [h12]
    _ = (i₂ * i₂) * (i₁ * i₁) := by group
    _ = 1 := by rw [h₁, h₂, one_mul]

theorem eq_or_coe_eq_neg_of_central_ratio {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    {i₁ i₂ : SL(n, K)} (h₁ : i₁ * i₁ = 1) (h₂ : i₂ * i₂ = 1)
    (hc : i₂ * i₁⁻¹ ∈ Subgroup.center SL(n, K)) :
    i₂ = i₁ ∨ (i₂ : Matrix (Fin n) (Fin n) K) = -(i₁ : Matrix (Fin n) (Fin n) K) := by
  have hz2 := mul_self_eq_one_of_central_ratio h₁ h₂ hc
  rcases Transfer.eq_one_or_coe_eq_neg_one hn hc hz2 with h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · right
    have h' : i₂ = (i₂ * i₁⁻¹) * i₁ := by group
    have h3 := congrArg (fun A : SL(n, K) => (A : Matrix (Fin n) (Fin n) K)) h'
    simp only [Matrix.SpecialLinearGroup.coe_mul, h, neg_mul, one_mul] at h3
    exact h3

theorem sl4_twin_gen {L₁ L₂ : Subgroup SL(4, 𝔽₃)} {i₁ i₂ : SL(4, 𝔽₃)}
    (h₁ : IsLongRootSL2 (show 2 ≤ 4 by norm_num) L₁ i₁)
    (h₂ : IsLongRootSL2 (show 2 ≤ 4 by norm_num) L₂ i₂) (hR : L₁ ≠ L₂)
    (hc : i₂ * i₁⁻¹ ∈ Subgroup.center SL(4, 𝔽₃)) :
    Commutes L₁ L₂ ∧ i₁ ∉ Subgroup.center SL(4, 𝔽₃) ∧ i₂ ∉ Subgroup.center SL(4, 𝔽₃) ∧
      ∀ r₁ ∈ L₁, ∀ r₂ ∈ L₂, r₁ * r₁ = i₁ → r₂ * r₂ = i₂ →
        Subgroup.centralizer ({i₁} : Set SL(4, 𝔽₃)) ⊔
          Subgroup.centralizer ({r₁ * r₂} : Set SL(4, 𝔽₃)) = ⊤ := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hneg : (i₂ : Matrix (Fin 4) (Fin 4) 𝔽₃) = -(i₁ : Matrix (Fin 4) (Fin 4) 𝔽₃) := by
    rcases eq_or_coe_eq_neg_of_central_ratio (by norm_num) h₁.mul_self h₂.mul_self hc with h | h
    · exfalso
      apply hR
      rw [h₁.eq_longRootGroup h2, h₂.eq_longRootGroup h2, h]
    · exact h
  have hcc : (i₁ : Matrix (Fin 4) (Fin 4) 𝔽₃) * i₂ = i₂ * i₁ := by
    rw [hneg, Matrix.mul_neg, Matrix.neg_mul]
  have hnc₁ := Transfer.not_mem_center_of_isLongRootSL2 h2 (by norm_num : 3 ≤ 4) h₁
  have hnc₂ := Transfer.not_mem_center_of_isLongRootSL2 h2 (by norm_num : 3 ≤ 4) h₂
  have hV : eigSpace (i₁ : Matrix (Fin 4) (Fin 4) 𝔽₃) (-1) ⊓
      eigSpace (i₂ : Matrix (Fin 4) (Fin 4) 𝔽₃) (-1) = ⊥ := by
    have e : eigSpace (i₂ : Matrix (Fin 4) (Fin 4) 𝔽₃) (-1) =
        eigSpace (i₁ : Matrix (Fin 4) (Fin 4) 𝔽₃) 1 := by
      ext v
      rw [mem_eigSpace_neg_one, mem_eigSpace_one, hneg, Matrix.neg_mulVec, neg_inj]
    rw [e]
    exact (isCompl_eigSpace h2 h₁.coe_mul_self).inf_eq_bot
  have hcomm : Commutes L₁ L₂ := fun x hx y hy => by
    rw [h₁.eq_longRootGroup h2] at hx
    rw [h₂.eq_longRootGroup h2] at hy
    exact mul_comm_of_inf_eq_bot h2 h₁.coe_mul_self h₂.coe_mul_self hcc hV hx hy
  refine ⟨hcomm, hnc₁, hnc₂, fun r₁ hr₁ r₂ hr₂ hsq₁ hsq₂ => ?_⟩
  have hr₁A := ((h₁.mem_iff h2).mp hr₁).1
  have hr₂A : (r₂ : Matrix (Fin 4) (Fin 4) 𝔽₃) * i₁ = i₁ * r₂ := by
    have h := ((h₂.mem_iff h2).mp hr₂).1
    rw [hneg, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
    exact h
  have hiJ : i₁ * (r₁ * r₂) = (r₁ * r₂) * i₁ := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun a b => congrFun (congrFun ?_ a) b
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc,
      ← hr₁A, Matrix.mul_assoc, ← hr₂A, ← Matrix.mul_assoc]
  have hJJ : (r₁ * r₂) * (r₁ * r₂) = i₁ * i₂ := by
    calc (r₁ * r₂) * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
      _ = r₁ * (r₁ * r₂) * r₂ := by rw [← hcomm r₁ hr₁ r₂ hr₂]
      _ = (r₁ * r₁) * (r₂ * r₂) := by group
      _ = i₁ * i₂ := by rw [hsq₁, hsq₂]
  have hJ : ((r₁ * r₂ : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) * (r₁ * r₂ : SL(4, 𝔽₃)) = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hJJ, Matrix.SpecialLinearGroup.coe_mul, hneg,
      Matrix.mul_neg, h₁.coe_mul_self]
  exact sl4_gen eq_zero_or_one_or_neg_one_three mul_self_ne_neg_one_three h2 i₁ (r₁ * r₂)
    h₁.mul_self hiJ hJ (h₁.finrank_minusSpace h2)

end Struct

section Model


theorem isLongRootSL2_sl2Inv_four {R : Subgroup SL(4, 𝔽₃)}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Fact.out).D)
    (e : R ≃* SL(2, 𝔽₃)) : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R (sl2Inv e) := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hL := fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := 3) (by omega)
  have hR' : R ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ 3 + 1) := by
    rw [← hL]
    exact hR
  obtain ⟨i, hi⟩ := hR'
  have hie : i = sl2Inv e :=
    eq_sl2Inv_of_orderOf_eq_two odd_natCard_galoisField_three e hi.mem
      ((hi.isClassicalSL2 h2).orderOf_eq_two)
  rw [← hie]
  exact hi

theorem compGen3Twin_psl_four (hadm : StatedLieAdmissible .PSL 4 3 1) :
    CompGen3Twin (compModel 3 1 .PSL 4) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfin : Finite (compModel 3 1 .PSL 4).G :=
    finite_modelUniv (t := .PSL) hp2 Nat.prime_three trivial hadm
  have : Finite SL(4, 𝔽₃) := hfin
  refine compGen3Twin_small_of_gen₂ (G := SL(4, 𝔽₃))
    (fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Fact.out).D) ?_ ?_ ?_
  · intro R hR
    exact nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL) trivial hadm
      (by decide) (by decide) hR
  · intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne hc
    obtain ⟨hcomm, hnc₁, hnc₂, -⟩ := sl4_twin_gen (isLongRootSL2_sl2Inv_four hR₁ e₁)
      (isLongRootSL2_sl2Inv_four hR₂ e₂) hne hc
    exact ⟨hcomm, hnc₁, hnc₂⟩
  · intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne hc r₁ hr₁ r₂ hr₂ hsq₁ hsq₂
    obtain ⟨-, -, -, hgen⟩ := sl4_twin_gen (isLongRootSL2_sl2Inv_four hR₁ e₁)
      (isLongRootSL2_sl2Inv_four hR₂ e₂) hne hc
    exact hgen r₁ hr₁ r₂ hr₂ hsq₁ hsq₂

end Model

end CFSG.ClassicalInvolution.ModelFacts.TG3
