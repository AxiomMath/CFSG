module

public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.GH74 CFSG.GH74.Exceptional Matrix CFSG.Assembly.LowTwoRank

@[expose] def spPM (A B : SpMat3) : Bool := spBEq A B || spBEq A (-B)

@[expose] def vGen : Fin 6 → SpMat3 :=
  ![sp43Mat 24, spMul (sp43Mat 10) (sp43Mat 17), spMul (sp43Mat 10) (sp43Mat 6), sp43Mat 24,
    spMul (sp43Mat 17) (sp43Mat 10), spMul (sp43Mat 6) (sp43Mat 10)]

@[expose] noncomputable def vGenE : Fin 6 → PSp43 :=
  ![s43 24, s43 10 * s43 17, s43 10 * s43 6, s43 24, s43 17 * s43 10, s43 6 * s43 10]

@[expose] def vL : Fin 64 → SpMat3 :=
  ![
    fromBlocks !![1, 0; 0, 1] !![0, 0; 0, 0] !![0, 0; 0, 0] !![1, 0; 0, 1],
    fromBlocks !![0, 1; 2, 0] !![0, 1; 2, 0] !![0, 1; 2, 0] !![0, 2; 1, 0],
    fromBlocks !![0, 1; 2, 1] !![0, 2; 2, 2] !![2, 0; 0, 1] !![0, 1; 2, 2],
    fromBlocks !![1, 0; 1, 1] !![0, 1; 1, 1] !![0, 1; 1, 0] !![2, 2; 0, 2],
    fromBlocks !![2, 2; 1, 2] !![1, 1; 0, 0] !![2, 0; 2, 2] !![0, 0; 0, 2],
    fromBlocks !![2, 1; 2, 2] !![1, 0; 1, 0] !![0, 1; 2, 1] !![1, 2; 2, 1],
    fromBlocks !![0, 0; 0, 1] !![1, 0; 1, 0] !![2, 2; 0, 2] !![1, 2; 1, 1],
    fromBlocks !![0, 1; 2, 0] !![1, 2; 2, 2] !![0, 0; 0, 0] !![0, 1; 2, 0],
    fromBlocks !![2, 1; 1, 2] !![1, 1; 0, 0] !![0, 2; 1, 1] !![1, 1; 2, 1],
    fromBlocks !![0, 0; 1, 1] !![2, 1; 1, 1] !![0, 2; 2, 2] !![0, 2; 0, 2],
    fromBlocks !![2, 0; 0, 2] !![1, 2; 2, 0] !![2, 0; 0, 2] !![0, 2; 2, 2],
    fromBlocks !![2, 0; 1, 0] !![2, 1; 1, 1] !![0, 1; 1, 1] !![1, 2; 0, 0],
    fromBlocks !![2, 0; 1, 1] !![0, 1; 2, 0] !![0, 0; 0, 0] !![2, 1; 0, 1],
    fromBlocks !![0, 1; 1, 2] !![2, 2; 0, 0] !![0, 0; 0, 0] !![1, 1; 1, 0],
    fromBlocks !![0, 1; 1, 1] !![1, 2; 2, 0] !![2, 0; 0, 2] !![1, 0; 0, 1],
    fromBlocks !![1, 1; 1, 0] !![1, 0; 1, 0] !![0, 0; 0, 0] !![0, 1; 1, 2],
    fromBlocks !![1, 2; 0, 2] !![0, 1; 2, 0] !![0, 0; 0, 0] !![1, 0; 2, 2],
    fromBlocks !![1, 1; 1, 0] !![2, 1; 1, 1] !![1, 1; 1, 0] !![2, 2; 2, 0],
    fromBlocks !![1, 2; 0, 2] !![1, 0; 0, 0] !![1, 2; 0, 2] !![2, 0; 2, 2],
    fromBlocks !![1, 0; 1, 2] !![2, 1; 1, 1] !![1, 2; 2, 2] !![2, 2; 0, 1],
    fromBlocks !![1, 0; 2, 2] !![2, 2; 2, 2] !![1, 0; 2, 2] !![0, 1; 2, 1],
    fromBlocks !![0, 2; 2, 1] !![1, 2; 2, 2] !![0, 2; 2, 1] !![0, 1; 1, 2],
    fromBlocks !![0, 0; 2, 0] !![0, 1; 2, 0] !![1, 2; 1, 0] !![1, 0; 0, 2],
    fromBlocks !![0, 2; 1, 1] !![1, 1; 1, 1] !![2, 1; 0, 1] !![1, 2; 0, 2],
    fromBlocks !![1, 0; 0, 2] !![0, 1; 2, 0] !![2, 2; 1, 0] !![0, 2; 0, 0],
    fromBlocks !![0, 2; 2, 0] !![0, 1; 2, 0] !![2, 1; 0, 2] !![2, 1; 2, 1],
    fromBlocks !![2, 2; 0, 2] !![2, 0; 0, 0] !![2, 0; 1, 1] !![1, 0; 2, 2],
    fromBlocks !![2, 2; 1, 1] !![0, 1; 2, 0] !![1, 0; 2, 1] !![0, 2; 2, 0],
    fromBlocks !![0, 0; 2, 1] !![2, 2; 2, 2] !![1, 0; 1, 2] !![2, 1; 1, 2],
    fromBlocks !![1, 2; 1, 0] !![1, 0; 1, 0] !![1, 0; 2, 2] !![1, 2; 0, 1],
    fromBlocks !![1, 2; 0, 1] !![2, 0; 0, 0] !![2, 2; 1, 2] !![2, 0; 0, 1],
    fromBlocks !![2, 2; 1, 0] !![1, 1; 1, 1] !![2, 1; 2, 2] !![0, 2; 2, 0],
    fromBlocks !![1, 0; 2, 1] !![2, 2; 0, 0] !![2, 1; 0, 1] !![1, 1; 2, 0],
    fromBlocks !![0, 2; 0, 1] !![1, 0; 0, 0] !![2, 0; 2, 1] !![0, 0; 0, 1],
    fromBlocks !![2, 0; 0, 1] !![1, 0; 0, 0] !![1, 2; 1, 1] !![1, 0; 2, 1],
    fromBlocks !![0, 0; 1, 0] !![0, 1; 1, 1] !![1, 2; 2, 0] !![0, 2; 0, 0],
    fromBlocks !![0, 0; 0, 2] !![1, 0; 0, 0] !![2, 2; 0, 1] !![0, 0; 1, 2],
    fromBlocks !![2, 1; 1, 2] !![1, 1; 1, 1] !![2, 2; 0, 1] !![0, 2; 0, 1],
    fromBlocks !![2, 0; 2, 1] !![0, 0; 0, 0] !![0, 2; 1, 0] !![2, 2; 0, 1],
    fromBlocks !![1, 1; 2, 2] !![0, 2; 2, 2] !![2, 1; 1, 0] !![2, 1; 2, 1],
    fromBlocks !![0, 2; 2, 0] !![2, 2; 2, 2] !![1, 1; 2, 1] !![2, 1; 2, 0],
    fromBlocks !![1, 2; 0, 1] !![2, 1; 1, 0] !![2, 0; 2, 2] !![1, 2; 0, 0],
    fromBlocks !![0, 0; 2, 1] !![1, 1; 0, 0] !![2, 0; 1, 2] !![1, 1; 0, 1],
    fromBlocks !![0, 0; 1, 1] !![1, 2; 2, 0] !![0, 1; 2, 2] !![2, 1; 2, 0],
    fromBlocks !![1, 0; 2, 0] !![1, 2; 2, 0] !![1, 1; 0, 1] !![1, 0; 2, 1],
    fromBlocks !![0, 1; 1, 1] !![0, 1; 1, 1] !![1, 1; 1, 2] !![0, 2; 2, 2],
    fromBlocks !![0, 2; 0, 1] !![1, 0; 1, 0] !![1, 2; 1, 0] !![0, 1; 2, 2],
    fromBlocks !![1, 1; 2, 0] !![1, 2; 2, 0] !![0, 2; 1, 2] !![0, 2; 0, 2],
    fromBlocks !![2, 2; 2, 1] !![0, 2; 2, 2] !![0, 0; 0, 0] !![1, 1; 1, 2],
    fromBlocks !![2, 1; 1, 1] !![2, 1; 1, 1] !![0, 0; 0, 0] !![1, 2; 2, 2],
    fromBlocks !![2, 0; 2, 2] !![1, 0; 1, 0] !![2, 1; 0, 2] !![0, 1; 0, 2],
    fromBlocks !![1, 0; 2, 1] !![0, 2; 2, 2] !![2, 2; 2, 0] !![2, 1; 0, 2],
    fromBlocks !![1, 2; 1, 0] !![0, 1; 1, 1] !![0, 2; 2, 1] !![2, 2; 1, 0],
    fromBlocks !![0, 1; 2, 1] !![1, 1; 0, 0] !![1, 1; 2, 0] !![0, 0; 1, 2],
    fromBlocks !![2, 1; 1, 1] !![0, 1; 2, 0] !![2, 1; 1, 1] !![1, 0; 1, 2],
    fromBlocks !![1, 1; 1, 2] !![0, 0; 0, 0] !![1, 1; 1, 2] !![2, 2; 2, 1],
    fromBlocks !![2, 1; 2, 2] !![1, 2; 2, 2] !![2, 0; 0, 1] !![1, 1; 2, 1],
    fromBlocks !![1, 1; 0, 1] !![2, 1; 1, 0] !![0, 1; 1, 2] !![2, 0; 2, 2],
    fromBlocks !![0, 1; 2, 2] !![2, 1; 1, 0] !![2, 2; 2, 0] !![0, 1; 2, 1],
    fromBlocks !![1, 1; 2, 1] !![1, 2; 2, 2] !![0, 1; 1, 0] !![2, 1; 2, 2],
    fromBlocks !![2, 2; 0, 1] !![0, 2; 1, 0] !![2, 1; 1, 1] !![1, 2; 2, 2],
    fromBlocks !![2, 1; 1, 0] !![2, 1; 1, 0] !![1, 1; 1, 2] !![1, 2; 2, 0],
    fromBlocks !![1, 2; 2, 0] !![0, 2; 2, 2] !![2, 0; 0, 2] !![2, 1; 1, 0],
    fromBlocks !![2, 2; 0, 1] !![0, 0; 0, 0] !![0, 1; 2, 0] !![2, 0; 2, 1]]

@[expose] def parArr : Fin 64 → Fin 64 :=
  ![
    0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 8,
    8, 9, 9, 10, 11, 11, 12, 13, 14, 14, 15, 15, 17, 18, 19, 19,
    20, 20, 22, 23, 23, 24, 24, 26, 27, 28, 29, 29, 30, 30, 32, 33,
    34, 34, 35, 35, 37, 39, 41, 41, 42, 42, 44, 46, 48, 50, 54, 56]

@[expose] def gnArr : Fin 64 → Fin 6 :=
  ![
    0, 0, 1, 2, 1, 2, 0, 2, 0, 0, 2, 0, 1, 2, 0, 1,
    2, 1, 2, 0, 1, 2, 2, 0, 1, 2, 0, 2, 2, 0, 1, 2,
    0, 2, 0, 1, 2, 0, 2, 2, 0, 0, 1, 2, 0, 2, 2, 0,
    1, 2, 0, 2, 2, 0, 1, 2, 0, 2, 2, 0, 0, 2, 0, 2]

@[expose] def checkBFS : Bool :=
  (List.finRange 64).all fun k =>
    k.val == 0 || (decide (parArr k < k) &&
      spPM (spMul (vL (parArr k)) (vGen (gnArr k))) (vL k))

@[expose] def checkClosed : Bool :=
  (List.finRange 64).all fun k => (List.finRange 6).all fun j =>
    (List.finRange 64).any fun k' => spPM (spMul (vL k) (vGen j)) (vL k')

@[expose] def checkDistinct : Bool :=
  (List.finRange 64).all fun k => (List.finRange 64).all fun k' =>
    !(spPM (vL k) (vL k')) || k == k'

@[expose] def checkGens : Bool :=
  spBEq (vL 0) 1 && spBEq (spMul (vGen 0) (vGen 3)) 1 && spBEq (spMul (vGen 1) (vGen 4)) 1 &&
    spBEq (spMul (vGen 2) (vGen 5)) 1

theorem checkBFS_eq : checkBFS = true := by decide +kernel

theorem checkClosed_eq : checkClosed = true := by decide +kernel

theorem checkDistinct_eq : checkDistinct = true := by decide +kernel

theorem checkGens_eq : checkGens = true := by decide +kernel

theorem spPM_iff {A B : SpMat3} : spPM A B = true ↔ A = B ∨ A = -B := by
  simp [spPM, Bool.or_eq_true, spBEq_iff]

section Lift

@[expose] def Lift (x : PSp43) (A : SpMat3) : Prop :=
  ∃ g : StatedSp 2 (ZMod 3), ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) = A ∧
    (QuotientGroup.mk g : PSp43) = x

theorem Lift.mul {x y : PSp43} {A B : SpMat3} (hx : Lift x A) (hy : Lift y B) :
    Lift (x * y) (A * B) := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨h, hh, rfl⟩ := hy
  exact ⟨g * h, by rw [Subgroup.coe_mul, Units.val_mul, hg, hh], QuotientGroup.mk_mul _ g h⟩

theorem Lift.neg {x : PSp43} {A : SpMat3} (hx : Lift x A) : Lift x (-A) := by
  obtain ⟨g, hg, rfl⟩ := hx
  have h1 : ((⟨-1, neg_one_mem_statedSp⟩ * g : StatedSp 2 (ZMod 3)) :
      GL (Fin 2 ⊕ Fin 2) (ZMod 3)) = -(g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) := by
    rw [Subgroup.coe_mul]
    exact neg_one_mul _
  exact ⟨⟨-1, neg_one_mem_statedSp⟩ * g, by rw [h1, Units.val_neg, hg]; rfl, mk_eq_mk_of_eq_neg h1⟩

theorem Lift.of_pm {x : PSp43} {A B : SpMat3} (hx : Lift x A) (h : A = B ∨ A = -B) : Lift x B := by
  rcases h with rfl | rfl
  · exact hx
  · have h := hx.neg
    have e : (-(-B) : SpMat3) = B := neg_neg B
    exact (congrArg (Lift x) e).mp h

theorem Lift.unique {x y : PSp43} {A : SpMat3} (hx : Lift x A) (hy : Lift y A) : x = y := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨h, hh, rfl⟩ := hy
  have : g = h := Subtype.ext (Units.ext (hg.trans hh.symm))
  rw [this]

theorem Lift.pm_of_eq {x : PSp43} {A B : SpMat3} (hA : Lift x A) (hB : Lift x B) :
    A = B ∨ A = -B := by
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨h, hh, hgh⟩ := hB
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hgh
  obtain ⟨c, hc⟩ := hgh
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c =
      (h : GL (Fin 2 ⊕ Fin 2) (ZMod 3))⁻¹ * (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) := hc
  have h1 : (h : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c =
      (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) := by
    rw [hc', mul_inv_cancel_left]
  rcases units_zmod_three c with rfl | rfl
  · left
    rw [map_one, mul_one] at h1
    rw [← hg, ← hh]
    exact (congrArg Units.val h1).symm
  · right
    rw [scalar_neg_one, mul_neg_one] at h1
    rw [← hg, ← hh]
    have := congrArg Units.val h1
    rw [Units.val_neg] at this
    exact this.symm

theorem lift_s43 (i : Fin 45) : Lift (s43 i) (sp43Mat i) :=
  ⟨⟨sp43Unit i, sp43Unit_mem i⟩, rfl, rfl⟩

theorem lift_vGenE (j : Fin 6) : Lift (vGenE j) (vGen j) := by
  fin_cases j
  · exact lift_s43 24
  · have := (lift_s43 10).mul (lift_s43 17)
    rwa [← spMul_eq] at this
  · have := (lift_s43 10).mul (lift_s43 6)
    rwa [← spMul_eq] at this
  · exact lift_s43 24
  · have := (lift_s43 17).mul (lift_s43 10)
    rwa [← spMul_eq] at this
  · have := (lift_s43 6).mul (lift_s43 10)
    rwa [← spMul_eq] at this

end Lift

@[expose] noncomputable def vSub : Subgroup PSp43 :=
  Subgroup.closure {vGenE 0, vGenE 1, vGenE 2}

theorem vGenE_inv_zero : (vGenE 0)⁻¹ = vGenE 3 := by
  simp [vGenE, s43_inv]

theorem vGenE_inv_one : (vGenE 1)⁻¹ = vGenE 4 := by
  simp [vGenE, s43_inv]

theorem vGenE_inv_two : (vGenE 2)⁻¹ = vGenE 5 := by
  simp [vGenE, s43_inv]

theorem vGenE_mem (j : Fin 6) : vGenE j ∈ vSub := by
  have h0 : vGenE 0 ∈ vSub := Subgroup.subset_closure (by simp)
  have h1 : vGenE 1 ∈ vSub := Subgroup.subset_closure (by simp)
  have h2 : vGenE 2 ∈ vSub := Subgroup.subset_closure (by simp)
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · change vGenE 3 ∈ vSub
    rw [← vGenE_inv_zero]
    exact vSub.inv_mem h0
  · change vGenE 4 ∈ vSub
    rw [← vGenE_inv_one]
    exact vSub.inv_mem h1
  · change vGenE 5 ∈ vSub
    rw [← vGenE_inv_two]
    exact vSub.inv_mem h2

theorem closed_step (k : Fin 64) (j : Fin 6) :
    ∃ k' : Fin 64, spPM (spMul (vL k) (vGen j)) (vL k') = true := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp checkClosed_eq k (List.mem_finRange k)) j
    (List.mem_finRange j)
  obtain ⟨k', -, hk'⟩ := List.any_eq_true.mp h
  exact ⟨k', hk'⟩

theorem vL_zero : vL 0 = 1 := by
  have := checkGens_eq
  simp only [checkGens, Bool.and_eq_true] at this
  exact spBEq_iff.1 this.1.1.1

theorem vL_inj {k k' : Fin 64} (h : spPM (vL k) (vL k') = true) : k = k' := by
  have := List.all_eq_true.mp (List.all_eq_true.mp checkDistinct_eq k (List.mem_finRange k)) k'
    (List.mem_finRange k')
  simpa [h] using this

theorem lift_one : Lift 1 1 := ⟨1, rfl, rfl⟩

theorem exists_lift_vL (k : Fin 64) : ∃ x ∈ vSub, Lift x (vL k) := by
  have key : ∀ n : ℕ, ∀ k : Fin 64, k.val = n → ∃ x ∈ vSub, Lift x (vL k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk
      by_cases h0 : k.val = 0
      · have : k = 0 := Fin.ext h0
        subst this
        exact ⟨1, vSub.one_mem, by rw [vL_zero]; exact lift_one⟩
      · have hbfs := List.all_eq_true.mp checkBFS_eq k (List.mem_finRange k)
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hbfs
        rcases hbfs with h | ⟨hlt, hpm⟩
        · exact absurd h h0
        · obtain ⟨x, hx, hxL⟩ := ih (parArr k).val (by have := Fin.lt_def.1 hlt; omega) (parArr k)
            rfl
          refine ⟨x * vGenE (gnArr k), vSub.mul_mem hx (vGenE_mem _), ?_⟩
          have := hxL.mul (lift_vGenE (gnArr k))
          rw [← spMul_eq] at this
          exact this.of_pm (spPM_iff.1 hpm)
  exact key k.val k rfl

theorem exists_vL_of_mem {x : PSp43} (hx : x ∈ vSub) : ∃ k, Lift x (vL k) := by
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, by rw [vL_zero]; exact lift_one⟩
  | mul_right x hx y hy ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨j, rfl⟩ : ∃ j : Fin 6, y = vGenE j := by
      rcases hy with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    obtain ⟨k', hk'⟩ := closed_step k j
    have := hk.mul (lift_vGenE j)
    rw [← spMul_eq] at this
    exact ⟨k', this.of_pm (spPM_iff.1 hk')⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨j, hj⟩ : ∃ j : Fin 6, y⁻¹ = vGenE j := by
      rcases hy with rfl | rfl | rfl
      · exact ⟨3, vGenE_inv_zero⟩
      · exact ⟨4, vGenE_inv_one⟩
      · exact ⟨5, vGenE_inv_two⟩
    rw [hj]
    obtain ⟨k', hk'⟩ := closed_step k j
    have := hk.mul (lift_vGenE j)
    rw [← spMul_eq] at this
    exact ⟨k', this.of_pm (spPM_iff.1 hk')⟩

noncomputable def xk (k : Fin 64) : PSp43 := (exists_lift_vL k).choose

theorem xk_mem (k : Fin 64) : xk k ∈ vSub := (exists_lift_vL k).choose_spec.1

theorem lift_xk (k : Fin 64) : Lift (xk k) (vL k) := (exists_lift_vL k).choose_spec.2

theorem xk_injective : Function.Injective xk := by
  intro k k' h
  have h1 := lift_xk k
  rw [h] at h1
  exact vL_inj (spPM_iff.2 (h1.pm_of_eq (lift_xk k')))

theorem mem_vSub_iff {x : PSp43} : x ∈ vSub ↔ ∃ k, x = xk k := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := exists_vL_of_mem hx
    exact ⟨k, hk.unique (lift_xk k)⟩
  · rintro ⟨k, rfl⟩
    exact xk_mem k

theorem card_vSub : Nat.card ↥vSub = 64 := by
  have e : Fin 64 ≃ ↥vSub := Equiv.ofBijective (fun k => ⟨xk k, xk_mem k⟩)
    ⟨fun a b h => xk_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨k, hk⟩ := mem_vSub_iff.1 x.2
      exact ⟨k, Subtype.ext hk.symm⟩⟩
  rw [← Nat.card_congr e]
  simp

theorem card_PSp43' : Nat.card PSp43 = 25920 := by
  rw [Nat.card_congr psp43EquivU2.toEquiv]
  exact card_U2_four

end CFSG.CGT.PushingUpLit.SolK
