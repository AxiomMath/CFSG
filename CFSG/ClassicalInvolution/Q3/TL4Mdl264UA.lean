module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UD
import CFSG.ClassicalInvolution.Q3.TL4Mdl264Eng

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4.U264

open Matrix CFSG.LieType.Multipliers.U43 CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.ComponentClassification.HarrisLit.P1.U43 CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
open CFSG.Assembly.LowTwoRank (StatedSU)

theorem isPGroup_closure_of_comm {G : Type*} [Group G] {s : Set G}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (h4 : ∀ x ∈ s, x ^ 4 = 1) :
    IsPGroup 2 ↥(Subgroup.closure s) :=
  CFSG.ClassicalInvolution.Q3.TL4.O264.isPGroup_closure_of_comm_gen hcomm h4

theorem two_lt_card_of_three {G : Type*} [Group G] {H : Subgroup G} [Finite ↥H] {a b c : G}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 < Nat.card ↥H :=
  CFSG.ClassicalInvolution.Q3.TL4.O264.two_lt_card_of_three_gen ha hb hc hab hac hbc

theorem three_ne_of_sq {G : Type*} [Group G] {x : G} (hx : x * x ≠ 1) :
    (1 : G) ≠ x * x ∧ (1 : G) ≠ x ∧ x * x ≠ x := by
  refine ⟨fun h => hx h.symm, fun h => hx (by rw [← h, one_mul]), fun h => hx ?_⟩
  have h1 : x = 1 := mul_left_cancel (a := x) (by rw [h, mul_one])
  rw [h1, one_mul]

@[expose] def iU : F9 := ⟨0, 1⟩

@[expose] def mW3 : Matrix (Fin 4) (Fin 4) F9 := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0]

@[expose] def mW3i : Matrix (Fin 4) (Fin 4) F9 :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

theorem mW3_mul : mW3 * mW3i = 1 := by decide +kernel

theorem mW3i_mul : mW3i * mW3 = 1 := by decide +kernel

@[expose] def wGL : GL (Fin 4) F9 := ⟨mW3, mW3i, mW3_mul, mW3i_mul⟩

theorem wGL_mem : wGL ∈ StatedSU 4 3 F9 := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · show mW3.det = 1
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, mW3]
  · show (mW3.map (· ^ 3))ᵀ * mW3 = 1
    decide +kernel

theorem w_u0_w : mW3 * matN9 codeU0 * mW3i = Matrix.diagonal ![1, iU, -iU, 1] := by
  decide +kernel

theorem w_r0_w : mW3 * matN9 codeR0 * mW3i = Matrix.diagonal ![1, -1, -1, 1] := by
  decide +kernel

theorem matU0_eq : matN9 codeU0 = Matrix.diagonal ![1, 1, iU, -iU] := by decide +kernel

theorem matU1_eq : matN9 codeU1 = Matrix.diagonal ![iU, -iU, 1, 1] := by decide +kernel

@[expose] noncomputable def wP : Equiv.Perm (Fin 820) := perm820 wGL

@[expose] noncomputable def u2P : Equiv.Perm (Fin 820) := wP * u0P * wP⁻¹

@[expose] noncomputable def r2P : Equiv.Perm (Fin 820) := wP * r0P * wP⁻¹

@[expose] noncomputable def K2 : Subgroup (Equiv.Perm (Fin 820)) := conjSub wP K0

@[expose] noncomputable def P2 : Subgroup (Equiv.Perm (Fin 820)) :=
  Subgroup.closure {u0P, u1P, u2P}

theorem wP_mem : wP ∈ P := by
  rw [P_eq_range]
  exact ⟨QuotientGroup.mk ⟨wGL, wGL_mem⟩, psi_mk ⟨wGL, wGL_mem⟩⟩

theorem u2P_eq : u2P = perm820 (wGL * matU0 * wGL⁻¹) := by
  rw [u2P, wP, u0P, map_mul, map_mul, map_inv]

theorem diag_comm (a b : Fin 4 → F9) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal b * Matrix.diagonal a := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem coe_w_u0_w : ((wGL * matU0 * wGL⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
    Matrix.diagonal ![1, iU, -iU, 1] := by
  rw [Units.val_mul, Units.val_mul]
  exact w_u0_w

theorem coe_matU0 : ((matU0 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
    Matrix.diagonal ![1, 1, iU, -iU] := matU0_eq

theorem coe_matU1 : ((matU1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
    Matrix.diagonal ![iU, -iU, 1, 1] := matU1_eq

theorem gl_comm_of_diag {A B : GL (Fin 4) F9} {a b : Fin 4 → F9}
    (hA : (A : Matrix (Fin 4) (Fin 4) F9) = Matrix.diagonal a)
    (hB : (B : Matrix (Fin 4) (Fin 4) F9) = Matrix.diagonal b) : A * B = B * A :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, hA, hB, diag_comm])

theorem u0_u1 : u0P * u1P = u1P * u0P := by
  rw [u0P, u1P, ← map_mul, ← map_mul, gl_comm_of_diag coe_matU0 coe_matU1]

theorem u0_u2 : u0P * u2P = u2P * u0P := by
  rw [u0P, u2P_eq, ← map_mul, ← map_mul, gl_comm_of_diag coe_matU0 coe_w_u0_w]

theorem u1_u2 : u1P * u2P = u2P * u1P := by
  rw [u1P, u2P_eq, ← map_mul, ← map_mul, gl_comm_of_diag coe_matU1 coe_w_u0_w]


theorem u2_sq : u2P * u2P = r2P := by
  rw [u2P, r2P, ← rel_facts.2.2.1]
  group

theorem r2P_eq : r2P = perm820 (wGL * matR0 * wGL⁻¹) := by
  rw [r2P, wP, r0P, map_mul, map_mul, map_inv]

theorem ptIndex_ne :
    ptIndex (Matrix.diagonal ![1, -1, -1, 1] *ᵥ decode 243) ≠
      ptIndex (matN9 codeR0 *ᵥ decode 243) := by
  decide +kernel

theorem r2_ne_r0 : r2P ≠ r0P := by
  intro h
  have h1 := congrArg (fun σ : Equiv.Perm (Fin 820) => ((σ ⟨243, by norm_num⟩ : Fin 820) : ℕ)) h
  simp only [r2P_eq, r0P, perm820_apply] at h1
  change ptIndex ((mW3 * matN9 codeR0 * mW3i) *ᵥ decode 243) =
    ptIndex (matN9 codeR0 *ᵥ decode 243) at h1
  rw [w_r0_w] at h1
  exact ptIndex_ne h1

theorem r2_ne_one : r2P ≠ 1 := by
  intro h
  apply rel_facts.1
  have h1 : r0P = wP⁻¹ * r2P * wP := by rw [r2P]; group
  rw [h1, h, mul_one, inv_mul_cancel]

theorem isPGroup_P2 : IsPGroup 2 ↥P2 := by
  have h4 : ∀ x : Equiv.Perm (Fin 820), x * x = r0P → x ^ 4 = 1 := fun x hx => by
    rw [show x ^ 4 = (x * x) * (x * x) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
      hx, rel_facts.2.1]
  refine isPGroup_closure_of_comm ?_ ?_
  · rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl)
    · rfl
    · exact u0_u1
    · exact u0_u2
    · exact u0_u1.symm
    · rfl
    · exact u1_u2
    · exact u0_u2.symm
    · exact u1_u2.symm
    · rfl
  · rintro x (rfl | rfl | rfl)
    · exact h4 _ rel_facts.2.2.1
    · exact h4 _ rel_facts.2.2.2.2.1
    · rw [show u2P ^ 4 = (u2P * u2P) * (u2P * u2P) by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc], u2_sq, r2P]
      calc wP * r0P * wP⁻¹ * (wP * r0P * wP⁻¹) = wP * (r0P * r0P) * wP⁻¹ := by group
        _ = 1 := by rw [rel_facts.2.1]; group

theorem P2_le_P : P2 ≤ P := by
  rw [P2, Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact mem_P.2.1
  · exact mem_P.2.2.2.1
  · exact P.mul_mem (P.mul_mem wP_mem mem_P.2.1) (P.inv_mem wP_mem)

theorem u0_mem_P2 : u0P ∈ P2 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem u1_mem_P2 : u1P ∈ P2 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem u2_mem_P2 : u2P ∈ P2 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem u1_mem_K1 : u1P ∈ K1 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem K1_eq : K1 = conjSub s01P⁻¹ K0 := by
  rw [← conjSub_s01, ← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem three_over_P2 (hu : IsUniqueInvolution K0 r0P) :
    K1 ≠ K0 ∧ K2 ≠ K0 ∧ K2 ≠ K1 ∧ 2 < Nat.card ↥(K0 ⊓ P2) ∧ 2 < Nat.card ↥(K1 ⊓ P2) ∧
      2 < Nat.card ↥(K2 ⊓ P2) := by
  have hu1 : IsUniqueInvolution K1 r0P := by
    have h := hu.conj s01P⁻¹
    rw [← K1_eq] at h
    have hc : s01P⁻¹ * r0P * s01P⁻¹⁻¹ = r0P := by
      rw [inv_inv, mul_assoc, ← rel_facts.2.2.2.2.2.2.2.2.2.2.1, ← mul_assoc, inv_mul_cancel,
        one_mul]
    rwa [hc] at h
  have hu2 : IsUniqueInvolution K2 r2P := hu.conj wP
  refine ⟨K1_ne_K0, fun h => ?_, fun h => ?_, ?_, ?_, ?_⟩
  · rw [h] at hu2
    exact r2_ne_r0 (hu2.eq hu)
  · rw [h] at hu2
    exact r2_ne_r0 (hu2.eq hu1)
  · obtain ⟨n1, n2, n3⟩ := three_ne_of_sq (x := u0P) (by rw [rel_facts.2.2.1]; exact rel_facts.1)
    rw [rel_facts.2.2.1] at n1 n3
    exact two_lt_card_of_three ⟨one_mem _, one_mem _⟩ ⟨r0_mem_K0, by
      rw [← rel_facts.2.2.1]; exact mul_mem u0_mem_P2 u0_mem_P2⟩ ⟨u0_mem_K0, u0_mem_P2⟩ n1 n2 n3
  · obtain ⟨n1, n2, n3⟩ := three_ne_of_sq (x := u1P)
      (by rw [rel_facts.2.2.2.2.1]; exact rel_facts.1)
    rw [rel_facts.2.2.2.2.1] at n1 n3
    exact two_lt_card_of_three ⟨one_mem _, one_mem _⟩ ⟨hu1.mem, by
      rw [← rel_facts.2.2.2.2.1]; exact mul_mem u1_mem_P2 u1_mem_P2⟩ ⟨u1_mem_K1, u1_mem_P2⟩
      n1 n2 n3
  · obtain ⟨n1, n2, n3⟩ := three_ne_of_sq (x := u2P) (by rw [u2_sq]; exact r2_ne_one)
    rw [u2_sq] at n1 n3
    exact two_lt_card_of_three ⟨one_mem _, one_mem _⟩ ⟨hu2.mem, by
      rw [← u2_sq]; exact mul_mem u2_mem_P2 u2_mem_P2⟩
      ⟨conj_mem_conjSub u0_mem_K0, u2_mem_P2⟩ n1 n2 n3

end CFSG.ClassicalInvolution.Q3.TL4.U264
