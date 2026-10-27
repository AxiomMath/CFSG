module

public import CFSG.LargeExtraspecial.AS35QIxSetup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem K_sq_eq_one {c : K} (h : c * c = 1) : c = 1 := by
  rcases AS35QTh.K_cases c with rfl | rfl | rfl | rfl
  · simp at h
  · rfl
  · rw [AS35QTh.omega_mul_omega] at h
    exact absurd h frob_omega_ne_one
  · rw [AS35QTh.frob_omega_mul_frob_omega] at h
    exact absurd h omega_ne_one

theorem eq_zero_of_omega_mul {c : K} (h : ω * c = c) : c = 0 := by
  have h1 : (ω - 1) * c = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) omega_ne_one
  · exact h2

theorem eq_zero_of_frob_omega_mul {c : K} (h : frob ω * c = c) : c = 0 := by
  have h1 : (frob ω - 1) * c = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) frob_omega_ne_one
  · exact h2

theorem vec_eq_sum (x : Fin 3 → K) :
    x = x 0 • ![(1 : K), 0, 0] + x 1 • ![(0 : K), 1, 0] + x 2 • ![(0 : K), 0, 1] := by
  funext i
  fin_cases i <;> simp

namespace IxSetup

variable (T : IxSetup S)

noncomputable abbrev tb : S.O := S.ρ ⟨_, T.hgM⟩

noncomputable abbrev zL : S.Qt →ₗ[ZMod 2] S.Qt := (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap

theorem l_add (x y : Fin 3 → K) : T.l (x + y) = T.l x + T.l y := T.hl.add x y

theorem l_injective : Function.Injective T.l := T.hl.bij.1

theorem l_surjective : Function.Surjective T.l := T.hl.bij.2

theorem l_zero : T.l 0 = 0 := T.hl.l_zero

theorem l_omega (x : Fin 3 → K) :
    T.l (ω • x) = (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l x) := T.hl.omega x

theorem zeta_sq (v : S.Qt) : T.zL (T.zL v) + T.zL v + v = 0 := T.hζ2 v

theorem l_smul (c : K) (x : Fin 3 → K) : T.l (c • x) = AS35QTh.act T.zL c (T.l x) := by
  rcases AS35QTh.K_cases c with rfl | rfl | rfl | rfl
  · rw [zero_smul, l_zero, AS35QTh.act_zero_left]
  · rw [one_smul, AS35QTh.act_one]
  · rw [l_omega, AS35QTh.act_omega]
    rfl
  · rw [T.hl.l_frob_omega, AS35QTh.act_frob_omega, add_comm]

theorem l_eq_sum (x : Fin 3 → K) :
    T.l x = AS35QTh.act T.zL (x 0) (T.l ![1, 0, 0]) + AS35QTh.act T.zL (x 1) (T.l ![0, 1, 0]) +
      AS35QTh.act T.zL (x 2) (T.l ![0, 0, 1]) := by
  conv_lhs => rw [vec_eq_sum x]
  rw [l_add, l_add, l_smul, l_smul, l_smul]

theorem map_l (σ : S.Qt →ₗ[ZMod 2] S.Qt) (hσ : ∀ v, T.zL (σ v) = σ (T.zL v)) (x : Fin 3 → K) :
    σ (T.l x) = AS35QTh.act T.zL (x 0) (σ (T.l ![1, 0, 0])) +
      AS35QTh.act T.zL (x 1) (σ (T.l ![0, 1, 0])) +
      AS35QTh.act T.zL (x 2) (σ (T.l ![0, 0, 1])) := by
  rw [l_eq_sum, map_add, map_add, AS35QTh.act_comm hσ, AS35QTh.act_comm hσ, AS35QTh.act_comm hσ]

theorem act_l (c : K) (x : Fin 3 → K) : AS35QTh.act T.zL c (T.l x) = T.l (c • x) :=
  (T.l_smul c x).symm

theorem apply_O (s s' : S.O) (v : S.Qt) :
    ((s * s' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s' : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem zL_comm {s : S.O} (hs : s * T.ζ = T.ζ * s) (v : S.Qt) :
    T.zL ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.zL v) := by
  have := congrArg (fun r : S.O => (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hs
  exact this.symm

theorem tb_mul_self : T.tb * T.tb = 1 := rho_t_mul_self S T.hgD T.hgM

theorem tb_mem_Mbar : T.tb ∈ S.Mbar := ⟨_, rfl⟩

theorem zeta_comm_tb : T.ζ * T.tb = T.tb * T.ζ := T.hζt

theorem alpha_l_e0 : (T.α : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![1, 0, 0]) = T.l ![1, 0, 0] := by
  rw [T.hlα]
  simp

theorem beta_l_e0 : (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![1, 0, 0]) = T.l ![0, 1, 0] := by
  rw [T.hlβ]
  simp

theorem beta_l_e1 : (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![0, 1, 0]) = T.l ![0, 0, 1] := by
  rw [T.hlβ]
  simp

theorem beta_l_e2 : (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![0, 0, 1]) = T.l ![1, 0, 0] := by
  rw [T.hlβ]
  simp

theorem eq_zero_of_alpha_fix {y : Fin 3 → K}
    (h : (T.α : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l y) = T.l y) : y 1 = 0 ∧ y 2 = 0 := by
  rw [T.hlα] at h
  have h' := T.l_injective h
  have h1 := congrFun h' 1
  have h2 := congrFun h' 2
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at h1 h2
  exact ⟨eq_zero_of_omega_mul h1, eq_zero_of_frob_omega_mul h2⟩

theorem inv_apply_of_apply {s : S.O} {v : S.Qt} (h : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ((s⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  conv_lhs => rw [← h]
  rw [← apply_O, inv_mul_cancel]
  rfl

theorem beta_inv_apply (v : S.Qt) :
    ((T.β⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  have e : T.β⁻¹ = T.β * T.β := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three, T.hβ3]
  rw [e]
  rfl

theorem tb_beta (v : S.Qt) : (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
    ((T.β⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  have e : T.tb * T.β = T.β⁻¹ * T.tb := by
    calc T.tb * T.β = T.tb * T.β * T.tb⁻¹ * T.tb := (inv_mul_cancel_right _ _).symm
      _ = T.β⁻¹ * T.tb := by rw [T.htβ]
  rw [← apply_O, ← apply_O, e]

theorem alpha_tb (v : S.Qt) : (T.α : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
    (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (((T.α⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  have hinv : T.tb⁻¹ = T.tb := inv_eq_of_mul_eq_one_right T.tb_mul_self
  have e : T.α * T.tb = T.tb * T.α⁻¹ := by
    calc T.α * T.tb = T.tb * (T.tb * T.α * T.tb) := by
          rw [← mul_assoc, ← mul_assoc, T.tb_mul_self, one_mul]
      _ = T.tb * T.α⁻¹ := by
        rw [show T.tb * T.α * T.tb = T.tb * T.α * T.tb⁻¹ by rw [hinv], T.htα]
  rw [← apply_O, ← apply_O, e]

theorem tb_zL (v : S.Qt) : T.zL ((T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
    (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.zL v) := T.zL_comm T.zeta_comm_tb.symm v

theorem tb_tb (v : S.Qt) :
    (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
  rw [← apply_O, T.tb_mul_self]
  rfl

theorem tb_act (c : K) (v : S.Qt) :
    (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (AS35QTh.act T.zL c v) =
      AS35QTh.act T.zL c ((T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) v) :=
  AS35QTh.act_comm (f := (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap) (fun v => T.tb_zL v) c v

theorem tb_l_e0 : (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![1, 0, 0]) = T.l ![1, 0, 0] := by
  obtain ⟨y, hy⟩ := T.l_surjective ((T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![1, 0, 0]))
  have hα : (T.α : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l y) = T.l y := by
    rw [hy, alpha_tb, inv_apply_of_apply T.alpha_l_e0]
  obtain ⟨h1, h2⟩ := T.eq_zero_of_alpha_fix hα
  have hy' : y = y 0 • ![(1 : K), 0, 0] := by
    funext i
    fin_cases i <;> simp [h1, h2]
  have htt := T.tb_tb (T.l ![1, 0, 0])
  rw [← hy, hy', l_smul, tb_act, ← hy, hy', ← l_smul, smul_smul] at htt
  have h0 := congrFun (T.l_injective htt) 0
  simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one] at h0
  have hy1 := K_sq_eq_one h0
  rw [← hy, hy', hy1, one_smul]

theorem tb_l_e1 : (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![0, 1, 0]) = T.l ![0, 0, 1] := by
  rw [← T.beta_l_e0, tb_beta, tb_l_e0, beta_inv_apply, beta_l_e0, beta_l_e1]

theorem tb_l_e2 : (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![0, 0, 1]) = T.l ![0, 1, 0] := by
  rw [← T.beta_l_e1, tb_beta, tb_l_e1, beta_inv_apply, beta_l_e2, beta_l_e0]

theorem tb_l (x : Fin 3 → K) :
    (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l x) = T.l ![x 0, x 2, x 1] := by
  have h := T.map_l (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap (fun v => T.tb_zL v) x
  simp only [LinearEquiv.coe_coe] at h
  rw [h, tb_l_e0, tb_l_e1, tb_l_e2, T.l_eq_sum ![x 0, x 2, x 1]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  abel

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
