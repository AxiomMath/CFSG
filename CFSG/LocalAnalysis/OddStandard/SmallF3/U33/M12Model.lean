module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

structure M12Mod where
  a : Fin 4
  b : Fin 4
  i : Fin 2
  j : Fin 2
  deriving DecidableEq

namespace M12Mod

@[expose] def act (i j : Fin 2) (c d : Fin 4) : Fin 4 × Fin 4 :=
  let c' := if j = 1 then -c else c
  let d' := if j = 1 then -d else d
  if i = 1 then (d', c') else (c', d')

@[expose] def mul (g h : M12Mod) : M12Mod :=
  ⟨g.a + (act g.i g.j h.a h.b).1, g.b + (act g.i g.j h.a h.b).2, g.i + h.i, g.j + h.j⟩

@[expose] def inv (g : M12Mod) : M12Mod :=
  ⟨(act g.i g.j (-g.a) (-g.b)).1, (act g.i g.j (-g.a) (-g.b)).2, g.i, g.j⟩

instance : Mul M12Mod := ⟨mul⟩

instance : One M12Mod := ⟨⟨0, 0, 0, 0⟩⟩

instance : Inv M12Mod := ⟨inv⟩

theorem act_add : ∀ (i j : Fin 2) (c d c' d' : Fin 4),
    act i j (c + c') (d + d') =
      ((act i j c d).1 + (act i j c' d').1, (act i j c d).2 + (act i j c' d').2) := by
  decide +kernel

theorem act_act : ∀ (i j k l : Fin 2) (c d : Fin 4),
    act i j (act k l c d).1 (act k l c d).2 = act (i + k) (j + l) c d := by
  decide +kernel

theorem act_zero_args : ∀ (i j : Fin 2), act i j 0 0 = (0, 0) := by decide +kernel

theorem act_zero : ∀ (c d : Fin 4), act 0 0 c d = (c, d) := by decide +kernel

theorem mul_assoc' (g h k : M12Mod) : g * h * k = g * (h * k) := by
  obtain ⟨a1, b1, i1, j1⟩ := g
  obtain ⟨a2, b2, i2, j2⟩ := h
  obtain ⟨a3, b3, i3, j3⟩ := k
  have h1 := act_add i1 j1 a2 b2 (act i2 j2 a3 b3).1 (act i2 j2 a3 b3).2
  have h2 := act_act i1 j1 i2 j2 a3 b3
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  show mul (mul ⟨a1, b1, i1, j1⟩ ⟨a2, b2, i2, j2⟩) ⟨a3, b3, i3, j3⟩ =
    mul ⟨a1, b1, i1, j1⟩ (mul ⟨a2, b2, i2, j2⟩ ⟨a3, b3, i3, j3⟩)
  simp only [mul]
  rw [h2] at e1 e2
  simp only [e1, e2, add_assoc]

theorem one_mul' (g : M12Mod) : 1 * g = g := by
  obtain ⟨a, b, i, j⟩ := g
  show mul ⟨0, 0, 0, 0⟩ ⟨a, b, i, j⟩ = ⟨a, b, i, j⟩
  simp [mul, act_zero]

theorem mul_one' (g : M12Mod) : g * 1 = g := by
  obtain ⟨a, b, i, j⟩ := g
  show mul ⟨a, b, i, j⟩ ⟨0, 0, 0, 0⟩ = ⟨a, b, i, j⟩
  simp [mul, act_zero_args]

theorem inv_mul_cancel_aux :
    ∀ (a b : Fin 4) (i j : Fin 2), mul (inv ⟨a, b, i, j⟩) ⟨a, b, i, j⟩ = ⟨0, 0, 0, 0⟩ := by
  decide +kernel

instance : Group M12Mod where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := fun ⟨a, b, i, j⟩ => inv_mul_cancel_aux a b i j

@[expose] def equivProd : M12Mod ≃ Fin 4 × Fin 4 × Fin 2 × Fin 2 where
  toFun g := (g.a, g.b, g.i, g.j)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_eq : Nat.card M12Mod = 64 := by
  rw [Nat.card_congr equivProd]
  simp [Nat.card_eq_fintype_card]

@[expose] def mx₁ : M12Mod := ⟨1, 0, 0, 0⟩

@[expose] def mx₂ : M12Mod := ⟨0, 1, 0, 0⟩

@[expose] def mlam : M12Mod := ⟨0, 0, 1, 0⟩

@[expose] def mtau : M12Mod := ⟨0, 0, 0, 1⟩

private theorem pow_mx₁_fin (k : Fin 4) : mx₁ ^ k.val = ⟨k, 0, 0, 0⟩ := by
  fin_cases k <;> decide +kernel

private theorem pow_mx₂_fin (k : Fin 4) : mx₂ ^ k.val = ⟨0, k, 0, 0⟩ := by
  fin_cases k <;> decide +kernel

private theorem pow_mlam_fin (k : Fin 2) : mlam ^ k.val = ⟨0, 0, k, 0⟩ := by
  fin_cases k <;> decide +kernel

private theorem pow_mtau_fin (k : Fin 2) : mtau ^ k.val = ⟨0, 0, 0, k⟩ := by
  fin_cases k <;> decide +kernel

private theorem mul_components : ∀ (a b : Fin 4) (i j : Fin 2),
    (⟨a, 0, 0, 0⟩ : M12Mod) * ⟨0, b, 0, 0⟩ * ⟨0, 0, i, 0⟩ * ⟨0, 0, 0, j⟩ =
      ⟨a, b, i, j⟩ := by
  decide +kernel

theorem eq_pow_mul (g : M12Mod) :
    g = mx₁ ^ g.a.val * mx₂ ^ g.b.val * mlam ^ g.i.val * mtau ^ g.j.val := by
  obtain ⟨a, b, i, j⟩ := g
  rw [pow_mx₁_fin a, pow_mx₂_fin b, pow_mlam_fin i, pow_mtau_fin j]
  exact (mul_components a b i j).symm

end M12Mod

variable {G : Type*} [Group G] {x₁ x₂ lam tau : G}

theorem M12Rel.exists_embedding (h : M12Rel x₁ x₂ lam tau) :
    ∃ φ : M12Mod →* G, Function.Injective φ ∧ φ.range = m12Grp x₁ x₂ lam tau ∧
      φ M12Mod.mx₁ = x₁ ∧ φ M12Mod.mx₂ = x₂ ∧ φ M12Mod.mlam = lam ∧ φ M12Mod.mtau = tau := by
  have hx1_4 : x₁ ^ 4 = 1 := by rw [← h.ord_x₁]; exact pow_orderOf_eq_one x₁
  have hx2_4 : x₂ ^ 4 = 1 := by rw [← h.ord_x₂]; exact pow_orderOf_eq_one x₂
  have hlam_2 : lam ^ 2 = 1 := by rw [← h.ord_lam]; exact pow_orderOf_eq_one lam
  have htau_2 : tau ^ 2 = 1 := by rw [← h.ord_tau]; exact pow_orderOf_eq_one tau
  have hlam_inv : lam⁻¹ = lam :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hlam_2)
  have htau_inv : tau⁻¹ = tau :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact htau_2)
  have hcomm_x : Commute x₁ x₂ := h.comm
  have hcomm_lt : Commute lam tau := h.comm_lam_tau
  have hconj_lam_x1 : lam * x₁ * lam⁻¹ = x₂ := h.conj_x₁
  have hconj_lam_x2 : lam * x₂ * lam⁻¹ = x₁ := by
    have hll : lam * lam = 1 := by rw [← pow_two]; exact hlam_2
    rw [← h.conj_x₁, hlam_inv]
    calc lam * (lam * x₁ * lam) * lam = (lam * lam) * x₁ * (lam * lam) := by group
      _ = x₁ := by rw [hll, one_mul, mul_one]
  have pow_x1_mod : ∀ n : ℕ, x₁ ^ n = x₁ ^ (n % 4) := by
    intro n
    rw [← h.ord_x₁]
    exact (pow_mod_orderOf x₁ n).symm
  have pow_x2_mod : ∀ n : ℕ, x₂ ^ n = x₂ ^ (n % 4) := by
    intro n
    rw [← h.ord_x₂]
    exact (pow_mod_orderOf x₂ n).symm
  have pow_lam_mod : ∀ n : ℕ, lam ^ n = lam ^ (n % 2) := by
    intro n
    rw [← h.ord_lam]
    exact (pow_mod_orderOf lam n).symm
  have pow_tau_mod : ∀ n : ℕ, tau ^ n = tau ^ (n % 2) := by
    intro n
    rw [← h.ord_tau]
    exact (pow_mod_orderOf tau n).symm
  have hx1_inv : x₁⁻¹ = x₁ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']; exact hx1_4
  have hx2_inv : x₂⁻¹ = x₂ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']; exact hx2_4
  have hx1_ne_one : x₁ ≠ 1 := by
    intro h1
    have h1' : orderOf x₁ = 1 := by rw [h1, orderOf_one]
    rw [h.ord_x₁] at h1'
    norm_num at h1'
  have hx1_notin_z2 : x₁ ∉ zpowers x₂ := by
    intro hmem
    have hmem' : x₁ ∈ zpowers x₁ ⊓ zpowers x₂ := ⟨Subgroup.mem_zpowers x₁, hmem⟩
    rw [h.inf_eq_bot] at hmem'
    exact hx1_ne_one (Subgroup.mem_bot.mp hmem')
  have hx1_sq_ne_one : x₁ ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (x := x₁) (n := 2) (by norm_num) (by rw [h.ord_x₁]; norm_num)
  have hcontra_x2 : x₁ = x₂ → False := by
    intro heq; apply hx1_notin_z2; rw [heq]; exact Subgroup.mem_zpowers x₂
  have hcontra_x1inv : x₁ = x₁ ^ 3 → False := by
    intro heq; apply hx1_sq_ne_one
    calc x₁ ^ 2 = x₁ * x₁ := by rw [pow_two]
      _ = x₁ ^ 3 * x₁ := by rw [← heq]
      _ = x₁ ^ 4 := by rw [← pow_succ]
      _ = 1 := hx1_4
  have hcontra_x2inv : x₁ = x₂ ^ 3 → False := by
    intro heq; apply hx1_notin_z2; rw [heq]; exact Subgroup.npow_mem_zpowers x₂ 3
  have hact_x1_00 : M12Mod.act (0 : Fin 2) (0 : Fin 2) (1 : Fin 4) (0 : Fin 4) = (1, 0) := by
    decide +kernel
  have hact_x1_01 : M12Mod.act (0 : Fin 2) (1 : Fin 2) (1 : Fin 4) (0 : Fin 4) = (3, 0) := by
    decide +kernel
  have hact_x1_10 : M12Mod.act (1 : Fin 2) (0 : Fin 2) (1 : Fin 4) (0 : Fin 4) = (0, 1) := by
    decide +kernel
  have hact_x1_11 : M12Mod.act (1 : Fin 2) (1 : Fin 2) (1 : Fin 4) (0 : Fin 4) = (0, 3) := by
    decide +kernel
  have hact_x2_00 : M12Mod.act (0 : Fin 2) (0 : Fin 2) (0 : Fin 4) (1 : Fin 4) = (0, 1) := by
    decide +kernel
  have hact_x2_01 : M12Mod.act (0 : Fin 2) (1 : Fin 2) (0 : Fin 4) (1 : Fin 4) = (0, 3) := by
    decide +kernel
  have hact_x2_10 : M12Mod.act (1 : Fin 2) (0 : Fin 2) (0 : Fin 4) (1 : Fin 4) = (1, 0) := by
    decide +kernel
  have hact_x2_11 : M12Mod.act (1 : Fin 2) (1 : Fin 2) (0 : Fin 4) (1 : Fin 4) = (3, 0) := by
    decide +kernel
  have conj_sigma_x1 : ∀ i j : Fin 2,
      (lam ^ i.val * tau ^ j.val) * x₁ * (lam ^ i.val * tau ^ j.val)⁻¹ =
        x₁ ^ (M12Mod.act i j 1 0).1.val * x₂ ^ (M12Mod.act i j 1 0).2.val := by
    intro i j
    have hcases : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 1 ∧ j = 1) := by
      revert i j; decide +kernel
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hact_x1_00]; simp
    · rw [hact_x1_01]; simp [h.tau_x₁, hx1_inv]
    · rw [hact_x1_10]; simp [h.conj_x₁]
    · rw [hact_x1_11]
      simp only [Fin.val_one, pow_one]
      have e1 : lam * tau * x₁ * (lam * tau)⁻¹ =
          lam * (tau * x₁ * tau⁻¹) * lam⁻¹ := by group
      rw [e1, h.tau_x₁]
      have e2 : lam * x₁⁻¹ * lam⁻¹ = (lam * x₁ * lam⁻¹)⁻¹ := by group
      rw [e2, h.conj_x₁, hx2_inv]
      simp
  have conj_sigma_x2 : ∀ i j : Fin 2,
      (lam ^ i.val * tau ^ j.val) * x₂ * (lam ^ i.val * tau ^ j.val)⁻¹ =
        x₁ ^ (M12Mod.act i j 0 1).1.val * x₂ ^ (M12Mod.act i j 0 1).2.val := by
    intro i j
    have hcases : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 1 ∧ j = 1) := by
      revert i j; decide +kernel
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hact_x2_00]; simp
    · rw [hact_x2_01]; simp [h.tau_x₂, hx2_inv]
    · rw [hact_x2_10]; simp [hconj_lam_x2]
    · rw [hact_x2_11]
      simp only [Fin.val_one, pow_one]
      have e1 : lam * tau * x₂ * (lam * tau)⁻¹ =
          lam * (tau * x₂ * tau⁻¹) * lam⁻¹ := by group
      rw [e1, h.tau_x₂]
      have e2 : lam * x₂⁻¹ * lam⁻¹ = (lam * x₂ * lam⁻¹)⁻¹ := by group
      rw [e2, hconj_lam_x2, hx1_inv]
      simp
  have act_lin1 : ∀ (i j : Fin 2) (c d : Fin 4),
      (M12Mod.act i j c d).1.val =
        ((M12Mod.act i j 1 0).1.val * c.val +
          (M12Mod.act i j 0 1).1.val * d.val) % 4 := by
    decide +kernel
  have act_lin2 : ∀ (i j : Fin 2) (c d : Fin 4),
      (M12Mod.act i j c d).2.val =
        ((M12Mod.act i j 1 0).2.val * c.val +
          (M12Mod.act i j 0 1).2.val * d.val) % 4 := by
    decide +kernel
  have conj_sigma : ∀ (i j : Fin 2) (c d : Fin 4),
      (lam ^ i.val * tau ^ j.val) * (x₁ ^ c.val * x₂ ^ d.val) *
          (lam ^ i.val * tau ^ j.val)⁻¹ =
        x₁ ^ (M12Mod.act i j c d).1.val * x₂ ^ (M12Mod.act i j c d).2.val := by
    intro i j c d
    have h1 : (lam ^ i.val * tau ^ j.val) * (x₁ ^ c.val * x₂ ^ d.val) *
        (lam ^ i.val * tau ^ j.val)⁻¹ =
          MulAut.conj (lam ^ i.val * tau ^ j.val) (x₁ ^ c.val * x₂ ^ d.val) := by
      rw [MulAut.conj_apply]
    rw [h1, map_mul, map_pow, map_pow]
    rw [show MulAut.conj (lam ^ i.val * tau ^ j.val) x₁ =
          x₁ ^ (M12Mod.act i j 1 0).1.val * x₂ ^ (M12Mod.act i j 1 0).2.val from by
        rw [MulAut.conj_apply]; exact conj_sigma_x1 i j,
        show MulAut.conj (lam ^ i.val * tau ^ j.val) x₂ =
          x₁ ^ (M12Mod.act i j 0 1).1.val * x₂ ^ (M12Mod.act i j 0 1).2.val from by
        rw [MulAut.conj_apply]; exact conj_sigma_x2 i j]
    have hpow1 : (x₁ ^ (M12Mod.act i j 1 0).1.val *
        x₂ ^ (M12Mod.act i j 1 0).2.val) ^ c.val =
        x₁ ^ ((M12Mod.act i j 1 0).1.val * c.val) *
          x₂ ^ ((M12Mod.act i j 1 0).2.val * c.val) := by
      rw [(hcomm_x.pow_pow (M12Mod.act i j 1 0).1.val
        (M12Mod.act i j 1 0).2.val).mul_pow]
      group
    have hpow2 : (x₁ ^ (M12Mod.act i j 0 1).1.val *
        x₂ ^ (M12Mod.act i j 0 1).2.val) ^ d.val =
        x₁ ^ ((M12Mod.act i j 0 1).1.val * d.val) *
          x₂ ^ ((M12Mod.act i j 0 1).2.val * d.val) := by
      rw [(hcomm_x.pow_pow (M12Mod.act i j 0 1).1.val
        (M12Mod.act i j 0 1).2.val).mul_pow]
      group
    rw [hpow1, hpow2]
    rw [show x₁ ^ ((M12Mod.act i j 1 0).1.val * c.val) *
            x₂ ^ ((M12Mod.act i j 1 0).2.val * c.val) *
            (x₁ ^ ((M12Mod.act i j 0 1).1.val * d.val) *
              x₂ ^ ((M12Mod.act i j 0 1).2.val * d.val)) =
          x₁ ^ ((M12Mod.act i j 1 0).1.val * c.val) *
            (x₂ ^ ((M12Mod.act i j 1 0).2.val * c.val) *
              x₁ ^ ((M12Mod.act i j 0 1).1.val * d.val)) *
            x₂ ^ ((M12Mod.act i j 0 1).2.val * d.val) from by group]
    rw [show x₂ ^ ((M12Mod.act i j 1 0).2.val * c.val) *
            x₁ ^ ((M12Mod.act i j 0 1).1.val * d.val) =
          x₁ ^ ((M12Mod.act i j 0 1).1.val * d.val) *
            x₂ ^ ((M12Mod.act i j 1 0).2.val * c.val) from
        (hcomm_x.pow_pow ((M12Mod.act i j 0 1).1.val * d.val)
          ((M12Mod.act i j 1 0).2.val * c.val)).symm.eq]
    rw [show x₁ ^ ((M12Mod.act i j 1 0).1.val * c.val) *
            (x₁ ^ ((M12Mod.act i j 0 1).1.val * d.val) *
              x₂ ^ ((M12Mod.act i j 1 0).2.val * c.val)) *
            x₂ ^ ((M12Mod.act i j 0 1).2.val * d.val) =
          (x₁ ^ ((M12Mod.act i j 1 0).1.val * c.val) *
            x₁ ^ ((M12Mod.act i j 0 1).1.val * d.val)) *
          (x₂ ^ ((M12Mod.act i j 1 0).2.val * c.val) *
            x₂ ^ ((M12Mod.act i j 0 1).2.val * d.val)) from by group]
    rw [← pow_add, ← pow_add,
        pow_x1_mod ((M12Mod.act i j 1 0).1.val * c.val +
          (M12Mod.act i j 0 1).1.val * d.val),
        act_lin1 i j c d,
        pow_x2_mod ((M12Mod.act i j 1 0).2.val * c.val +
          (M12Mod.act i j 0 1).2.val * d.val),
        act_lin2 i j c d]
  have sigma_mul : ∀ (i j k l : Fin 2),
      (lam ^ i.val * tau ^ j.val) * (lam ^ k.val * tau ^ l.val) =
        lam ^ (i + k).val * tau ^ (j + l).val := by
    intro i j k l
    have h1 : lam ^ i.val * lam ^ k.val = lam ^ (i + k).val := by
      rw [← pow_add, Fin.val_add, pow_lam_mod]
    have h2 : tau ^ j.val * tau ^ l.val = tau ^ (j + l).val := by
      rw [← pow_add, Fin.val_add, pow_tau_mod]
    have hswap : tau ^ j.val * lam ^ k.val = lam ^ k.val * tau ^ j.val :=
      (hcomm_lt.pow_pow k.val j.val).symm.eq
    calc (lam ^ i.val * tau ^ j.val) * (lam ^ k.val * tau ^ l.val)
        = lam ^ i.val * (tau ^ j.val * lam ^ k.val) * tau ^ l.val := by group
      _ = lam ^ i.val * (lam ^ k.val * tau ^ j.val) * tau ^ l.val := by rw [hswap]
      _ = (lam ^ i.val * lam ^ k.val) * (tau ^ j.val * tau ^ l.val) := by group
      _ = lam ^ (i + k).val * tau ^ (j + l).val := by rw [h1, h2]
  have combine_ab : ∀ (a b : Fin 4) (i j : Fin 2) (c d : Fin 4),
      (x₁ ^ a.val * x₂ ^ b.val) *
          (x₁ ^ (M12Mod.act i j c d).1.val * x₂ ^ (M12Mod.act i j c d).2.val) =
        x₁ ^ (a + (M12Mod.act i j c d).1).val *
          x₂ ^ (b + (M12Mod.act i j c d).2).val := by
    intro a b i j c d
    have e1 : x₁ ^ (a + (M12Mod.act i j c d).1).val =
        x₁ ^ (a.val + (M12Mod.act i j c d).1.val) := by
      rw [Fin.val_add, ← pow_x1_mod]
    have e2 : x₂ ^ (b + (M12Mod.act i j c d).2).val =
        x₂ ^ (b.val + (M12Mod.act i j c d).2.val) := by
      rw [Fin.val_add, ← pow_x2_mod]
    rw [e1, e2]
    have hcx : x₂ ^ b.val * x₁ ^ (M12Mod.act i j c d).1.val =
        x₁ ^ (M12Mod.act i j c d).1.val * x₂ ^ b.val :=
      (hcomm_x.pow_pow (M12Mod.act i j c d).1.val b.val).symm.eq
    calc (x₁ ^ a.val * x₂ ^ b.val) *
            (x₁ ^ (M12Mod.act i j c d).1.val * x₂ ^ (M12Mod.act i j c d).2.val)
        = x₁ ^ a.val * (x₂ ^ b.val * x₁ ^ (M12Mod.act i j c d).1.val) *
            x₂ ^ (M12Mod.act i j c d).2.val := by group
      _ = x₁ ^ a.val * (x₁ ^ (M12Mod.act i j c d).1.val * x₂ ^ b.val) *
            x₂ ^ (M12Mod.act i j c d).2.val := by rw [hcx]
      _ = (x₁ ^ a.val * x₁ ^ (M12Mod.act i j c d).1.val) *
            (x₂ ^ b.val * x₂ ^ (M12Mod.act i j c d).2.val) := by group
      _ = x₁ ^ (a.val + (M12Mod.act i j c d).1.val) *
            x₂ ^ (b.val + (M12Mod.act i j c d).2.val) := by rw [← pow_add, ← pow_add]
  let phiFun : M12Mod → G := fun g =>
    x₁ ^ g.a.val * x₂ ^ g.b.val * lam ^ g.i.val * tau ^ g.j.val
  have hmap : ∀ g g' : M12Mod, phiFun (g * g') = phiFun g * phiFun g' := by
    intro g g'
    obtain ⟨a, b, i, j⟩ := g
    obtain ⟨c, d, k, l⟩ := g'
    show x₁ ^ (a + (M12Mod.act i j c d).1).val * x₂ ^ (b + (M12Mod.act i j c d).2).val *
          lam ^ (i + k).val * tau ^ (j + l).val =
        x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val * tau ^ j.val *
          (x₁ ^ c.val * x₂ ^ d.val * lam ^ k.val * tau ^ l.val)
    have key : (x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val * tau ^ j.val) *
          (x₁ ^ c.val * x₂ ^ d.val * lam ^ k.val * tau ^ l.val) =
        x₁ ^ (a + (M12Mod.act i j c d).1).val * x₂ ^ (b + (M12Mod.act i j c d).2).val *
          lam ^ (i + k).val * tau ^ (j + l).val := by
      calc (x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val * tau ^ j.val) *
            (x₁ ^ c.val * x₂ ^ d.val * lam ^ k.val * tau ^ l.val)
          = (x₁ ^ a.val * x₂ ^ b.val) *
              ((lam ^ i.val * tau ^ j.val) * (x₁ ^ c.val * x₂ ^ d.val) *
                (lam ^ i.val * tau ^ j.val)⁻¹) *
              ((lam ^ i.val * tau ^ j.val) * (lam ^ k.val * tau ^ l.val)) := by group
        _ = (x₁ ^ a.val * x₂ ^ b.val) *
              (x₁ ^ (M12Mod.act i j c d).1.val * x₂ ^ (M12Mod.act i j c d).2.val) *
              (lam ^ (i + k).val * tau ^ (j + l).val) := by
              rw [conj_sigma i j c d, sigma_mul i j k l]
        _ = (x₁ ^ (a + (M12Mod.act i j c d).1).val *
              x₂ ^ (b + (M12Mod.act i j c d).2).val) *
              (lam ^ (i + k).val * tau ^ (j + l).val) := by rw [combine_ab a b i j c d]
        _ = x₁ ^ (a + (M12Mod.act i j c d).1).val *
              x₂ ^ (b + (M12Mod.act i j c d).2).val *
              lam ^ (i + k).val * tau ^ (j + l).val := by group
    exact key.symm
  let φ : M12Mod →* G := MonoidHom.mk' phiFun hmap
  have φ_apply : ∀ g : M12Mod,
      φ g = x₁ ^ g.a.val * x₂ ^ g.b.val * lam ^ g.i.val * tau ^ g.j.val := fun g => rfl
  have φ_mx₁ : φ M12Mod.mx₁ = x₁ := by rw [φ_apply]; simp [M12Mod.mx₁]
  have φ_mx₂ : φ M12Mod.mx₂ = x₂ := by rw [φ_apply]; simp [M12Mod.mx₂]
  have φ_mlam : φ M12Mod.mlam = lam := by rw [φ_apply]; simp [M12Mod.mlam]
  have φ_mtau : φ M12Mod.mtau = tau := by rw [φ_apply]; simp [M12Mod.mtau]
  have hrange : φ.range = m12Grp x₁ x₂ lam tau := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨g, rfl⟩ := hy
      rw [φ_apply]
      have h1 : x₁ ∈ m12Grp x₁ x₂ lam tau := Subgroup.subset_closure (by simp)
      have h2 : x₂ ∈ m12Grp x₁ x₂ lam tau := Subgroup.subset_closure (by simp)
      have hi : lam ∈ m12Grp x₁ x₂ lam tau := Subgroup.subset_closure (by simp)
      have hj : tau ∈ m12Grp x₁ x₂ lam tau := Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ h1 g.a.val) (Subgroup.pow_mem _ h2 g.b.val))
        (Subgroup.pow_mem _ hi g.i.val)) (Subgroup.pow_mem _ hj g.j.val)
    · rw [m12Grp, Subgroup.closure_le]
      rintro s (rfl | rfl | rfl | rfl)
      · exact ⟨M12Mod.mx₁, φ_mx₁⟩
      · exact ⟨M12Mod.mx₂, φ_mx₂⟩
      · exact ⟨M12Mod.mlam, φ_mlam⟩
      · exact ⟨M12Mod.mtau, φ_mtau⟩
  have hinj : Function.Injective φ := by
    intro g g' hgg0
    obtain ⟨a, b, i, j⟩ := g
    obtain ⟨a', b', i', j'⟩ := g'
    have hgg : x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val * tau ^ j.val =
        x₁ ^ a'.val * x₂ ^ b'.val * lam ^ i'.val * tau ^ j'.val := by
      simpa only [φ_apply] using hgg0
    set p : Fin 2 := i + i' with hpdef
    set q : Fin 2 := j + j' with hqdef
    set U : G := (lam ^ i.val * tau ^ j.val) * (lam ^ i'.val * tau ^ j'.val)⁻¹ with hUdef
    have hU_sigma : U = lam ^ p.val * tau ^ q.val := by
      rw [hUdef]
      have hσ'inv : (lam ^ i'.val * tau ^ j'.val)⁻¹ = lam ^ i'.val * tau ^ j'.val := by
        rw [mul_inv_rev, ← inv_pow, ← inv_pow, hlam_inv, htau_inv]
        exact (hcomm_lt.pow_pow i'.val j'.val).symm.eq
      rw [hσ'inv, sigma_mul i j i' j', hpdef, hqdef]
    have hU_eq : U = (x₁ ^ a.val * x₂ ^ b.val)⁻¹ * (x₁ ^ a'.val * x₂ ^ b'.val) := by
      rw [hUdef]
      calc (lam ^ i.val * tau ^ j.val) * (lam ^ i'.val * tau ^ j'.val)⁻¹
          = (x₁ ^ a.val * x₂ ^ b.val)⁻¹ *
              ((x₁ ^ a.val * x₂ ^ b.val) *
                ((lam ^ i.val * tau ^ j.val) * (lam ^ i'.val * tau ^ j'.val)⁻¹)) := by
            group
        _ = (x₁ ^ a.val * x₂ ^ b.val)⁻¹ *
              ((x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val * tau ^ j.val) *
                (lam ^ i'.val * tau ^ j'.val)⁻¹) := by group
        _ = (x₁ ^ a.val * x₂ ^ b.val)⁻¹ *
              ((x₁ ^ a'.val * x₂ ^ b'.val * lam ^ i'.val * tau ^ j'.val) *
                (lam ^ i'.val * tau ^ j'.val)⁻¹) := by rw [hgg]
        _ = (x₁ ^ a.val * x₂ ^ b.val)⁻¹ * (x₁ ^ a'.val * x₂ ^ b'.val) := by group
    have hP : Commute x₁ (x₁ ^ a.val * x₂ ^ b.val) :=
      ((Commute.refl x₁).pow_right a.val).mul_right (hcomm_x.pow_right b.val)
    have hQ : Commute x₁ (x₁ ^ a'.val * x₂ ^ b'.val) :=
      ((Commute.refl x₁).pow_right a'.val).mul_right (hcomm_x.pow_right b'.val)
    have hU_comm : Commute x₁ U := by
      rw [hU_eq]
      exact hP.inv_right.mul_right hQ
    have hUx1 : U * x₁ * U⁻¹ = x₁ := by
      rw [hU_comm.eq.symm]
      group
    have hEq : x₁ = x₁ ^ (M12Mod.act p q 1 0).1.val * x₂ ^ (M12Mod.act p q 1 0).2.val := by
      have hc := conj_sigma p q 1 0
      simp only [Fin.val_one, Fin.val_zero, pow_one, pow_zero, mul_one] at hc
      rw [← hU_sigma] at hc
      rw [hUx1] at hc
      exact hc
    have key : ∀ p q : Fin 2, M12Mod.act p q 1 0 = (1, 0) → p = 0 ∧ q = 0 := by
      decide +kernel
    have hcases : ∀ p q : Fin 2, M12Mod.act p q 1 0 = (1, 0) ∨
        M12Mod.act p q 1 0 = (0, 1) ∨ M12Mod.act p q 1 0 = (3, 0) ∨
        M12Mod.act p q 1 0 = (0, 3) := by
      decide +kernel
    have hpq : p = 0 ∧ q = 0 := by
      rcases hcases p q with hc | hc | hc | hc
      · exact key p q hc
      · exfalso; apply hcontra_x2; rw [hc] at hEq; simpa using hEq
      · exfalso; apply hcontra_x1inv; rw [hc] at hEq; simpa using hEq
      · exfalso; apply hcontra_x2inv; rw [hc] at hEq; simpa using hEq
    have hi : i = i' := by
      have hsum : i + i' = 0 := by rw [← hpdef]; exact hpq.1
      have key2 : ∀ i i' : Fin 2, i + i' = 0 → i = i' := by decide +kernel
      exact key2 i i' hsum
    have hj : j = j' := by
      have hsum : j + j' = 0 := by rw [← hqdef]; exact hpq.2
      have key3 : ∀ j j' : Fin 2, j + j' = 0 → j = j' := by decide +kernel
      exact key3 j j' hsum
    have hPQ : x₁ ^ a.val * x₂ ^ b.val = x₁ ^ a'.val * x₂ ^ b'.val := by
      have hgg2 := hgg
      rw [hi, hj] at hgg2
      exact mul_right_cancel (mul_right_cancel hgg2)
    have huv : x₁ ^ a.val * (x₁ ^ a'.val)⁻¹ = x₂ ^ b'.val * (x₂ ^ b.val)⁻¹ := by
      have h1 : (x₁ ^ a'.val)⁻¹ * (x₁ ^ a.val * x₂ ^ b.val) = x₂ ^ b'.val := by
        rw [hPQ, ← mul_assoc, inv_mul_cancel, one_mul]
      have h2 : (x₁ ^ a'.val)⁻¹ * x₁ ^ a.val = x₂ ^ b'.val * (x₂ ^ b.val)⁻¹ := by
        rw [← h1]; group
      rw [((Commute.refl x₁).pow_pow a.val a'.val).inv_right.eq.symm] at h2
      exact h2
    have hu_mem : x₁ ^ a.val * (x₁ ^ a'.val)⁻¹ ∈ zpowers x₁ :=
      Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers x₁ a.val)
        (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x₁ a'.val))
    have hv_mem : x₂ ^ b'.val * (x₂ ^ b.val)⁻¹ ∈ zpowers x₂ :=
      Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers x₂ b'.val)
        (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x₂ b.val))
    have hu1 : x₁ ^ a.val * (x₁ ^ a'.val)⁻¹ = 1 := by
      have hmem : x₁ ^ a.val * (x₁ ^ a'.val)⁻¹ ∈ zpowers x₁ ⊓ zpowers x₂ :=
        ⟨hu_mem, by rw [huv]; exact hv_mem⟩
      rw [h.inf_eq_bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hpoweq : x₁ ^ a.val = x₁ ^ a'.val := eq_of_mul_inv_eq_one hu1
    have ha : a = a' := by
      apply Fin.ext
      exact pow_injOn_Iio_orderOf (x := x₁)
        (by rw [h.ord_x₁]; exact a.isLt) (by rw [h.ord_x₁]; exact a'.isLt) hpoweq
    have hv1 : x₂ ^ b'.val * (x₂ ^ b.val)⁻¹ = 1 := by
      rw [← huv]; exact hu1
    have hpoweq2 : x₂ ^ b.val = x₂ ^ b'.val := (eq_of_mul_inv_eq_one hv1).symm
    have hb : b = b' := by
      apply Fin.ext
      exact pow_injOn_Iio_orderOf (x := x₂)
        (by rw [h.ord_x₂]; exact b.isLt) (by rw [h.ord_x₂]; exact b'.isLt) hpoweq2
    rw [ha, hb, hi, hj]
  exact ⟨φ, hinj, hrange, φ_mx₁, φ_mx₂, φ_mlam, φ_mtau⟩

theorem M12Rel.card_m12Grp (h : M12Rel x₁ x₂ lam tau) :
    Nat.card (m12Grp x₁ x₂ lam tau) = 64 := by
  obtain ⟨φ, hφinj, hφrange, -⟩ := M12Rel.exists_embedding h
  rw [← hφrange, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
  exact M12Mod.card_eq

end CFSG.OddStandard.SmallF3.HarrisU33
