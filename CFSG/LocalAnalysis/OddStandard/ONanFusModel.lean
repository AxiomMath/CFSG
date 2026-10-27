module

public import CFSG.LocalAnalysis.OddStandard.ONanSylowFacts

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model

theorem invE_d_zero_iff : ∀ i : Fin 7, (invE i).d = 0 ↔ i.val ≤ 2 := by decide

theorem dmul_zero_right : ∀ a : Fin 8, dmul a 0 = a := by decide

theorem ck_zero_right : ∀ a : Fin 8, ck a 0 = 0 := by decide

theorem v0_mul (a b : AlpE) : (a * b).v0 = a.v0 + act a.d 0 b + ck a.d b.d := rfl

theorem v1_mul (a b : AlpE) : (a * b).v1 = a.v1 + act a.d 1 b := rfl

theorem v2_mul (a b : AlpE) : (a * b).v2 = a.v2 + act a.d 2 b + ck a.d b.d := rfl

theorem act_zero (i : Fin 3) (g : AlpE) : act 0 i g = ![g.v0, g.v1, g.v2] i := by
  fin_cases i <;> simp [act, me_zero]

theorem mul_comm_iff_of_d_zero (g y : AlpE) (hy : y.d = 0) :
    g * y = y * g ↔ ∀ i : Fin 3, act g.d i y = ![y.v0, y.v1, y.v2] i := by
  constructor
  · intro h i
    have h0 := congrArg AlpE.v0 h
    have h1 := congrArg AlpE.v1 h
    have h2 := congrArg AlpE.v2 h
    rw [v0_mul, v0_mul, hy, ck_zero_right, ck_zero_left, act_zero] at h0
    rw [v1_mul, v1_mul, hy, act_zero] at h1
    rw [v2_mul, v2_mul, hy, ck_zero_right, ck_zero_left, act_zero] at h2
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero] at h0 ⊢
      simpa [add_comm] using h0
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at h1 ⊢
      simpa [add_comm] using h1
    · simp only [Fin.reduceFinMk, Matrix.cons_val] at h2 ⊢
      simpa [add_comm] using h2
  · intro h
    apply AlpE.ext
    · rw [mul_d, mul_d, hy, dmul_zero_right, dmul_zero_left]
    · rw [v0_mul, v0_mul, hy, ck_zero_right, ck_zero_left, act_zero, h 0]
      simp [add_comm]
    · rw [v1_mul, v1_mul, hy, act_zero, h 1]
      simp [add_comm]
    · rw [v2_mul, v2_mul, hy, ck_zero_right, ck_zero_left, act_zero, h 2]
      simp [add_comm]

theorem card_stab_le_two : ∀ y : AlpE, y.d = 0 → y * y ≠ 1 → y * y ≠ zc →
    (Finset.univ.filter fun d : Fin 8 =>
      ∀ i : Fin 3, act d i y = ![y.v0, y.v1, y.v2] i).card ≤ 2 := by
  decide +kernel

theorem card_centralizer_le_128 {y : AlpE} (hy : y.d = 0) (h1 : y * y ≠ 1) (hz : y * y ≠ zc) :
    Nat.card (Subgroup.centralizer ({y} : Set AlpE)) ≤ 128 := by
  set Sd := Finset.univ.filter fun d : Fin 8 => ∀ i : Fin 3, act d i y = ![y.v0, y.v1, y.v2] i
    with hSd
  have hS : Sd.card ≤ 2 := card_stab_le_two y hy h1 hz
  have hmem : ∀ g : Subgroup.centralizer ({y} : Set AlpE), g.1.d ∈ Sd := by
    intro g
    have := Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [hSd, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (mul_comm_iff_of_d_zero g.1 y hy).1 this⟩
  let f : Subgroup.centralizer ({y} : Set AlpE) → Sd × (ZMod 4 × ZMod 4 × ZMod 4) :=
    fun g => (⟨g.1.d, hmem g⟩, (g.1.v0, g.1.v1, g.1.v2))
  have hf : Function.Injective f := by
    intro g g' h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (AlpE.ext h.1 h.2.1 h.2.2.1 h.2.2.2)
  calc Nat.card (Subgroup.centralizer ({y} : Set AlpE))
      ≤ Nat.card (Sd × (ZMod 4 × ZMod 4 × ZMod 4)) := Nat.card_le_card_of_injective f hf
    _ = Sd.card * 64 := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe]
        simp [ZMod.card]
    _ ≤ 128 := by omega

end CFSG.OddStandard.ONanRec
