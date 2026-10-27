module

public import CFSG.GF2Type.SmithTypeE.DMod.Siegel
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open Module

abbrev W64 := Fin 64 → ZMod 2

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem two_pow_lt_64 (i : Fin 6) : 2 ^ i.val < 64 := by
  have := Nat.pow_lt_pow_right (a := 2) (by norm_num) i.isLt
  simpa using this

@[expose] def flipS (i : Fin 6) (T : Fin 64) : Fin 64 :=
  ⟨T.val ^^^ 2 ^ i.val, by
    have h1 : T.val < 2 ^ 6 := by simpa using T.isLt
    have h2 : 2 ^ i.val < 2 ^ 6 := by simpa using two_pow_lt_64 i
    simpa using Nat.xor_lt_two_pow h1 h2⟩

theorem flipS_val (i : Fin 6) (T : Fin 64) : (flipS i T).val = T.val ^^^ 2 ^ i.val := rfl

theorem flipS_flipS (i : Fin 6) (T : Fin 64) : flipS i (flipS i T) = T := by
  apply Fin.ext
  simp [flipS_val, Nat.xor_assoc]

theorem flipS_comm (i j : Fin 6) (T : Fin 64) : flipS i (flipS j T) = flipS j (flipS i T) := by
  apply Fin.ext
  simp only [flipS_val, Nat.xor_assoc, Nat.xor_comm (2 ^ j.val)]

theorem testBit_flipS (i : Fin 6) (T : Fin 64) (j : ℕ) :
    (flipS i T).val.testBit j = (T.val.testBit j ^^ decide (i.val = j)) := by
  rw [flipS_val, Nat.testBit_xor, Nat.testBit_two_pow]

theorem testBit_flipS_self (i : Fin 6) (T : Fin 64) :
    (flipS i T).val.testBit i.val = !T.val.testBit i.val := by
  rw [testBit_flipS]
  simp

theorem testBit_flipS_ne {i j : Fin 6} (h : i ≠ j) (T : Fin 64) :
    (flipS i T).val.testBit j.val = T.val.testBit j.val := by
  rw [testBit_flipS]
  have : decide (i.val = j.val) = false := decide_eq_false fun e => h (Fin.ext e)
  simp [this]

@[expose] def wedgeL (i : Fin 6) : W64 →ₗ[ZMod 2] W64 where
  toFun v T := if T.val.testBit i.val then v (flipS i T) else 0
  map_add' v w := by
    funext T
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    funext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

@[expose] def contrL (i : Fin 6) : W64 →ₗ[ZMod 2] W64 where
  toFun v T := if T.val.testBit i.val then 0 else v (flipS i T)
  map_add' v w := by
    funext T
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    funext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem wedgeL_apply (i : Fin 6) (v : W64) (T : Fin 64) :
    wedgeL i v T = if T.val.testBit i.val then v (flipS i T) else 0 := rfl

theorem contrL_apply (i : Fin 6) (v : W64) (T : Fin 64) :
    contrL i v T = if T.val.testBit i.val then 0 else v (flipS i T) := rfl

theorem wedgeL_mul_self (i : Fin 6) : wedgeL i * wedgeL i = 0 := by
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [Module.End.mul_apply, wedgeL_apply, testBit_flipS_self, LinearMap.zero_apply,
    Pi.zero_apply]
  cases T.val.testBit i.val <;> simp

theorem contrL_mul_self (i : Fin 6) : contrL i * contrL i = 0 := by
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [Module.End.mul_apply, contrL_apply, testBit_flipS_self, LinearMap.zero_apply,
    Pi.zero_apply]
  cases T.val.testBit i.val <;> simp

theorem wedgeL_anticomm (i j : Fin 6) : wedgeL i * wedgeL j + wedgeL j * wedgeL i = 0 := by
  by_cases hij : i = j
  · subst hij
    rw [wedgeL_mul_self, add_zero]
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, wedgeL_apply, testBit_flipS_ne hij,
    testBit_flipS_ne (Ne.symm hij), LinearMap.zero_apply, Pi.add_apply, Pi.zero_apply,
    flipS_comm i j]
  cases T.val.testBit i.val <;> cases T.val.testBit j.val <;> simp [zmod2_add_self]

theorem contrL_anticomm (i j : Fin 6) : contrL i * contrL j + contrL j * contrL i = 0 := by
  by_cases hij : i = j
  · subst hij
    rw [contrL_mul_self, add_zero]
  refine LinearMap.ext fun v => funext fun T => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, contrL_apply, testBit_flipS_ne hij,
    testBit_flipS_ne (Ne.symm hij), LinearMap.zero_apply, Pi.add_apply, Pi.zero_apply,
    flipS_comm i j]
  cases T.val.testBit i.val <;> cases T.val.testBit j.val <;> simp [zmod2_add_self]

theorem wedgeL_contrL_anticomm (i j : Fin 6) :
    wedgeL i * contrL j + contrL j * wedgeL i = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    refine LinearMap.ext fun v => funext fun T => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, wedgeL_apply, contrL_apply,
      testBit_flipS_self, flipS_flipS, Module.End.one_apply, Pi.add_apply]
    cases T.val.testBit i.val <;> simp
  · rw [if_neg hij]
    refine LinearMap.ext fun v => funext fun T => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, wedgeL_apply, contrL_apply,
      testBit_flipS_ne hij, testBit_flipS_ne (Ne.symm hij), LinearMap.zero_apply, Pi.add_apply,
      Pi.zero_apply, flipS_comm i j]
    cases T.val.testBit i.val <;> cases T.val.testBit j.val <;> simp [zmod2_add_self]

theorem alg_add_self (a : Module.End (ZMod 2) W64) : a + a = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) a, h2, zero_smul]

theorem alg_eq_of_add_eq {a b c : Module.End (ZMod 2) W64} (h : a + b = c) :
    a = c + b := by
  rw [← h, add_assoc, alg_add_self, add_zero]

@[expose] noncomputable def rhoL : V12 →ₗ[ZMod 2] Module.End (ZMod 2) W64 where
  toFun x := ∑ i, x.1 i • wedgeL i + ∑ i, x.2 i • contrL i
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, RingHom.id_apply, smul_add]

theorem rhoL_apply (x : V12) : rhoL x = ∑ i, x.1 i • wedgeL i + ∑ i, x.2 i • contrL i := rfl

theorem sum_smul_anticomm (a b : Fin 6 → ZMod 2) (P Q : Fin 6 → Module.End (ZMod 2) W64) :
    (∑ i, a i • P i) * (∑ j, b j • Q j) + (∑ j, b j • Q j) * (∑ i, a i • P i) =
      ∑ i, ∑ j, (a i * b j) • (P i * Q j + Q j * P i) := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, smul_add]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (b j)]

theorem rhoL_anticomm (x y : V12) : rhoL x * rhoL y + rhoL y * rhoL x = B12 x y • 1 := by
  have e : ∀ A B C D : Module.End (ZMod 2) W64, (A + B) * (C + D) + (C + D) * (A + B) =
      (A * C + C * A) + (A * D + D * A) + (B * C + C * B) + (B * D + D * B) := by
    intro A B C D
    simp only [add_mul, mul_add]
    abel
  rw [rhoL_apply, rhoL_apply, e, sum_smul_anticomm, sum_smul_anticomm, sum_smul_anticomm,
    sum_smul_anticomm]
  simp only [wedgeL_anticomm, contrL_anticomm, smul_zero, Finset.sum_const_zero, zero_add,
    add_zero]
  have hDA : ∀ i j, contrL j * wedgeL i + wedgeL i * contrL j = if i = j then 1 else 0 :=
    fun i j => by rw [add_comm]; exact wedgeL_contrL_anticomm i j
  have hBC : ∀ i j, contrL i * wedgeL j + wedgeL j * contrL i = if j = i then 1 else 0 :=
    fun i j => by rw [add_comm]; exact wedgeL_contrL_anticomm j i
  simp only [hDA, hBC, wedgeL_contrL_anticomm, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← Finset.sum_add_distrib, ← add_smul, B12, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (x.2 i)]

theorem rhoL_single_fst (i : Fin 6) : rhoL (Pi.single i 1, 0) = wedgeL i := by
  rw [rhoL_apply]
  simp [Pi.single_apply, ite_smul]

theorem rhoL_single_snd (i : Fin 6) : rhoL (0, Pi.single i 1) = contrL i := by
  rw [rhoL_apply]
  simp [Pi.single_apply, ite_smul]

theorem q12_single_fst (i : Fin 6) : q12 (Pi.single i 1, 0) = 0 := by
  simp [q12_apply]

theorem q12_single_snd (i : Fin 6) : q12 (0, Pi.single i 1) = 0 := by
  simp [q12_apply]

theorem eq_sum_singles (x : V12) :
    x = ∑ i, x.1 i • ((Pi.single i 1, 0) : V12) + ∑ i, x.2 i • ((0, Pi.single i 1) : V12) := by
  refine Prod.ext ?_ ?_
  · funext j
    simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · funext j
    simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

@[expose] noncomputable def sqDefect : V12 →+ Module.End (ZMod 2) W64 :=
  AddMonoidHom.mk' (fun x => rhoL x * rhoL x + q12 x • 1) fun x y => by
    have h := rhoL_anticomm x y
    rw [map_add, q12_add, add_mul, mul_add, mul_add, add_smul, add_smul]
    calc rhoL x * rhoL x + rhoL x * rhoL y + (rhoL y * rhoL x + rhoL y * rhoL y) +
          (q12 x • 1 + q12 y • 1 + B12 x y • (1 : Module.End (ZMod 2) W64))
        = rhoL x * rhoL x + q12 x • 1 + (rhoL y * rhoL y + q12 y • 1) +
            ((rhoL x * rhoL y + rhoL y * rhoL x) + B12 x y • 1) := by abel
      _ = _ := by rw [h, ← add_smul, zmod2_add_self, zero_smul, add_zero]

theorem sqDefect_smul (c : ZMod 2) (x : V12) (h : sqDefect x = 0) : sqDefect (c • x) = 0 := by
  rcases (by decide : ∀ d : ZMod 2, d = 0 ∨ d = 1) c with rfl | rfl
  · rw [zero_smul, map_zero]
  · rw [one_smul]
    exact h

theorem rhoL_mul_self (x : V12) : rhoL x * rhoL x = q12 x • 1 := by
  have hE : ∀ i, sqDefect ((Pi.single i 1, 0) : V12) = 0 := fun i => by
    change rhoL _ * rhoL _ + q12 _ • 1 = 0
    rw [rhoL_single_fst, wedgeL_mul_self, q12_single_fst, zero_smul, add_zero]
  have hF : ∀ i, sqDefect ((0, Pi.single i 1) : V12) = 0 := fun i => by
    change rhoL _ * rhoL _ + q12 _ • 1 = 0
    rw [rhoL_single_snd, contrL_mul_self, q12_single_snd, zero_smul, add_zero]
  have h : sqDefect x = 0 := by
    rw [eq_sum_singles x, map_add, map_sum, map_sum,
      Finset.sum_eq_zero fun i _ => sqDefect_smul _ _ (hE i),
      Finset.sum_eq_zero fun i _ => sqDefect_smul _ _ (hF i), add_zero]
  have h' : rhoL x * rhoL x + q12 x • 1 = 0 := h
  exact (alg_eq_of_add_eq h').trans (zero_add _)

section Alg

local notation "𝔼" => Module.End (ZMod 2) W64

theorem conj_one_add_mul {p q r : 𝔼} (α β : ZMod 2) (hp : p * p = 0) (hq : q * q = 0)
    (hpq : p * q + q * p = 0) (hqr : q * r + r * q = α • 1) (hpr : p * r + r * p = β • 1) :
    (1 + p * q) * r * (1 + p * q) = r + α • p + β • q := by
  have hqp : q * p = p * q := (alg_eq_of_add_eq (by rw [add_comm]; exact hpq)).trans (zero_add _)
  have hqr' : q * r = α • 1 + r * q := alg_eq_of_add_eq hqr
  have hpr' : p * r = β • 1 + r * p := alg_eq_of_add_eq hpr
  have h1 : p * q * r = α • p + β • q + r * p * q := by
    rw [mul_assoc, hqr', mul_add, mul_smul_comm, mul_one, ← mul_assoc, hpr', add_mul,
      smul_mul_assoc, one_mul, mul_assoc r]
    abel
  have hA : p * (p * q) = 0 := by rw [← mul_assoc, hp, zero_mul]
  have hB : q * (p * q) = 0 := by rw [← mul_assoc, hqp, mul_assoc, hq, mul_zero]
  have hC : p * (q * (p * q)) = 0 := by rw [hB, mul_zero]
  have h2 : p * q * r * (p * q) = 0 := by
    rw [h1]
    simp only [add_mul, smul_mul_assoc, mul_assoc, hA, hB, hC, mul_zero, smul_zero, add_zero]
  calc (1 + p * q) * r * (1 + p * q) = r + (p * q * r + r * (p * q)) + p * q * r * (p * q) := by
        noncomm_ring
    _ = r + α • p + β • q := by
        rw [h2, add_zero, h1, ← mul_assoc r p q, add_assoc (α • p + β • q), alg_add_self,
          add_zero, add_assoc]

theorem one_add_mul_sq {p q : 𝔼} (hp : p * p = 0) (hpq : p * q + q * p = 0) :
    (1 + p * q) * (1 + p * q) = 1 := by
  have hqp : q * p = p * q := (alg_eq_of_add_eq (by rw [add_comm]; exact hpq)).trans (zero_add _)
  have h : p * q * (p * q) = 0 := by
    rw [mul_assoc, ← mul_assoc q p q, hqp, mul_assoc p q q, ← mul_assoc, hp, zero_mul]
  calc (1 + p * q) * (1 + p * q) = 1 + (p * q + p * q) + p * q * (p * q) := by noncomm_ring
    _ = 1 := by rw [h, alg_add_self, add_zero, add_zero]

end Alg

@[expose] noncomputable def tlift (u w : V12) : Module.End (ZMod 2) W64 := 1 + rhoL u * rhoL w

theorem rhoL_anticomm_of_B {u w : V12} (h : B12 u w = 0) :
    rhoL u * rhoL w + rhoL w * rhoL u = 0 := by
  rw [rhoL_anticomm, h, zero_smul]

theorem rhoL_mul_self_of_q {u : V12} (h : q12 u = 0) : rhoL u * rhoL u = 0 := by
  rw [rhoL_mul_self, h, zero_smul]

theorem tlift_mul_self {u w : V12} (h : TsPair u w) : tlift u w * tlift u w = 1 :=
  one_add_mul_sq (rhoL_mul_self_of_q h.1) (rhoL_anticomm_of_B h.2.2)

theorem tlift_apply_tlift {u w : V12} (h : TsPair u w) (v : W64) : tlift u w (tlift u w v) = v := by
  have := congrArg (fun f : Module.End (ZMod 2) W64 => f v) (tlift_mul_self h)
  simpa using this

theorem tlift_swap {u w : V12} (h : TsPair u w) : tlift w u = tlift u w := by
  unfold tlift
  rw [alg_eq_of_add_eq (rhoL_anticomm_of_B h.2.2), zero_add]

theorem tlift_add_right {u w : V12} (h : TsPair u w) : tlift u (u + w) = tlift u w := by
  unfold tlift
  rw [map_add, mul_add, rhoL_mul_self_of_q h.1, zero_add]

theorem tlift_eq_of_line_eq {u w u' w' : V12} (h : TsPair u w) (h' : TsPair u' w')
    (huw : u ≠ w) (huw' : u' ≠ w')
    (e : ({u, w, u + w} : Finset V12) = {u', w', u' + w'}) : tlift u w = tlift u' w' := by
  have hu'mem : u' ∈ ({u, w, u + w} : Finset V12) := by
    rw [e]; simp
  have hw'mem : w' ∈ ({u, w, u + w} : Finset V12) := by
    rw [e]; simp
  have hwu : TsPair w u := tsPair_swap h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu'mem hw'mem
  rcases hu'mem with h1 | h1 | h1 <;> rcases hw'mem with h2 | h2 | h2 <;> subst u' w'
  · exact (huw' rfl).elim
  · rfl
  · exact (tlift_add_right h).symm
  · exact (tlift_swap h).symm
  · exact (huw' rfl).elim
  · rw [add_comm u w, tlift_add_right hwu, tlift_swap h]
  · exact (tlift_add_right h).symm.trans (tlift_swap h')
  · rw [← tlift_swap h', add_comm u w, tlift_add_right hwu, tlift_swap h]
  · exact (huw' rfl).elim

theorem tlift_rho_tlift {u w : V12} (h : TsPair u w) (x : V12) :
    tlift u w * rhoL x * tlift u w = rhoL (siegelEquiv u w x) := by
  unfold tlift
  rw [conj_one_add_mul (B12 w x) (B12 u x) (rhoL_mul_self_of_q h.1) (rhoL_mul_self_of_q h.2.1)
    (rhoL_anticomm_of_B h.2.2) (rhoL_anticomm w x) (rhoL_anticomm u x), siegelEquiv_apply h,
    map_add, map_add, map_smul, map_smul, B12_comm w x, B12_comm u x]

theorem tlift_rho_apply {u w : V12} (h : TsPair u w) (x : V12) (v : W64) :
    tlift u w (rhoL x v) = rhoL (siegelEquiv u w x) (tlift u w v) := by
  rw [← tlift_rho_tlift h x]
  simp only [Module.End.mul_apply, tlift_apply_tlift h]

theorem tlift_conj {u w : V12} (h : TsPair u w) (u' w' : V12) :
    tlift u w * tlift u' w' * tlift u w = tlift (siegelEquiv u w u') (siegelEquiv u w w') := by
  have hT := tlift_mul_self h
  have e1 : tlift u' w' = 1 + rhoL u' * rhoL w' := rfl
  have e2 : tlift (siegelEquiv u w u') (siegelEquiv u w w') =
      1 + rhoL (siegelEquiv u w u') * rhoL (siegelEquiv u w w') := rfl
  have e3 : tlift u w * rhoL u' * tlift u w * (tlift u w * rhoL w' * tlift u w) =
      tlift u w * (rhoL u' * rhoL w') * tlift u w := by
    calc tlift u w * rhoL u' * tlift u w * (tlift u w * rhoL w' * tlift u w)
        = tlift u w * rhoL u' * (tlift u w * tlift u w) * rhoL w' * tlift u w := by
          simp only [mul_assoc]
      _ = tlift u w * (rhoL u' * rhoL w') * tlift u w := by
          rw [hT, mul_one]
          simp only [mul_assoc]
  rw [e1, e2, ← tlift_rho_tlift h, ← tlift_rho_tlift h, e3, mul_add, add_mul, mul_one, hT]

theorem testBit_rev (T : Fin 64) (i : Fin 6) :
    (Fin.rev T).val.testBit i.val = !T.val.testBit i.val := by
  revert T i
  decide

theorem flipS_rev (i : Fin 6) (T : Fin 64) : flipS i (Fin.rev T) = Fin.rev (flipS i T) := by
  revert i T
  decide

@[expose] def betaVal (v w : W64) : ZMod 2 := ∑ T : Fin 64, v T * w (Fin.rev T)

@[expose] noncomputable def betaL : LinearMap.BilinForm (ZMod 2) W64 :=
  LinearMap.mk₂ (ZMod 2) betaVal
    (fun v v' w => by
      simp only [betaVal, Pi.add_apply, add_mul, ← Finset.sum_add_distrib])
    (fun c v w => by
      simp only [betaVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun v w w' => by
      simp only [betaVal, Pi.add_apply, mul_add, ← Finset.sum_add_distrib])
    (fun c v w => by
      simp only [betaVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

theorem betaL_apply (v w : W64) : betaL v w = ∑ T : Fin 64, v T * w (Fin.rev T) := rfl

theorem sum_flipS (i : Fin 6) (f : Fin 64 → ZMod 2) : ∑ T, f (flipS i T) = ∑ T, f T :=
  Equiv.sum_comp (Function.Involutive.toPerm (flipS i) (flipS_flipS i)) f

theorem betaL_wedgeL (i : Fin 6) (v w : W64) : betaL (wedgeL i v) w = betaL v (wedgeL i w) := by
  rw [betaL_apply, betaL_apply, ← sum_flipS i]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [wedgeL_apply, testBit_flipS_self, flipS_flipS, testBit_rev, flipS_rev]
  cases T.val.testBit i.val <;> simp

theorem betaL_contrL (i : Fin 6) (v w : W64) : betaL (contrL i v) w = betaL v (contrL i w) := by
  rw [betaL_apply, betaL_apply, ← sum_flipS i]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [contrL_apply, testBit_flipS_self, flipS_flipS, testBit_rev, flipS_rev]
  cases T.val.testBit i.val <;> simp

theorem betaL_rhoL (x : V12) (v w : W64) : betaL (rhoL x v) w = betaL v (rhoL x w) := by
  simp only [rhoL_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add,
    map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    betaL_wedgeL, betaL_contrL]

theorem betaL_tlift {u w : V12} (h : TsPair u w) (v v' : W64) :
    betaL (tlift u w v) (tlift u w v') = betaL v v' := by
  have hX : ∀ a b : W64, betaL (rhoL u (rhoL w a)) b = betaL a (rhoL u (rhoL w b)) := by
    intro a b
    rw [betaL_rhoL, betaL_rhoL]
    have hc := alg_eq_of_add_eq (rhoL_anticomm_of_B h.2.2)
    have := congrArg (fun f : Module.End (ZMod 2) W64 => betaL a (f b)) hc
    simpa using this.symm
  have hXX : ∀ b : W64, rhoL u (rhoL w (rhoL u (rhoL w b))) = 0 := by
    intro b
    have hc := alg_eq_of_add_eq (rhoL_anticomm_of_B h.2.2)
    have hq := rhoL_mul_self_of_q h.1
    have : rhoL u * rhoL w * (rhoL u * rhoL w) = 0 := by
      rw [zero_add] at hc
      rw [mul_assoc, ← mul_assoc (rhoL w), ← hc, mul_assoc (rhoL u) (rhoL w) (rhoL w),
        rhoL_mul_self_of_q h.2.1, mul_zero, mul_zero]
    simpa using congrArg (fun f : Module.End (ZMod 2) W64 => f b) this
  simp only [tlift, LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, map_add,
    LinearMap.add_apply]
  rw [hX, hX, hXX, map_zero, add_zero]
  calc betaL v v' + betaL v (rhoL u (rhoL w v')) + (betaL v (rhoL u (rhoL w v')))
      = betaL v v' + (betaL v (rhoL u (rhoL w v')) + betaL v (rhoL u (rhoL w v'))) := by abel
    _ = betaL v v' := by rw [zmod2_add_self, add_zero]

@[expose] noncomputable def rhoAt (s : W64) : V12 →ₗ[ZMod 2] W64 where
  toFun x := rhoL x s
  map_add' x y := by rw [map_add, LinearMap.add_apply]
  map_smul' c x := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

@[expose] noncomputable def annSub (s : W64) : Submodule (ZMod 2) V12 := LinearMap.ker (rhoAt s)

theorem mem_annSub {s : W64} {x : V12} : x ∈ annSub s ↔ rhoL x s = 0 := Iff.rfl

theorem zmod2_eq_zero_of_smul {c : ZMod 2} {s : W64} (hs : s ≠ 0) (h : c • s = 0) : c = 0 := by
  rcases (by decide : ∀ d : ZMod 2, d = 0 ∨ d = 1) c with rfl | rfl
  · rfl
  · rw [one_smul] at h
    exact absurd h hs

theorem tsPair_of_mem_annSub {s : W64} (hs : s ≠ 0) {x y : V12} (hx : x ∈ annSub s)
    (hy : y ∈ annSub s) : TsPair x y := by
  rw [mem_annSub] at hx hy
  refine ⟨zmod2_eq_zero_of_smul hs ?_, zmod2_eq_zero_of_smul hs ?_,
    zmod2_eq_zero_of_smul hs ?_⟩
  · have := congrArg (fun f : Module.End (ZMod 2) W64 => f s) (rhoL_mul_self x)
    simpa [hx] using this.symm
  · have := congrArg (fun f : Module.End (ZMod 2) W64 => f s) (rhoL_mul_self y)
    simpa [hy] using this.symm
  · have := congrArg (fun f : Module.End (ZMod 2) W64 => f s) (rhoL_anticomm x y)
    simpa [hx, hy] using this.symm

theorem finrank_le_six_of_isotropic (U : Submodule (ZMod 2) V12)
    (hU : ∀ x ∈ U, ∀ y ∈ U, B12 x y = 0) : finrank (ZMod 2) U ≤ 6 := by
  have hle : U ≤ LinearMap.BilinForm.orthogonal Q12.polarBilin U := fun y hy =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => by
      change Q12.polarBilin x y = 0
      rw [QuadraticMap.polarBilin_apply_apply, polar_Q12]
      exact hU x hx y hy
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal Q12_polarBilin_nondegenerate U
  have h3 : finrank (ZMod 2) V12 = 12 := by
    simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  have h4 := Submodule.finrank_le U
  omega

theorem finrank_annSub_le {s : W64} (hs : s ≠ 0) : finrank (ZMod 2) (annSub s) ≤ 6 :=
  finrank_le_six_of_isotropic _ fun _ hx _ hy => (tsPair_of_mem_annSub hs hx hy).2.2

theorem eq_annSub_of_le {s : W64} (hs : s ≠ 0) {U : Submodule (ZMod 2) V12} (hU : U ≤ annSub s)
    (h6 : 6 ≤ finrank (ZMod 2) U) : U = annSub s :=
  Submodule.eq_of_le_of_finrank_le hU ((finrank_annSub_le hs).trans h6)

theorem annSub_tlift {u w : V12} (h : TsPair u w) (s : W64) :
    annSub (tlift u w s) = (annSub s).map (siegelEquiv u w).toLinearMap := by
  have hS : ∀ x, siegelEquiv u w (siegelEquiv u w x) = x := fun x => by
    have := congrArg (fun g : V12 ≃ₗ[ZMod 2] V12 => g x) (siegelEquiv_mul_self h)
    simpa using this
  ext x
  rw [Submodule.mem_map, mem_annSub]
  constructor
  · intro hx
    refine ⟨siegelEquiv u w x, ?_, hS x⟩
    rw [mem_annSub]
    have h1 := tlift_rho_apply h (siegelEquiv u w x) s
    rw [hS, hx] at h1
    have h2 := congrArg (tlift u w) h1
    rwa [tlift_apply_tlift h, map_zero] at h2
  · rintro ⟨y, hy, rfl⟩
    rw [mem_annSub] at hy
    change rhoL (siegelEquiv u w y) (tlift u w s) = 0
    rw [← tlift_rho_apply h, hy, map_zero]

end CFSG.GF2Type.SmithTypeE.DMod
