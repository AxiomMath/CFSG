
module

public import Certificates.Data.Kernel.P946008.Defs
public import Certificates.Certificate946008Base

public section

open scoped BigOperators

namespace CFSG.KC.P946008

open CFSG.RankThree.GF2n.Parrott Certificates

theorem packT_succ (f : Nat → Nat) (n : Nat) :
    packT f (n + 1) = packT f n + f n % 256 * 256 ^ n := rfl

theorem packT_lt (f : Nat → Nat) : ∀ n, packT f n < 256 ^ n
  | 0 => Nat.one_pos
  | n + 1 => by
    rw [packT_succ, pow_succ]
    have h1 := packT_lt f n
    have h2 : f n % 256 < 256 := Nat.mod_lt _ (by norm_num)
    have h3 : f n % 256 * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    generalize 256 ^ n = X at h1 h3 ⊢
    generalize f n % 256 * X = Y at h3 ⊢
    omega

theorem lk_packT (f : Nat → Nat) : ∀ n p, p < n → lk (packT f n) p = f p % 256
  | 0, p, h => absurd h (Nat.not_lt_zero p)
  | n + 1, p, h => by
    rw [lk, packT_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hp | hp
    · have ih := lk_packT f n p hp
      rw [lk] at ih
      obtain ⟨d, hd⟩ : ∃ d, n = p + 1 + d := ⟨n - (p + 1), by omega⟩
      have e : f n % 256 * 256 ^ n = 256 ^ p * (256 * (f n % 256 * 256 ^ d)) := by
        rw [hd]
        ring
      rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
      exact ih
    · subst hp
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (packT_lt f p), zero_add,
        Nat.mod_mod]

theorem sum_shift_lt : ∀ (n : Nat) (b : Fin n → Nat), (∀ i, b i < 2) →
    ∑ i : Fin n, b i <<< (i : Nat) < 2 ^ n
  | 0, b, _ => by simp
  | n + 1, b, hb => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have ih := sum_shift_lt n (fun i => b i.castSucc) (fun i => hb _)
    have h2 := hb (Fin.last n)
    rw [Nat.shiftLeft_eq, pow_succ]
    have h3 : b (Fin.last n) * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
    generalize ∑ i : Fin n, b i.castSucc <<< (i : Nat) = S at ih ⊢
    generalize 2 ^ n = X at ih h3 ⊢
    generalize b (Fin.last n) * X = Y at h3 ⊢
    omega

theorem bitRow_lt (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (m : Nat) : bitRow M m < 256 :=
  sum_shift_lt 8 _ (fun _ => Nat.mod_lt _ (by norm_num))

theorem cMask_lt (ms : List Nat) (v : Nat) : cMask ms v < 256 :=
  lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)

theorem lkT (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) {v : Nat} (hv : v < 256) :
    lk (packT (bitRow M) 256) v = bitRow M v := by
  rw [lk_packT _ _ _ hv, Nat.mod_eq_of_lt (bitRow_lt M v)]

theorem lkC (ms : List Nat) {v : Nat} (hv : v < 256) :
    lk (packT (cMask ms) 256) v = cMask ms v := by
  rw [lk_packT _ _ _ hv, Nat.mod_eq_of_lt (cMask_lt ms v)]

theorem phi_eq (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) :
    phiMask M ms = phiK (packT (bitRow M) 256) (packT (cMask ms) 256) := by
  funext p
  have hp : p % 256 < 256 := Nat.mod_lt _ (by norm_num)
  rw [phiK, lkT M hp, lkC ms hp]
  rfl

theorem allN_succ (n : Nat) (f : Nat → Bool) : allN (n + 1) f = (f n && allN n f) := rfl

theorem allN_true {f : Nat → Bool} : ∀ {n}, allN n f = true → ∀ k < n, f k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    rw [allN_succ, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact allN_true h.2 k hk
    · exact h.1

theorem cocycle_of (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat)
    (h : cocyK (packT (bitRow M) 256) (packT (cMask ms) 256) = true) :
    cocycleCheck M ms = true := by
  rw [cocycleCheck, List.all_eq_true]
  intro p hp
  rw [List.all_eq_true]
  intro q hq
  rw [List.mem_range] at hp hq
  have h1 : cocyRow (packT (bitRow M) 256) (packT (cMask ms) 256) p
      (lk (packT (bitRow M) 256) p) (lk (packT (cMask ms) 256) p) = true := allN_true h p hp
  have h2 := allN_true h1 q hq
  have h256 : (256 : Nat) = 2 ^ 8 := by norm_num
  have hx : p ^^^ q < 256 := by
    rw [h256] at hp hq ⊢
    exact Nat.xor_lt_two_pow hp hq
  rw [lkC ms hx, lkC ms hp, lkC ms hq, lkT M hp, lkT M hq] at h2
  exact h2

theorem cube_of (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat)
    (h : cubeK (packT (bitRow M) 256) (packT (cMask ms) 256) = true) :
    cubeCheck M ms = true := by
  rw [cubeCheck, List.all_eq_true, phi_eq M ms]
  intro p hp
  exact allN_true h p (List.mem_range.mp hp)

theorem liftFacts_of {M Minv : Matrix (Fin 8) (Fin 8) (ZMod 2)} {ms : List Nat}
    {fixedCard invCard : ℕ} {noncommValue : Bool}
    (h1 : M * Minv = 1) (h2 : Minv * M = 1) (h3 : M * M * M = 1)
    (hk : liftK (packT (bitRow M) 256) (packT (cMask ms) 256) fixedCard invCard noncommValue =
      true) :
    LiftFacts M Minv ms fixedCard invCard noncommValue := by
  rw [liftK] at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩ := hk
  refine ⟨h1, h2, h3, cocycle_of M ms k5, ?_, cube_of M ms k4, ?_, ?_, ?_⟩
  · rw [phi_eq M ms]
    exact beq_iff_eq.mp k0
  · rw [phi_eq M ms]
    exact beq_iff_eq.mp k1
  · change noncommG (phiMask M ms) = noncommValue
    rw [phi_eq M ms]
    exact beq_iff_eq.mp k2
  · rw [phi_eq M ms]
    exact beq_iff_eq.mp k3

theorem fixedCentral_eq (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) :
    fixedCentral M ms = centralG (phiK (packT (bitRow M) 256) (packT (cMask ms) 256)) := by
  change centralG (phiMask M ms) = _
  rw [phi_eq M ms]

theorem invMaskCount_eq (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) :
    invMaskCount M ms = invCountG (phiK (packT (bitRow M) 256) (packT (cMask ms) 256)) := by
  change invCountG (phiMask M ms) = _
  rw [phi_eq M ms]

theorem fixedCentreCard_eq (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) :
    fixedCentreCard M ms = centreG (phiK (packT (bitRow M) 256) (packT (cMask ms) 256)) := by
  change centreG (phiMask M ms) = _
  rw [phi_eq M ms]

theorem fixedOrderFour_eq (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) :
    fixedOrderFour M ms = ord4G (phiK (packT (bitRow M) 256) (packT (cMask ms) 256)) := by
  change ord4G (phiMask M ms) = _
  rw [phi_eq M ms]

end CFSG.KC.P946008
