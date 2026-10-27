module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup

section Twist

variable {W : Type*} [Group W]

@[expose] def fixSub (j : MulAut W) : Subgroup W where
  carrier := {w | j w = w}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one j
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixSub {j : MulAut W} {w : W} : w ∈ fixSub j ↔ j w = w := Iff.rfl

@[expose] def twistHom (hc : ∀ a b : W, a * b = b * a) (j : MulAut W) : W →* W :=
  MonoidHom.mk' (fun w => w * j w) fun a b => by
    simp only [map_mul]
    calc a * b * (j a * j b) = a * (b * j a) * j b := by group
      _ = a * (j a * b) * j b := by rw [hc b (j a)]
      _ = a * j a * (b * j b) := by group

theorem twistHom_apply (hc : ∀ a b : W, a * b = b * a) (j : MulAut W) (w : W) :
    twistHom hc j w = w * j w := rfl

theorem ker_twistHom (hc : ∀ a b : W, a * b = b * a) (h2 : ∀ w : W, w * w = 1) (j : MulAut W) :
    (twistHom hc j).ker = fixSub j := by
  ext w
  rw [MonoidHom.mem_ker, twistHom_apply, mem_fixSub]
  constructor
  · intro h
    have hw : w⁻¹ = w := inv_eq_of_mul_eq_one_right (h2 w)
    have : j w = w⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, hw]
  · intro h
    rw [h]
    exact h2 w

theorem range_twistHom_le (hc : ∀ a b : W, a * b = b * a) {j : MulAut W} (hj : j * j = 1) :
    (twistHom hc j).range ≤ fixSub j := by
  rintro _ ⟨w, rfl⟩
  rw [mem_fixSub, twistHom_apply, map_mul]
  have hjj : j (j w) = w := by
    have := congrArg (fun φ : MulAut W => φ w) hj
    simpa using this
  rw [hjj]
  exact hc _ _

theorem commImg_eq_range_twistHom (hc : ∀ a b : W, a * b = b * a) (h2 : ∀ w : W, w * w = 1)
    (j : MulAut W) : CFSG.LocalAnalysis.EvenBN.Tits.N.commImg j = (twistHom hc j).range := by
  have hinv : ∀ w : W, (j w)⁻¹ = j w := fun w => by
    rw [← map_inv, inv_eq_of_mul_eq_one_right (h2 w)]
  refine le_antisymm ?_ ?_
  · rw [CFSG.LocalAnalysis.EvenBN.Tits.N.commImg, Subgroup.closure_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨w, by rw [twistHom_apply, hinv]⟩
  · rintro _ ⟨w, rfl⟩
    refine Subgroup.subset_closure ⟨w, ?_⟩
    rw [twistHom_apply, hinv]

variable [Finite W]

theorem card_fixSub_mul_card_commImg (hc : ∀ a b : W, a * b = b * a) (h2 : ∀ w : W, w * w = 1)
    (j : MulAut W) :
    Nat.card (fixSub j) * Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg j) = Nat.card W := by
  rw [commImg_eq_range_twistHom hc h2 j, ← ker_twistHom hc h2 j]
  exact Subgroup.card_ker_mul_card_range (twistHom hc j)

theorem commImg_le_fixSub (hc : ∀ a b : W, a * b = b * a) (h2 : ∀ w : W, w * w = 1) {j : MulAut W}
    (hj : j * j = 1) : CFSG.LocalAnalysis.EvenBN.Tits.N.commImg j ≤ fixSub j := by
  rw [commImg_eq_range_twistHom hc h2 j]
  exact range_twistHom_le hc hj

theorem card_le_sq_fixSub (hc : ∀ a b : W, a * b = b * a) (h2 : ∀ w : W, w * w = 1) {j : MulAut W}
    (hj : j * j = 1) : Nat.card W ≤ Nat.card (fixSub j) ^ 2 := by
  have h := card_fixSub_mul_card_commImg hc h2 j
  have hle : Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg j) ≤ Nat.card (fixSub j) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective (commImg_le_fixSub hc h2 hj))
  calc Nat.card W = Nat.card (fixSub j) * Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg j) :=
        h.symm
    _ ≤ Nat.card (fixSub j) * Nat.card (fixSub j) := Nat.mul_le_mul_left _ hle
    _ = Nat.card (fixSub j) ^ 2 := (sq _).symm

theorem card_fixSub_sq_of_inverts (hc : ∀ a b : W, a * b = b * a) (h2 : ∀ w : W, w * w = 1)
    {x d : MulAut W} (hd : d * d = 1) (hx5 : x ^ 5 = 1) (hfpf : ∀ w : W, x w = w → w = 1)
    (hdx : d * x * d⁻¹ = x⁻¹) : Nat.card (fixSub d) ^ 2 = Nat.card W := by
  letI : CommGroup W := { ‹Group W› with mul_comm := hc }
  have hx4 : x⁻¹ = x ^ 4 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx5)
  have e1 : d * x = x ^ 4 * d := by rw [← hx4]; exact mul_inv_eq_iff_eq_mul.1 hdx
  have e2 : d * (x * x) = x ^ 3 * d := by
    calc d * (x * x) = (d * x) * x := by rw [mul_assoc]
      _ = x ^ 4 * d * x := by rw [e1]
      _ = x ^ 4 * (d * x) := by rw [mul_assoc]
      _ = x ^ 4 * (x ^ 4 * d) := by rw [e1]
      _ = x ^ 8 * d := by rw [← mul_assoc, ← pow_add]
      _ = x ^ 3 * d := by
        have : x ^ 8 = x ^ 3 := by rw [show 8 = 5 + 3 from rfl, pow_add, hx5, one_mul]
        rw [this]
  have hrange : fixSub d ≤ (twistHom hc d).range := by
    intro c hcd
    rw [mem_fixSub] at hcd
    have hp : ∀ n : ℕ, (x ^ (n + 1)) c = x ((x ^ n) c) := fun n => by rw [pow_succ']; rfl
    have p1 : (x ^ 1) c = x c := by rw [hp 0, pow_zero]; rfl
    have p2 : (x ^ 2) c = x (x c) := by rw [hp 1, p1]
    have p3 : (x ^ 3) c = x (x (x c)) := by rw [hp 2, p2]
    have p4 : (x ^ 4) c = x (x (x (x c))) := by rw [hp 3, p3]
    have p5 : x (x (x (x (x c)))) = c := by rw [← p4, ← hp 4, hx5]; rfl
    have h1 : d (x c) = x (x (x (x c))) := by
      have := congrArg (fun φ : MulAut W => φ c) e1
      simp only [MulAut.mul_apply, hcd] at this
      rw [this, p4]
    have h2' : d (x (x c)) = x (x (x c)) := by
      have := congrArg (fun φ : MulAut W => φ c) e2
      simp only [MulAut.mul_apply, hcd] at this
      rw [this, p3]
    have hN : c * x c * x (x c) * x (x (x c)) * x (x (x (x c))) = 1 := by
      apply hfpf
      simp only [map_mul, p5]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    refine ⟨x c * x (x c), ?_⟩
    rw [twistHom_apply, map_mul, h1, h2']
    have hc1 : c * (x c * x (x c) * (x (x (x (x c))) * x (x (x c)))) = 1 := by
      rw [← hN]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    have hc2 := eq_inv_of_mul_eq_one_right hc1
    rw [hc2]
    exact inv_eq_of_mul_eq_one_right (h2 c)
  have hEq : fixSub d = (twistHom hc d).range := le_antisymm hrange (range_twistHom_le hc hd)
  have hcard := card_fixSub_mul_card_commImg hc h2 d
  rw [commImg_eq_range_twistHom hc h2 d, ← hEq] at hcard
  rw [sq]
  exact hcard

end Twist

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
