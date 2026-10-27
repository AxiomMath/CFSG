module

public import Certificates.Data.Kernel.Tower.T2
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerFacts
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerCode
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower

variable {X : Type*} [Group X] {mul : Nat → Nat → Nat} {dec : Nat → X}

@[expose] def dec2 (D : ExtData X) (dec : Nat → X) (c : Nat) : CycExt D :=
  ⟨dec (c / 2), c % 2 == 1⟩

theorem tm_eq (mul : Nat → Nat → Nat) (FA g a b : Nat) : tm mul FA g a b =
    if a % 2 = 1 then
      (if b % 2 = 1 then 2 * mul (mul (a / 2) (l16 FA (b / 2))) g
        else 2 * mul (a / 2) (l16 FA (b / 2)) + 1)
    else 2 * mul (a / 2) (b / 2) + b % 2 := by
  have h1 : ∀ x : Nat, Nat.shiftRight x 1 = x / 2 := fun x =>
    (Nat.shiftRight_eq_div_pow x 1).trans (by rw [pow_one])
  have h2 : ∀ x : Nat, Nat.land x 1 = x % 2 := fun x => Nat.and_one_is_mod x
  unfold tm
  simp only [h1, h2]
  cases hA : Nat.beq (a % 2) 1 <;> cases hB : Nat.beq (b % 2) 1
  · have ha := Nat.ne_of_beq_eq_false hA
    simp [ha, Nat.mul_comm]
  · have ha := Nat.ne_of_beq_eq_false hA
    simp [ha, Nat.mul_comm]
  · have ha := Nat.eq_of_beq_eq_true hA
    have hb := Nat.ne_of_beq_eq_false hB
    simp [ha, hb, Nat.mul_comm]
  · have ha := Nat.eq_of_beq_eq_true hA
    have hb := Nat.eq_of_beq_eq_true hB
    simp [ha, hb, Nat.mul_comm]

theorem dec2_two_mul_add (D : ExtData X) (dec : Nat → X) {m r : Nat} (hr : r < 2) :
    dec2 D dec (2 * m + r) = ⟨dec m, r == 1⟩ := by
  have e1 : (2 * m + r) / 2 = m := by omega
  have e2 : (2 * m + r) % 2 = r := by omega
  rw [dec2, e1, e2]

theorem dec2_two_mul (D : ExtData X) (dec : Nat → X) (m : Nat) :
    dec2 D dec (2 * m) = ⟨dec m, false⟩ := by
  have e1 : 2 * m / 2 = m := by omega
  have e2 : 2 * m % 2 = 0 := by omega
  rw [dec2, e1, e2]
  rfl

theorem tm_model (M : IsModel (⊤ : Subgroup X) 8192 mul dec) (D : ExtData X) {FA g : Nat}
    (hFA : ∀ c < 8192, l16 FA c < 8192 ∧ D.α (dec c) = dec (l16 FA c)) (hg : g < 8192)
    (hdg : dec g = D.g) :
    IsModel (⊤ : Subgroup (CycExt D)) 16384 (tm mul FA g) (dec2 D dec) where
  mem _ _ := Subgroup.mem_top _
  inj a ha b hb h := by
    rw [dec2, dec2, CycExt.mk.injEq] at h
    have hk := M.inj (a / 2) (by omega) (b / 2) (by omega) h.1
    have hd : a % 2 = b % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> simp_all
    omega
  surj x _ := by
    obtain ⟨k, d⟩ := x
    obtain ⟨c, hc, hck⟩ := M.surj k (Subgroup.mem_top _)
    cases d
    · refine ⟨2 * c + 0, by omega, ?_⟩
      rw [dec2_two_mul_add D dec (by omega), hck]
      rfl
    · refine ⟨2 * c + 1, by omega, ?_⟩
      rw [dec2_two_mul_add D dec (by omega), hck]
      rfl
  mul_lt a ha b hb := by
    have hb2 : b / 2 < 8192 := by omega
    have hF := (hFA _ hb2).1
    rw [tm_eq]
    have ha2 : a / 2 < 8192 := by omega
    split_ifs
    · have := M.mul_lt _ (M.mul_lt (a / 2) ha2 _ hF) g hg
      omega
    · have := M.mul_lt (a / 2) ha2 _ hF
      omega
    · have := M.mul_lt (a / 2) ha2 (b / 2) hb2
      omega
  dec_mul a ha b hb := by
    have ha2 : a / 2 < 8192 := by omega
    have hb2 : b / 2 < 8192 := by omega
    obtain ⟨hF, hα⟩ := hFA _ hb2
    have ea : dec2 D dec a = ⟨dec (a / 2), a % 2 == 1⟩ := rfl
    have eb : dec2 D dec b = ⟨dec (b / 2), b % 2 == 1⟩ := rfl
    rw [tm_eq, ea, eb, CycExt.mk_mul_mk]
    split_ifs with h1 h2
    · rw [dec2_two_mul, M.dec_mul _ (M.mul_lt _ ha2 _ hF) _ hg, M.dec_mul _ ha2 _ hF]
      simp [h1, h2, CycExt.pw, CycExt.sq, hα, hdg]
    · rw [dec2_two_mul_add D dec (by omega), M.dec_mul _ ha2 _ hF]
      have h0 : b % 2 = 0 := by omega
      simp [h1, h0, CycExt.pw, CycExt.sq, hα]
    · rw [dec2_two_mul_add D dec (by omega), M.dec_mul _ ha2 _ hb2]
      have h0 : a % 2 = 0 := by omega
      simp [h0, CycExt.pw, CycExt.sq]
  zero_lt := by omega
  dec_zero := by
    rw [dec2, Nat.zero_div, M.dec_zero]
    rfl

end Certificates.KernelTower
