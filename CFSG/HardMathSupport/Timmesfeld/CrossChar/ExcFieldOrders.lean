module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldBalance

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley

section Orders

theorem dvd_pow_sub_one_of_orderOf {p q e n : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) = e) (hen : e ∣ n) : p ∣ q ^ n - 1 := by
  have h1 : ((q : ℕ) : ZMod p) ^ n = 1 := orderOf_dvd_iff_pow_eq_one.1 (h ▸ hen)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, h1]
  simp

theorem dvd_sq_sub_one_of_cast_eq {p a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p)) (hd : p ∣ a ^ 2 - 1) : p ∣ b ^ 2 - 1 := by
  have h1 := (ZMod.natCast_eq_zero_iff (a ^ 2 - 1) p).2 hd
  rw [Nat.cast_sub (Nat.one_le_pow _ _ ha), Nat.cast_pow, Nat.cast_one, h] at h1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hb), Nat.cast_pow,
    Nat.cast_one]
  exact h1

end Orders

section Torus


theorem not_coprime_card_adjointE8 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E8 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E8 k)) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card k : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  rcases degCount_E8_eq_two hcnt with rfl | rfl | rfl | rfl
  · exact not_coprime_card_of_sylowTorus (sylowTorus_E8_five k hp he) hp (by norm_num)
  · exact not_coprime_card_of_sylowTorus (sylowTorus_E8_eight k hp he) hp (by norm_num)
  · exact not_coprime_card_of_sylowTorus (sylowTorus_E8_ten k hp he) hp (by norm_num)
  · exact not_coprime_card_of_sylowTorus (sylowTorus_E8_twelve k hp he) hp (by norm_num)

theorem not_coprime_card_adjointE7 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E7 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E7 k)) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card k : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  obtain rfl := degCount_E7_eq_two hcnt
  exact not_coprime_card_of_sylowTorus (sylowTorus_E7_four k hp he) hp (by norm_num)

theorem not_coprime_card_adjointE6 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E6 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E6 k)) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card k : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  rcases degCount_E6_eq_two hcnt with rfl | rfl
  · exact not_coprime_card_of_sylowTorus (sylowTorus_E6_four k hp he) hp (by norm_num)
  · exact not_coprime_card_of_sylowTorus (sylowTorus_E6_six k hp he) hp (by norm_num)

theorem not_coprime_card_adjointF4 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.F4 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.F4 k)) := by
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  rw [← Nat.Prime.dvd_iff_not_coprime hp, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card k : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  unfold ordF4
  rcases degCount_F4_eq_two hcnt with rfl | rfl | rfl
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_sub_one_of_orderOf hq he
      (by norm_num : 3 ∣ 6)) _) _
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_sub_one_of_orderOf hq he
      (by norm_num : 4 ∣ 8)) _) _) _
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_sub_one_of_orderOf hq he
      (by norm_num : 6 ∣ 6)) _) _

theorem not_coprime_card_adjointG2 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card k ^ 2 - 1) : ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 k)) := by
  rw [← Nat.Prime.dvd_iff_not_coprime hp, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  unfold ordG2
  exact Dvd.dvd.mul_left hd _

end Torus

end CFSG.HardMathSupport.Timmesfeld.CrossChar
