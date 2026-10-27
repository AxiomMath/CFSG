module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Ord
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOrd

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.X10

theorem two_mul_card_l4u4 {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hX : (p ^ f % 4 = 3 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel X .PSU 4 p f)) :
    ((Nat.card X * 2 = (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)) ∨
      (Nat.card X * 2 = (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)))
      ∧ (Nat.card X).factorization p = 6 * f := by
  rcases hX with ⟨h3, hX⟩ | ⟨h1, hX⟩
  · have h := card_psl4 hp2 hX
    rw [(gcd_four_of_mod_three h3).1] at h
    exact ⟨Or.inl h, by
      have := (CatLeafProof.X10Sp.lieOrder_of_lieModel (Or.inl rfl) hp2 (by norm_num) hX).2
      simpa [lieSylowExponent] using this⟩
  · have h := card_psu4 hp2 hX
    rw [(gcd_four_of_mod_one h1).2] at h
    exact ⟨Or.inr h, by
      have := (CatLeafProof.X10Sp.lieOrder_of_lieModel (Or.inr (Or.inl rfl)) hp2 (by norm_num)
        hX).2
      simpa [lieSylowExponent] using this⟩

theorem pow_nine_le {q : ℕ} (hq : 3 ≤ q) :
    q ^ 9 ≤ 2 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
  have h2 : 9 ≤ q ^ 2 := by nlinarith
  have h3 : 27 ≤ q ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h4 : 81 ≤ q ^ 4 := by
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have a2 : 8 * q ^ 2 ≤ 9 * (q ^ 2 - 1) := by omega
  have a3 : 26 * q ^ 3 ≤ 27 * (q ^ 3 - 1) := by omega
  have a4 : 80 * q ^ 4 ≤ 81 * (q ^ 4 - 1) := by omega
  have e9 : q ^ 9 = q ^ 2 * q ^ 3 * q ^ 4 := by ring
  have hm : (8 * q ^ 2) * (26 * q ^ 3) * (80 * q ^ 4) ≤
      (9 * (q ^ 2 - 1)) * (27 * (q ^ 3 - 1)) * (81 * (q ^ 4 - 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul a2 a3) a4
  have : 16640 * q ^ 9 ≤ 19683 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
    calc 16640 * q ^ 9 = (8 * q ^ 2) * (26 * q ^ 3) * (80 * q ^ 4) := by rw [e9]; ring
      _ ≤ (9 * (q ^ 2 - 1)) * (27 * (q ^ 3 - 1)) * (81 * (q ^ 4 - 1)) := hm
      _ = 19683 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by ring
  omega

theorem pow_fifteen_le_four_mul_card {X : Type} [Group X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hX : (p ^ f % 4 = 3 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel X .PSU 4 p f)) :
    (p ^ f) ^ 15 ≤ 4 * Nat.card X := by
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  have h9 := pow_nine_le hq3
  have hlow : (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1) ≤
      Nat.card X * 2 := by
    rcases (two_mul_card_l4u4 hp2 hX).1 with h | h
    · exact h.ge
    · rw [h]
      gcongr
      omega
  calc (p ^ f) ^ 15 = (p ^ f) ^ 6 * (p ^ f) ^ 9 := by ring
    _ ≤ (p ^ f) ^ 6 * (2 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1))) :=
        Nat.mul_le_mul_left _ h9
    _ = 2 * ((p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)) := by
        ring
    _ ≤ 2 * (Nat.card X * 2) := Nat.mul_le_mul_left _ hlow
    _ = 4 * Nat.card X := by ring

theorem false_of_l4u4_of_cofactor_le (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ' : StatedLieTag} {n' p f' f N C c : ℕ} (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hadm' : StatedLieAdmissible τ' n' p f') (hX' : LieModel X τ' n' p f')
    (hX : (p ^ f % 4 = 3 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel X .PSU 4 p f))
    (hN : lieSylowExponent τ' n' = N)
    (hC : lieOrderCofactor τ' n' (p ^ f') ≤ c * (p ^ f') ^ C)
    (h16 : N * f' = 6 * f → 2 * C ≤ 3 * N ∧ 16 * c ^ 2 < (p ^ f') ^ (3 * N - 2 * C)) :
    False := by
  have hp : p.Prime := hadm'.1
  obtain ⟨-, hc', hfac'⟩ := hO X τ' n' p f' hadm' hX'
  rw [hN] at hfac'
  have hfac := (two_mul_card_l4u4 hp2 hX).2
  have hNf : N * f' = 6 * f := hfac'.symm.trans hfac
  obtain ⟨h2C, h16'⟩ := h16 hNf
  have hQN : (p ^ f') ^ N = (p ^ f) ^ 6 := by
    rw [← pow_mul, ← pow_mul, mul_comm f' N, hNf, mul_comm]
  have hXle : Nat.card X ≤ c * (p ^ f') ^ (N + C) := by
    have hdiv := Nat.pos_of_ne_zero (lieOrderDivisor_ne_zero hadm')
    calc Nat.card X ≤ Nat.card X * lieOrderDivisor τ' n' (p ^ f') :=
          Nat.le_mul_of_pos_right _ hdiv
      _ = lieOrderNumerator τ' n' (p ^ f') := hc'
      _ = (p ^ f') ^ N * lieOrderCofactor τ' n' (p ^ f') := by
          rw [lieOrderNumerator_eq hadm', hN]
      _ ≤ (p ^ f') ^ N * (c * (p ^ f') ^ C) := Nat.mul_le_mul_left _ hC
      _ = c * (p ^ f') ^ (N + C) := by rw [pow_add]; ring
  have hlow := pow_fifteen_le_four_mul_card hp hp2 hf hX
  have hsq : ((p ^ f') ^ N) ^ 5 ≤ 16 * c ^ 2 * (p ^ f') ^ (2 * N + 2 * C) := by
    calc ((p ^ f') ^ N) ^ 5 = ((p ^ f) ^ 15) ^ 2 := by rw [hQN]; ring
      _ ≤ (4 * Nat.card X) ^ 2 := Nat.pow_le_pow_left hlow 2
      _ ≤ (4 * (c * (p ^ f') ^ (N + C))) ^ 2 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hXle) 2
      _ = 16 * c ^ 2 * (p ^ f') ^ (2 * N + 2 * C) := by
          rw [show 2 * N + 2 * C = (N + C) * 2 by ring, pow_mul]
          ring
  have hsplit : ((p ^ f') ^ N) ^ 5 =
      (p ^ f') ^ (3 * N - 2 * C) * (p ^ f') ^ (2 * N + 2 * C) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hsplit] at hsq
  have hpos : 0 < (p ^ f') ^ (2 * N + 2 * C) := pow_pos (pow_pos hp.pos _) _
  have := Nat.le_of_mul_le_mul_right hsq hpos
  omega

theorem sixteen_lt_pow {Q k : ℕ} (hQ : 3 ≤ Q) (hk : 3 ≤ k) : 16 * 1 ^ 2 < Q ^ k :=
  calc 16 * 1 ^ 2 < 3 ^ 3 := by norm_num
    _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
    _ ≤ Q ^ k := Nat.pow_le_pow_right (by omega) hk

theorem unitary_six_factor_le {Q : ℕ} (hQ : 2 ≤ Q) : (Q ^ 3 + 1) * (Q ^ 5 + 1) ≤ Q ^ 9 := by
  have e : (Q ^ 3 + 1) * (Q ^ 5 + 1) = Q ^ 8 + Q ^ 5 + Q ^ 3 + 1 := by ring
  have h35 : Q ^ 3 ≤ Q ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h8 : 8 ≤ Q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have h58 : 3 * Q ^ 5 ≤ Q ^ 8 :=
    calc 3 * Q ^ 5 ≤ Q ^ 3 * Q ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = Q ^ 8 := by ring
  have h89 : 2 * Q ^ 8 ≤ Q ^ 9 :=
    calc 2 * Q ^ 8 ≤ Q * Q ^ 8 := Nat.mul_le_mul_right _ hQ
      _ = Q ^ 9 := by ring
  omega

end CFSG.ComponentClassification.GSThmB.Pump516
