module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05NonIsoArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS05NonIso

open CFSG.Yardstones.Md0ec50421ce4

theorem catalogIs_onLie_eq {S : Type} [Group S] {d : TauCeti.LieTypeIndex}
    (h : catalogIs S (onLie fun d' => d' = d)) :
    ∃ hv : d.Valid, Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨d, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | alternating n hn => exact (hi : False).elim
  | lie v =>
      obtain ⟨d', hv⟩ := v
      have hd : d' = d := hi
      subst hd
      exact ⟨hv, ⟨e⟩⟩
  | sporadic s => exact (hi : False).elim

theorem valid_B2_ne3 {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B 2 Q).Valid) :
    Q.p ^ Q.exponent ≠ 3 := fun h =>
  ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
    ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2 ⟨rfl, (TauCeti.PrimePower.card_def Q).trans h⟩)

theorem valid_A3_ne2 {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 3 Q).Valid) :
    Q.p ^ Q.exponent ≠ 2 := fun h =>
  ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
    ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2
      (Or.inr (Or.inr ⟨rfl, (TauCeti.PrimePower.card_def Q).trans h⟩)))

theorem cancel_common {M d1 d2 Z A B : ℕ} (hZ : 0 < Z) (E1 : M * d1 = Z * A) (E2 : M * d2 = Z * B) :
    A * d2 = B * d1 := by
  refine Nat.eq_of_mul_eq_mul_left hZ ?_
  calc Z * (A * d2) = (Z * A) * d2 := by ring
    _ = (M * d1) * d2 := by rw [E1]
    _ = (M * d2) * d1 := by ring
    _ = (Z * B) * d1 := by rw [E2]
    _ = Z * (B * d1) := by ring

theorem core_gen {M d1 d2 Z P1 P2 : ℕ} (hZ : 0 < Z) (E1 : M * d1 = Z * P1) (E2 : M * d2 = Z * P2)
    (hd1 : d1 ≤ 3) (hd2 : 1 ≤ d2) (hP : 3 * P2 < P1) : False := by
  have key := cancel_common hZ E1 E2
  have h1 : P2 * d1 ≤ P2 * 3 := Nat.mul_le_mul_left _ hd1
  have h2 : P1 ≤ P1 * d2 := Nat.le_mul_of_pos_right _ hd2
  omega

theorem ineq_t_A2B2 {t : ℕ} (ht : 2 ≤ t) : 3 * (t ^ 6 - 1) < t ^ 8 - 1 := by
  have h8 : 4 * t ^ 6 ≤ t ^ 8 := by
    have : t ^ 8 = t ^ 6 * t ^ 2 := by ring
    rw [this]
    have h4 : 4 ≤ t ^ 2 := by nlinarith
    have := Nat.mul_le_mul_left (t ^ 6) h4
    linarith
  have h6 : 1 ≤ t ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

theorem ineq_t_U3B2 {t : ℕ} (ht : 2 ≤ t) :
    3 * ((t ^ 6 - 1) * (t ^ 12 - 1)) < (t ^ 8 - 1) * (t ^ 12 + 1) := by
  have h6 : 4 * t ^ 6 ≤ t ^ 8 := by
    have : t ^ 8 = t ^ 6 * t ^ 2 := by ring
    rw [this]
    have h4 : 4 ≤ t ^ 2 := by nlinarith
    have := Nat.mul_le_mul_left (t ^ 6) h4
    linarith
  have h1 : 1 ≤ t ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h8 : 1 ≤ t ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h12 : 1 ≤ t ^ 12 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h8, h12]
  have h6' : (4 : ℤ) * (t : ℤ) ^ 6 ≤ (t : ℤ) ^ 8 := by exact_mod_cast h6
  have h1' : (1 : ℤ) ≤ (t : ℤ) ^ 6 := by exact_mod_cast h1
  have h12' : (1 : ℤ) ≤ (t : ℤ) ^ 12 := by exact_mod_cast h12
  have hab : (1 : ℤ) ≤ (t : ℤ) ^ 6 * (t : ℤ) ^ 12 := by nlinarith
  have hc := mul_le_mul_of_nonneg_right h6' (by positivity : (0 : ℤ) ≤ (t : ℤ) ^ 12)
  nlinarith

theorem ineq_s_A3 {s : ℕ} (hs : 3 ≤ s) : 3 * ((s ^ 2 - 1) * (s ^ 3 - 1)) < s ^ 6 - 1 := by
  rcases (show s = 3 ∨ 4 ≤ s by omega) with rfl | h4
  · norm_num
  · have hA : (s ^ 2 - 1) * (s ^ 3 - 1) ≤ s ^ 2 * s ^ 3 :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have h1 : 3 * ((s ^ 2 - 1) * (s ^ 3 - 1)) ≤ 3 * s ^ 5 := by
      calc 3 * ((s ^ 2 - 1) * (s ^ 3 - 1)) ≤ 3 * (s ^ 2 * s ^ 3) := Nat.mul_le_mul_left 3 hA
        _ = 3 * s ^ 5 := by ring
    have h5 : 4 * s ^ 5 ≤ s ^ 6 := by
      have : s ^ 6 = s ^ 5 * s := by ring
      rw [this]
      have := Nat.mul_le_mul_left (s ^ 5) h4
      linarith
    have h6 : 2 ≤ s ^ 5 := le_trans (by norm_num) (Nat.pow_le_pow_left h4 5)
    exact lt_of_le_of_lt h1 (by omega)

theorem ineq_s_pm {s : ℕ} (h4 : 4 ≤ s) :
    3 * ((s ^ 2 - 1) * (s ^ 3 + 1)) ≤ 3 * (s ^ 5 + s ^ 2) ∧ 3 * s ^ 2 + 2 ≤ s ^ 5 ∧
      4 * s ^ 5 ≤ s ^ 6 := by
  have hA : (s ^ 2 - 1) * (s ^ 3 + 1) ≤ s ^ 2 * (s ^ 3 + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  refine ⟨?_, ?_, ?_⟩
  · calc 3 * ((s ^ 2 - 1) * (s ^ 3 + 1)) ≤ 3 * (s ^ 2 * (s ^ 3 + 1)) := Nat.mul_le_mul_left 3 hA
      _ = 3 * (s ^ 5 + s ^ 2) := by ring
  · have h4' : 4 ≤ s ^ 3 := by nlinarith
    have h2 : 4 * s ^ 2 ≤ s ^ 2 * s ^ 3 := by
      have := Nat.mul_le_mul_left (s ^ 2) h4'
      linarith
    have e : s ^ 2 * s ^ 3 = s ^ 5 := by ring
    have : 2 ≤ s ^ 2 := by nlinarith
    omega
  · have : s ^ 6 = s ^ 5 * s := by ring
    rw [this]
    have := Nat.mul_le_mul_left (s ^ 5) h4
    linarith

theorem ineq_s_U4 {s : ℕ} (hs : 3 ≤ s) : 3 * ((s ^ 2 - 1) * (s ^ 3 + 1)) < s ^ 6 - 1 := by
  rcases (show s = 3 ∨ 4 ≤ s by omega) with rfl | h4
  · norm_num
  · obtain ⟨h1, h2, h3⟩ := ineq_s_pm h4
    exact lt_of_le_of_lt h1 (by omega)

theorem ineq_s_UU {s : ℕ} (hs : 3 ≤ s) : 3 * ((s ^ 2 - 1) * (s ^ 3 + 1)) < s ^ 6 + 1 := by
  rcases (show s = 3 ∨ 4 ≤ s by omega) with rfl | h4
  · norm_num
  · obtain ⟨h1, h2, h3⟩ := ineq_s_pm h4
    exact lt_of_le_of_lt h1 (by omega)

theorem ineq_s_U3A3 {s : ℕ} (hs : 2 ≤ s) : 3 * ((s ^ 2 - 1) * (s ^ 3 - 1)) < s ^ 6 + 1 := by
  rcases (show s = 2 ∨ s = 3 ∨ 4 ≤ s by omega) with rfl | rfl | h4
  · norm_num
  · norm_num
  · have hA : (s ^ 2 - 1) * (s ^ 3 - 1) ≤ s ^ 2 * s ^ 3 :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have h1 : 3 * ((s ^ 2 - 1) * (s ^ 3 - 1)) ≤ 3 * s ^ 5 := by
      calc 3 * ((s ^ 2 - 1) * (s ^ 3 - 1)) ≤ 3 * (s ^ 2 * s ^ 3) := Nat.mul_le_mul_left 3 hA
        _ = 3 * s ^ 5 := by ring
    have h5 : 4 * s ^ 5 ≤ s ^ 6 := by
      have : s ^ 6 = s ^ 5 * s := by ring
      rw [this]
      have := Nat.mul_le_mul_left (s ^ 5) h4
      linarith
    have h6 : 2 ≤ s ^ 5 := le_trans (by norm_num) (Nat.pow_le_pow_left h4 5)
    exact lt_of_le_of_lt h1 (by omega)

theorem core_key {M d1 d2 Z P1 P2 : ℕ} (hZ : 0 < Z) (E1 : M * d1 = Z * P1) (E2 : M * d2 = Z * P2) :
    P1 * d2 = P2 * d1 := cancel_common hZ E1 E2

theorem same_A2_B2 {M p a b : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hF1 : M.factorization p = 3 * a) (hF2 : M.factorization p = 4 * b)
    (E1 : M * Nat.gcd 3 (p ^ a - 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)))
    (E2 : M * Nat.gcd 2 (p ^ b - 1) = (p ^ b) ^ 4 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 4 - 1))) :
    False := by
  have hab : 3 * a = 4 * b := by omega
  obtain ⟨j, rfl, rfl⟩ : ∃ j, a = 4 * j ∧ b = 3 * j := ⟨a / 4, by omega, by omega⟩
  have hp2 : 2 ≤ p ^ j := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
  rw [show p ^ (4 * j) = (p ^ j) ^ 4 by ring] at E1
  rw [show p ^ (3 * j) = (p ^ j) ^ 3 by ring] at E2
  generalize p ^ j = t at hp2 E1 E2
  have h12 : 2 ≤ t ^ 12 := le_trans hp2 (le_self_pow (by omega) (by norm_num))
  exact core_gen (Z := t ^ 12 * (t ^ 12 - 1)) (P1 := t ^ 8 - 1) (P2 := t ^ 6 - 1)
    (Nat.mul_pos (by positivity) (by omega))
    (by rw [E1, show (t ^ 4) ^ 3 = t ^ 12 by ring, show (t ^ 4) ^ 2 = t ^ 8 by ring]; ring)
    (by rw [E2, show (t ^ 3) ^ 4 = t ^ 12 by ring, show (t ^ 3) ^ 2 = t ^ 6 by ring]; ring)
    (Nat.gcd_le_left _ (by norm_num)) (Nat.gcd_pos_of_pos_left _ (by norm_num)) (ineq_t_A2B2 hp2)

theorem same_U3_B2 {M p a b : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hF1 : M.factorization p = 3 * a) (hF2 : M.factorization p = 4 * b)
    (E1 : M * Nat.gcd 3 (p ^ a + 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)))
    (E2 : M * Nat.gcd 2 (p ^ b - 1) = (p ^ b) ^ 4 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 4 - 1))) :
    False := by
  have hab : 3 * a = 4 * b := by omega
  obtain ⟨j, rfl, rfl⟩ : ∃ j, a = 4 * j ∧ b = 3 * j := ⟨a / 4, by omega, by omega⟩
  have hp2 : 2 ≤ p ^ j := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
  rw [show p ^ (4 * j) = (p ^ j) ^ 4 by ring] at E1
  rw [show p ^ (3 * j) = (p ^ j) ^ 3 by ring] at E2
  generalize p ^ j = t at hp2 E1 E2
  exact core_gen (Z := t ^ 12) (P1 := (t ^ 8 - 1) * (t ^ 12 + 1)) (P2 := (t ^ 6 - 1) * (t ^ 12 - 1))
    (by positivity)
    (by rw [E1, show (t ^ 4) ^ 3 = t ^ 12 by ring, show (t ^ 4) ^ 2 = t ^ 8 by ring])
    (by rw [E2, show (t ^ 3) ^ 4 = t ^ 12 by ring, show (t ^ 3) ^ 2 = t ^ 6 by ring])
    (Nat.gcd_le_left _ (by norm_num)) (Nat.gcd_pos_of_pos_left _ (by norm_num)) (ineq_t_U3B2 hp2)

theorem same_A2_A3 {M p a b : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b) (hs2 : p ^ b ≠ 2)
    (hF1 : M.factorization p = 3 * a) (hF2 : M.factorization p = 6 * b)
    (E1 : M * Nat.gcd 3 (p ^ a - 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)))
    (E2 : M * Nat.gcd 4 (p ^ b - 1) =
      (p ^ b) ^ 6 * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 3 - 1) * ((p ^ b) ^ 4 - 1)))) : False := by
  have hab : a = 2 * b := by omega
  subst hab
  rw [show p ^ (2 * b) = (p ^ b) ^ 2 by ring] at E1
  have hpb : 2 ≤ p ^ b := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
  generalize p ^ b = s at hpb hs2 E1 E2
  have hs3 : 3 ≤ s := by omega
  have h4 : 2 ≤ s ^ 4 := le_trans hpb (le_self_pow (by omega) (by norm_num))
  exact core_gen (Z := s ^ 6 * (s ^ 4 - 1)) (P1 := s ^ 6 - 1) (P2 := (s ^ 2 - 1) * (s ^ 3 - 1))
    (Nat.mul_pos (by positivity) (by omega))
    (by rw [E1, show (s ^ 2) ^ 3 = s ^ 6 by ring, show (s ^ 2) ^ 2 = s ^ 4 by ring]; ring)
    (by rw [E2]; ring)
    (Nat.gcd_le_left _ (by norm_num)) (Nat.gcd_pos_of_pos_left _ (by norm_num)) (ineq_s_A3 hs3)

theorem same_A2_U4 {M p a b : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hF1 : M.factorization p = 3 * a) (hF2 : M.factorization p = 6 * b)
    (E1 : M * Nat.gcd 3 (p ^ a - 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)))
    (E2 : M * Nat.gcd 4 (p ^ b + 1) =
      (p ^ b) ^ 6 * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 3 + 1) * ((p ^ b) ^ 4 - 1)))) : False := by
  have hab : a = 2 * b := by omega
  subst hab
  rw [show p ^ (2 * b) = (p ^ b) ^ 2 by ring] at E1
  have hpb : 2 ≤ p ^ b := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
  generalize p ^ b = s at hpb E1 E2
  have h4 : 2 ≤ s ^ 4 := le_trans hpb (le_self_pow (by omega) (by norm_num))
  have hz : 0 < s ^ 6 * (s ^ 4 - 1) := Nat.mul_pos (by positivity) (by omega)
  have E1' : M * Nat.gcd 3 (s ^ 2 - 1) = s ^ 6 * (s ^ 4 - 1) * (s ^ 6 - 1) := by
    rw [E1, show (s ^ 2) ^ 3 = s ^ 6 by ring, show (s ^ 2) ^ 2 = s ^ 4 by ring]; ring
  have E2' : M * Nat.gcd 4 (s + 1) = s ^ 6 * (s ^ 4 - 1) * ((s ^ 2 - 1) * (s ^ 3 + 1)) := by
    rw [E2]; ring
  by_cases hs3 : 3 ≤ s
  · exact core_gen hz E1' E2' (Nat.gcd_le_left _ (by norm_num))
      (Nat.gcd_pos_of_pos_left _ (by norm_num)) (ineq_s_U4 hs3)
  · obtain rfl : s = 2 := by omega
    have key := core_key hz E1' E2'
    norm_num at key

theorem same_U3_A3 {M p a b : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hF1 : M.factorization p = 3 * a) (hF2 : M.factorization p = 6 * b)
    (E1 : M * Nat.gcd 3 (p ^ a + 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)))
    (E2 : M * Nat.gcd 4 (p ^ b - 1) =
      (p ^ b) ^ 6 * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 3 - 1) * ((p ^ b) ^ 4 - 1)))) : False := by
  have hab : a = 2 * b := by omega
  subst hab
  rw [show p ^ (2 * b) = (p ^ b) ^ 2 by ring] at E1
  have hpb : 2 ≤ p ^ b := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
  generalize p ^ b = s at hpb E1 E2
  have h4 : 2 ≤ s ^ 4 := le_trans hpb (le_self_pow (by omega) (by norm_num))
  exact core_gen (Z := s ^ 6 * (s ^ 4 - 1)) (P1 := s ^ 6 + 1) (P2 := (s ^ 2 - 1) * (s ^ 3 - 1))
    (Nat.mul_pos (by positivity) (by omega))
    (by rw [E1, show (s ^ 2) ^ 3 = s ^ 6 by ring, show (s ^ 2) ^ 2 = s ^ 4 by ring]; ring)
    (by rw [E2]; ring)
    (Nat.gcd_le_left _ (by norm_num)) (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (ineq_s_U3A3 hpb)

theorem same_U3_U4 {M p a b : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hF1 : M.factorization p = 3 * a) (hF2 : M.factorization p = 6 * b)
    (E1 : M * Nat.gcd 3 (p ^ a + 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)))
    (E2 : M * Nat.gcd 4 (p ^ b + 1) =
      (p ^ b) ^ 6 * (((p ^ b) ^ 2 - 1) * (((p ^ b) ^ 3 + 1) * ((p ^ b) ^ 4 - 1)))) : False := by
  have hab : a = 2 * b := by omega
  subst hab
  rw [show p ^ (2 * b) = (p ^ b) ^ 2 by ring] at E1
  have hpb : 2 ≤ p ^ b := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
  generalize p ^ b = s at hpb E1 E2
  have h4 : 2 ≤ s ^ 4 := le_trans hpb (le_self_pow (by omega) (by norm_num))
  have hz : 0 < s ^ 6 * (s ^ 4 - 1) := Nat.mul_pos (by positivity) (by omega)
  have E1' : M * Nat.gcd 3 (s ^ 2 + 1) = s ^ 6 * (s ^ 4 - 1) * (s ^ 6 + 1) := by
    rw [E1, show (s ^ 2) ^ 3 = s ^ 6 by ring, show (s ^ 2) ^ 2 = s ^ 4 by ring]; ring
  have E2' : M * Nat.gcd 4 (s + 1) = s ^ 6 * (s ^ 4 - 1) * ((s ^ 2 - 1) * (s ^ 3 + 1)) := by
    rw [E2]; ring
  by_cases hs3 : 3 ≤ s
  · exact core_gen hz E1' E2' (Nat.gcd_le_left _ (by norm_num))
      (Nat.gcd_pos_of_pos_left _ (by norm_num)) (ineq_s_UU hs3)
  · obtain rfl : s = 2 := by omega
    have key := core_key hz E1' E2'
    norm_num at key

theorem id_sq (v : ℕ) : (v + 1) ^ 2 - 1 = v * (v + 2) := by
  rw [show (v + 1) ^ 2 = v * (v + 2) + 1 by ring]; exact Nat.add_sub_cancel _ _

theorem id_cube (v : ℕ) : (v + 1) ^ 3 - 1 = v * (v ^ 2 + 3 * v + 3) := by
  rw [show (v + 1) ^ 3 = v * (v ^ 2 + 3 * v + 3) + 1 by ring]; exact Nat.add_sub_cancel _ _

theorem id_four (v : ℕ) : (v + 1) ^ 4 - 1 = v * (v + 2) * (v ^ 2 + 2 * v + 2) := by
  rw [show (v + 1) ^ 4 = v * (v + 2) * (v ^ 2 + 2 * v + 2) + 1 by ring]; exact Nat.add_sub_cancel _ _

theorem prepL3 {M x p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hx : x = p ^ a)
    (E : M * Nat.gcd 3 (x - 1) = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1))) :
    ∃ v, 1 ≤ v ∧ p ∣ v + 1 ∧ p ^ (a * 3) = (v + 1) ^ 3 ∧
      M * Nat.gcd 3 v = p ^ (a * 3) * (v ^ 2 * (v + 2) * (v ^ 2 + 3 * v + 3)) := by
  have h2 : 2 ≤ x := by rw [hx]; exact le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
  obtain ⟨v, rfl⟩ : ∃ v, x = v + 1 := ⟨x - 1, by omega⟩
  have hpow : p ^ (a * 3) = (v + 1) ^ 3 := by rw [hx, pow_mul]
  refine ⟨v, by omega, ?_, hpow, ?_⟩
  · rw [hx]; exact dvd_pow_self p (by omega)
  · rw [Nat.add_sub_cancel, id_sq, id_cube, ← hpow] at E
    rw [E]; ring

theorem prepU3 {M x p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hx : x = p ^ a)
    (E : M * Nat.gcd 3 (x + 1) = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1))) :
    ∃ v, 1 ≤ v ∧ p ∣ v + 1 ∧ p ^ (a * 3) = (v + 1) ^ 3 ∧
      M * Nat.gcd 3 (v + 2) = p ^ (a * 3) * (v * (v + 2) ^ 2 * (v ^ 2 + v + 1)) := by
  have h2 : 2 ≤ x := by rw [hx]; exact le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
  obtain ⟨v, rfl⟩ : ∃ v, x = v + 1 := ⟨x - 1, by omega⟩
  have hpow : p ^ (a * 3) = (v + 1) ^ 3 := by rw [hx, pow_mul]
  refine ⟨v, by omega, ?_, hpow, ?_⟩
  · rw [hx]; exact dvd_pow_self p (by omega)
  · rw [show v + 1 + 1 = v + 2 by ring, id_sq, show (v + 1) ^ 3 + 1 = (v + 2) * (v ^ 2 + v + 1) by ring,
      ← hpow] at E
    rw [E]; ring

theorem prepB2 {M y s b : ℕ} (hs : s.Prime) (hb : 1 ≤ b) (hy : y = s ^ b)
    (E : M * Nat.gcd 2 (y - 1) = y ^ 4 * ((y ^ 2 - 1) * (y ^ 4 - 1))) :
    ∃ u, 1 ≤ u ∧ s ∣ u + 1 ∧ u + 1 = s ^ b ∧ s ^ (b * 4) = (u + 1) ^ 4 ∧
      M * Nat.gcd 2 u = s ^ (b * 4) * (u ^ 2 * (u + 2) ^ 2 * (u ^ 2 + 2 * u + 2)) := by
  have h2 : 2 ≤ y := by rw [hy]; exact le_trans hs.two_le (le_self_pow hs.one_lt.le (by omega))
  obtain ⟨u, rfl⟩ : ∃ u, y = u + 1 := ⟨y - 1, by omega⟩
  have hpow : s ^ (b * 4) = (u + 1) ^ 4 := by rw [hy, pow_mul]
  refine ⟨u, by omega, ?_, hy, hpow, ?_⟩
  · rw [hy]; exact dvd_pow_self s (by omega)
  · rw [Nat.add_sub_cancel, id_sq, id_four, ← hpow] at E
    rw [E]; ring

theorem prepA3 {M y s b : ℕ} (hs : s.Prime) (hb : 1 ≤ b) (hy : y = s ^ b)
    (E : M * Nat.gcd 4 (y - 1) = y ^ 6 * ((y ^ 2 - 1) * ((y ^ 3 - 1) * (y ^ 4 - 1)))) :
    ∃ u, 1 ≤ u ∧ s ∣ u + 1 ∧ u + 1 = s ^ b ∧ s ^ (b * 6) = (u + 1) ^ 6 ∧
      M * Nat.gcd 4 u = s ^ (b * 6) * (u ^ 3 * (u ^ 2 + 3 * u + 3) * ((u + 2) ^ 2 * (u ^ 2 + 2 * u + 2))) := by
  have h2 : 2 ≤ y := by rw [hy]; exact le_trans hs.two_le (le_self_pow hs.one_lt.le (by omega))
  obtain ⟨u, rfl⟩ : ∃ u, y = u + 1 := ⟨y - 1, by omega⟩
  have hpow : s ^ (b * 6) = (u + 1) ^ 6 := by rw [hy, pow_mul]
  refine ⟨u, by omega, ?_, hy, hpow, ?_⟩
  · rw [hy]; exact dvd_pow_self s (by omega)
  · rw [Nat.add_sub_cancel, id_sq, id_cube, id_four, ← hpow] at E
    rw [E]; ring

theorem prepU4 {M y s b : ℕ} (hs : s.Prime) (hb : 1 ≤ b) (hy : y = s ^ b)
    (E : M * Nat.gcd 4 (y + 1) = y ^ 6 * ((y ^ 2 - 1) * ((y ^ 3 + 1) * (y ^ 4 - 1)))) :
    ∃ u, 1 ≤ u ∧ s ∣ u + 1 ∧ u + 1 = s ^ b ∧ s ^ (b * 6) = (u + 1) ^ 6 ∧
      M * Nat.gcd 4 (u + 2) = s ^ (b * 6) * ((u + 2) ^ 3 * (u ^ 2 + u + 1) * (u ^ 2 * (u ^ 2 + 2 * u + 2))) := by
  have h2 : 2 ≤ y := by rw [hy]; exact le_trans hs.two_le (le_self_pow hs.one_lt.le (by omega))
  obtain ⟨u, rfl⟩ : ∃ u, y = u + 1 := ⟨y - 1, by omega⟩
  have hpow : s ^ (b * 6) = (u + 1) ^ 6 := by rw [hy, pow_mul]
  refine ⟨u, by omega, ?_, hy, hpow, ?_⟩
  · rw [hy]; exact dvd_pow_self s (by omega)
  · rw [show u + 1 + 1 = u + 2 by ring, show (u + 1) ^ 3 + 1 = (u + 2) * (u ^ 2 + u + 1) by ring,
      id_sq, id_four, ← hpow] at E
    rw [E]; ring

theorem five_le {s : ℕ} (hs : s.Prime) (h2 : s ≠ 2) (h3 : s ≠ 3) : 5 ≤ s := by
  by_contra hc
  have h4 : s = 4 := by have := hs.two_le; omega
  subst h4
  norm_num at hs

theorem pn_pow {p s b : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) : ¬ p ∣ s ^ b := fun h =>
  hps ((Nat.prime_dvd_prime_iff_eq hp hs).1 (hp.dvd_of_dvd_pow h))

theorem cross_L3_B2 {M p s a b : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) (hp2 : p ≠ 2)
    (hs2 : s ≠ 2) (ha : 1 ≤ a) (hb : 1 ≤ b) (hy3 : s ^ b ≠ 3)
    (E1 : M * Nat.gcd 3 (p ^ a - 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)))
    (E2 : M * Nat.gcd 2 (s ^ b - 1) = (s ^ b) ^ 4 * (((s ^ b) ^ 2 - 1) * ((s ^ b) ^ 4 - 1))) :
    False := by
  obtain ⟨v, hv1, hpv, hpow, E1⟩ := prepL3 hp ha rfl E1
  obtain ⟨u, hu1, hsu, hyu, hs4, E2⟩ := prepB2 hs hb rfl E2
  obtain ⟨c12, c1, c2⟩ := cop_all (e1 := a * 3) (e2 := b * 4) hp hs hps
    (nd_L hp hpv (Nat.gcd_dvd_right _ _)) (nd_L hs hsu (Nat.gcd_dvd_right _ _))
  obtain ⟨hR2, hR1⟩ := gen_div E1 E2 c12 c1 c2
  have X := bnd_Sp4 hp hp2 hu1 hR2
  rw [hpow] at X
  by_cases hs3 : s = 3
  · subst hs3
    have hb2 : 2 ≤ b := by
      by_contra hc
      obtain rfl : b = 1 := by omega
      norm_num at hy3
    have hu3 : 3 ≤ u := by
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hb2
      norm_num at this
      omega
    have Y := bnd_L33 hv1 hR1
    rw [hs4] at Y
    exact fin_b hu3 Y X
  · have hs5 : 5 ≤ s := five_le hs hs2 hs3
    have Y := bnd_L3s hs hs5 hv1 hR1
    rw [hs4] at Y
    exact fin_a hu1 Y X

theorem cross_U3_B2 {M p s a b : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) (hp2 : p ≠ 2)
    (hs2 : s ≠ 2) (ha : 1 ≤ a) (hb : 1 ≤ b) (hy3 : s ^ b ≠ 3)
    (E1 : M * Nat.gcd 3 (p ^ a + 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)))
    (E2 : M * Nat.gcd 2 (s ^ b - 1) = (s ^ b) ^ 4 * (((s ^ b) ^ 2 - 1) * ((s ^ b) ^ 4 - 1))) :
    False := by
  obtain ⟨v, hv1, hpv, hpow, E1⟩ := prepU3 hp ha rfl E1
  obtain ⟨u, hu1, hsu, hyu, hs4, E2⟩ := prepB2 hs hb rfl E2
  obtain ⟨c12, c1, c2⟩ := cop_all (e1 := a * 3) (e2 := b * 4) hp hs hps
    (nd_U hp hpv (Nat.gcd_dvd_right _ _)) (nd_L hs hsu (Nat.gcd_dvd_right _ _))
  obtain ⟨hR2, hR1⟩ := gen_div E1 E2 c12 c1 c2
  have X := bnd_Sp4 hp hp2 hu1 hR2
  rw [hpow] at X
  by_cases hs3 : s = 3
  · subst hs3
    have hb2 : 2 ≤ b := by
      by_contra hc
      obtain rfl : b = 1 := by omega
      norm_num at hy3
    have hu3 : 3 ≤ u := by
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hb2
      norm_num at this
      omega
    have Y := bnd_U33 hv1 hR1
    rw [hs4] at Y
    exact fin_b hu3 Y X
  · have hs5 : 5 ≤ s := five_le hs hs2 hs3
    have Y := bnd_U3s hs hs5 hv1 hR1
    rw [hs4] at Y
    exact fin_a hu1 Y X

theorem cross_L3_A3 {M p s a b : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) (hp2 : p ≠ 2)
    (hs2 : s ≠ 2) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (E1 : M * Nat.gcd 3 (p ^ a - 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)))
    (E2 : M * Nat.gcd 4 (s ^ b - 1) =
      (s ^ b) ^ 6 * (((s ^ b) ^ 2 - 1) * (((s ^ b) ^ 3 - 1) * ((s ^ b) ^ 4 - 1)))) : False := by
  obtain ⟨v, hv1, hpv, hpow, E1⟩ := prepL3 hp ha rfl E1
  obtain ⟨u, hu1, hsu, hyu, hs6, E2⟩ := prepA3 hs hb rfl E2
  obtain ⟨c12, c1, c2⟩ := cop_all (e1 := a * 3) (e2 := b * 6) hp hs hps
    (nd_L hp hpv (Nat.gcd_dvd_right _ _)) (nd_L hs hsu (Nat.gcd_dvd_right _ _))
  obtain ⟨hR2, hR1⟩ := gen_div E1 E2 c12 c1 c2
  have hpy : ¬ p ∣ u + 1 := by rw [hyu]; exact pn_pow hp hs hps
  have hsb : s ≤ s ^ b := le_self_pow (by have := hs.two_le; omega) (by omega)
  by_cases hs3 : s = 3
  · subst hs3
    have Y := bnd_L33 hv1 hR1
    have X := bnd_L4b hp (five_le hp hp2 hps) hpy hu1 hR2
    rw [hpow] at X
    rw [hs6] at Y
    exact fin_d (by omega) Y X
  · have hs5 : 5 ≤ s := five_le hs hs2 hs3
    have Y := bnd_L3s hs hs5 hv1 hR1
    have X := bnd_L4s hp hp2 hpy hu1 hR2
    rw [hpow] at X
    rw [hs6] at Y
    exact fin_e (by omega) Y X
theorem cross_U3_A3 {M p s a b : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) (hp2 : p ≠ 2)
    (hs2 : s ≠ 2) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (E1 : M * Nat.gcd 3 (p ^ a + 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)))
    (E2 : M * Nat.gcd 4 (s ^ b - 1) =
      (s ^ b) ^ 6 * (((s ^ b) ^ 2 - 1) * (((s ^ b) ^ 3 - 1) * ((s ^ b) ^ 4 - 1)))) : False := by
  obtain ⟨v, hv1, hpv, hpow, E1⟩ := prepU3 hp ha rfl E1
  obtain ⟨u, hu1, hsu, hyu, hs6, E2⟩ := prepA3 hs hb rfl E2
  obtain ⟨c12, c1, c2⟩ := cop_all (e1 := a * 3) (e2 := b * 6) hp hs hps
    (nd_U hp hpv (Nat.gcd_dvd_right _ _)) (nd_L hs hsu (Nat.gcd_dvd_right _ _))
  obtain ⟨hR2, hR1⟩ := gen_div E1 E2 c12 c1 c2
  have hpy : ¬ p ∣ u + 1 := by rw [hyu]; exact pn_pow hp hs hps
  have hsb : s ≤ s ^ b := le_self_pow (by have := hs.two_le; omega) (by omega)
  by_cases hs3 : s = 3
  · subst hs3
    have Y := bnd_U33 hv1 hR1
    have X := bnd_L4b hp (five_le hp hp2 hps) hpy hu1 hR2
    rw [hpow] at X
    rw [hs6] at Y
    exact fin_d (by omega) Y X
  · have hs5 : 5 ≤ s := five_le hs hs2 hs3
    have Y := bnd_U3s hs hs5 hv1 hR1
    have X := bnd_L4s hp hp2 hpy hu1 hR2
    rw [hpow] at X
    rw [hs6] at Y
    exact fin_e (by omega) Y X
theorem cross_L3_U4 {M p s a b : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) (hp2 : p ≠ 2)
    (hs2 : s ≠ 2) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (E1 : M * Nat.gcd 3 (p ^ a - 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)))
    (E2 : M * Nat.gcd 4 (s ^ b + 1) =
      (s ^ b) ^ 6 * (((s ^ b) ^ 2 - 1) * (((s ^ b) ^ 3 + 1) * ((s ^ b) ^ 4 - 1)))) : False := by
  obtain ⟨v, hv1, hpv, hpow, E1⟩ := prepL3 hp ha rfl E1
  obtain ⟨u, hu1, hsu, hyu, hs6, E2⟩ := prepU4 hs hb rfl E2
  obtain ⟨c12, c1, c2⟩ := cop_all (e1 := a * 3) (e2 := b * 6) hp hs hps
    (nd_L hp hpv (Nat.gcd_dvd_right _ _)) (nd_U hs hsu (Nat.gcd_dvd_right _ _))
  obtain ⟨hR2, hR1⟩ := gen_div E1 E2 c12 c1 c2
  have hpy : ¬ p ∣ u + 1 := by rw [hyu]; exact pn_pow hp hs hps
  have hsb : s ≤ s ^ b := le_self_pow (by have := hs.two_le; omega) (by omega)
  by_cases hs3 : s = 3
  · subst hs3
    have Y := bnd_L33 hv1 hR1
    have X := bnd_U4b hp (five_le hp hp2 hps) hpy hu1 hR2
    rw [hpow] at X
    rw [hs6] at Y
    exact fin_d (by omega) Y X
  · have hs5 : 5 ≤ s := five_le hs hs2 hs3
    have Y := bnd_L3s hs hs5 hv1 hR1
    have X := bnd_U4s hp hp2 hpy hu1 hR2
    rw [hpow] at X
    rw [hs6] at Y
    exact fin_e (by omega) Y X
theorem cross_U3_U4 {M p s a b : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) (hp2 : p ≠ 2)
    (hs2 : s ≠ 2) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (E1 : M * Nat.gcd 3 (p ^ a + 1) = (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)))
    (E2 : M * Nat.gcd 4 (s ^ b + 1) =
      (s ^ b) ^ 6 * (((s ^ b) ^ 2 - 1) * (((s ^ b) ^ 3 + 1) * ((s ^ b) ^ 4 - 1)))) : False := by
  obtain ⟨v, hv1, hpv, hpow, E1⟩ := prepU3 hp ha rfl E1
  obtain ⟨u, hu1, hsu, hyu, hs6, E2⟩ := prepU4 hs hb rfl E2
  obtain ⟨c12, c1, c2⟩ := cop_all (e1 := a * 3) (e2 := b * 6) hp hs hps
    (nd_U hp hpv (Nat.gcd_dvd_right _ _)) (nd_U hs hsu (Nat.gcd_dvd_right _ _))
  obtain ⟨hR2, hR1⟩ := gen_div E1 E2 c12 c1 c2
  have hpy : ¬ p ∣ u + 1 := by rw [hyu]; exact pn_pow hp hs hps
  have hsb : s ≤ s ^ b := le_self_pow (by have := hs.two_le; omega) (by omega)
  by_cases hs3 : s = 3
  · subst hs3
    have Y := bnd_U33 hv1 hR1
    have X := bnd_U4b hp (five_le hp hp2 hps) hpy hu1 hR2
    rw [hpow] at X
    rw [hs6] at Y
    exact fin_d (by omega) Y X
  · have hs5 : 5 ≤ s := five_le hs hs2 hs3
    have Y := bnd_U3s hs hs5 hv1 hR1
    have X := bnd_U4s hp hp2 hpy hu1 hR2
    rw [hpow] at X
    rw [hs6] at Y
    exact fin_e (by omega) Y X
section Cert

theorem raw_eq {S : Type} [Group S] {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hb : CFSG.Blueprint.LieModel S t n p f) :
    Nat.card S * CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t n (p ^ f) =
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator t n (p ^ f) ∧
      (Nat.card S).factorization p =
        CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * f := by
  have h := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S t n p f
    (CFSG.Blueprint.LieModel.admissible hb) hb
  exact ⟨h.2.1, h.2.2⟩

theorem orderEq_A2 {S : Type} [Group S] (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 Q).Valid) (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 Q, hv⟩) :
    ∃ hb : CFSG.Blueprint.LieModel S .PSL 3 Q.p Q.exponent,
      Nat.card S * Nat.gcd 3 (Q.p ^ Q.exponent - 1) =
        (Q.p ^ Q.exponent) ^ 3 * (((Q.p ^ Q.exponent) ^ 2 - 1) * ((Q.p ^ Q.exponent) ^ 3 - 1)) ∧
      (Nat.card S).factorization Q.p = 3 * Q.exponent := by
  have hb : CFSG.Blueprint.LieModel S .PSL 3 Q.p Q.exponent :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide)
      (CFSG.Models.lieModel_A 2 Q hv e)
  obtain ⟨h, hf⟩ := raw_eq hb
  refine ⟨hb, ?_, hf⟩
  simp only [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] at h
  rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by decide)] at h
  norm_num at h
  exact h

theorem orderEq_U3 {S : Type} [Group S] (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 Q, hv⟩) :
    ∃ hb : CFSG.Blueprint.LieModel S .PSU 3 Q.p Q.exponent,
      Nat.card S * Nat.gcd 3 (Q.p ^ Q.exponent + 1) =
        (Q.p ^ Q.exponent) ^ 3 * (((Q.p ^ Q.exponent) ^ 2 - 1) * ((Q.p ^ Q.exponent) ^ 3 + 1)) ∧
      (Nat.card S).factorization Q.p = 3 * Q.exponent := by
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 Q, hv⟩ = Q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 Q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 Q, hv⟩ = Q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 Q
  have hm := CFSG.Models.lieModel_twistedA 2 Q hv e
  rw [hc, hf] at hm
  have hb : CFSG.Blueprint.LieModel S .PSU 3 Q.p Q.exponent :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm
  obtain ⟨h, hfa⟩ := raw_eq hb
  refine ⟨hb, ?_, hfa⟩
  simp only [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] at h
  rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by decide)] at h
  norm_num at h
  exact h

theorem orderEq_B2 {S : Type} [Group S] (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 Q).Valid) (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 Q, hv⟩) :
    ∃ hb : CFSG.Blueprint.LieModel S .PSp 2 Q.p Q.exponent,
      Nat.card S * Nat.gcd 2 (Q.p ^ Q.exponent - 1) =
        (Q.p ^ Q.exponent) ^ 4 * (((Q.p ^ Q.exponent) ^ 2 - 1) * ((Q.p ^ Q.exponent) ^ 4 - 1)) ∧
      (Nat.card S).factorization Q.p = 4 * Q.exponent := by
  have hb : CFSG.Blueprint.LieModel S .PSp 2 Q.p Q.exponent :=
    Or.inl ⟨by decide, CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 Q hv e⟩
  obtain ⟨h, hf⟩ := raw_eq hb
  refine ⟨hb, ?_, hf⟩
  simp only [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] at h
  rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.prod_pair (by decide)] at h
  norm_num at h
  exact h

theorem orderEq_A3 {S : Type} [Group S] (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 3 Q).Valid) (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 3 Q, hv⟩) :
    ∃ hb : CFSG.Blueprint.LieModel S .PSL 4 Q.p Q.exponent,
      Nat.card S * Nat.gcd 4 (Q.p ^ Q.exponent - 1) =
        (Q.p ^ Q.exponent) ^ 6 * (((Q.p ^ Q.exponent) ^ 2 - 1) *
          (((Q.p ^ Q.exponent) ^ 3 - 1) * ((Q.p ^ Q.exponent) ^ 4 - 1))) ∧
      (Nat.card S).factorization Q.p = 6 * Q.exponent := by
  have hb : CFSG.Blueprint.LieModel S .PSL 4 Q.p Q.exponent :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide)
      (CFSG.Models.lieModel_A 3 Q hv e)
  obtain ⟨h, hf⟩ := raw_eq hb
  refine ⟨hb, ?_, hf⟩
  simp only [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] at h
  rw [show Finset.Icc 2 4 = {2, 3, 4} from by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide)] at h
  norm_num at h
  exact h

theorem orderEq_U4 {S : Type} [Group S] (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 Q, hv⟩) :
    ∃ hb : CFSG.Blueprint.LieModel S .PSU 4 Q.p Q.exponent,
      Nat.card S * Nat.gcd 4 (Q.p ^ Q.exponent + 1) =
        (Q.p ^ Q.exponent) ^ 6 * (((Q.p ^ Q.exponent) ^ 2 - 1) *
          (((Q.p ^ Q.exponent) ^ 3 + 1) * ((Q.p ^ Q.exponent) ^ 4 - 1))) ∧
      (Nat.card S).factorization Q.p = 6 * Q.exponent := by
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 Q, hv⟩ = Q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 3 Q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 Q, hv⟩ = Q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 3 Q
  have hm := CFSG.Models.lieModel_twistedA 3 Q hv e
  rw [hc, hf] at hm
  have hb : CFSG.Blueprint.LieModel S .PSU 4 Q.p Q.exponent :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm
  obtain ⟨h, hfa⟩ := raw_eq hb
  refine ⟨hb, ?_, hfa⟩
  simp only [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] at h
  rw [show Finset.Icc 2 4 = {2, 3, 4} from by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide)] at h
  norm_num at h
  exact h

theorem char2_absurd {S : Type} [Group S] {t t' : CFSG.Open.StatedLieTag} {n n' f p g : ℕ}
    (hb : CFSG.Blueprint.LieModel S t n 2 f) (hb' : CFSG.Blueprint.LieModel S t' n' p g)
    (hp2 : p ≠ 2) (h1 : ¬ (t = .PSL ∧ n = 2)) (h2 : ¬ (t' = .PSL ∧ n' = 2))
    (h3 : ¬ (t = .PSU ∧ n = 4 ∧ t' = .PSp ∧ n' = 2)) : False := by
  rcases CFSG.SeitzReduction.CrossChar.crossChar_arith (CFSG.Blueprint.LieModel.admissible hb)
      (CFSG.Blueprint.LieModel.admissible hb') hp2 (raw_eq hb).1 (raw_eq hb').1 with
    ⟨ht, hn, -, ht', hn', -⟩ | ⟨ht, hn, -, ht', hn', -⟩ | ⟨ht, hn, -, ht', hn', -⟩
  · exact h1 ⟨ht, hn⟩
  · exact h2 ⟨ht', hn'⟩
  · exact h3 ⟨ht, hn, ht', hn'⟩

theorem dispatch {S : Type} [Group S] {t t' : CFSG.Open.StatedLieTag} {n n' p p' a b : ℕ}
    (hb1 : CFSG.Blueprint.LieModel S t n p a) (hb2 : CFSG.Blueprint.LieModel S t' n' p' b)
    (h1 : ¬ (t = .PSL ∧ n = 2)) (h2 : ¬ (t' = .PSL ∧ n' = 2))
    (h3 : ¬ (t = .PSU ∧ n = 4 ∧ t' = .PSp ∧ n' = 2))
    (h3' : ¬ (t' = .PSU ∧ n' = 4 ∧ t = .PSp ∧ n = 2))
    (same : p = p' → False) (cross : p ≠ p' → p ≠ 2 → p' ≠ 2 → False) : False := by
  by_cases hpp : p = p'
  · exact same hpp
  by_cases hp2 : p = 2
  · subst hp2
    exact char2_absurd hb1 hb2 (Ne.symm hpp) h1 h2 h3
  by_cases hp2' : p' = 2
  · subst hp2'
    exact char2_absurd hb2 hb1 hpp h2 h1 h3'
  exact cross hpp hp2 hp2'

theorem pair_A2_B2 {S : Type} [Group S] (Q Q' : TauCeti.PrimePower)
    (hA : (TauCeti.LieTypeIndex.A 2 Q).Valid) (eA : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 Q, hA⟩)
    (hB : (TauCeti.LieTypeIndex.B 2 Q').Valid)
    (eB : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 Q', hB⟩) : False := by
  obtain ⟨hb1, E1, F1⟩ := orderEq_A2 Q hA eA
  obtain ⟨hb2, E2, F2⟩ := orderEq_B2 Q' hB eB
  exact dispatch hb1 hb2 (by decide) (by decide) (by decide) (by decide)
    (fun hpp => by
      rw [← hpp] at E2
      exact same_A2_B2 Q.prime_p Q.exponent_pos Q'.exponent_pos F1 (by rw [hpp]; exact F2) E1 E2)
    (fun hpp h1 h2 => cross_L3_B2 Q.prime_p Q'.prime_p hpp h1 h2 Q.exponent_pos Q'.exponent_pos
      (valid_B2_ne3 hB) E1 E2)

theorem pair_A2_A3 {S : Type} [Group S] (Q Q' : TauCeti.PrimePower)
    (hA : (TauCeti.LieTypeIndex.A 2 Q).Valid) (eA : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 Q, hA⟩)
    (hB : (TauCeti.LieTypeIndex.A 3 Q').Valid)
    (eB : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 3 Q', hB⟩) : False := by
  obtain ⟨hb1, E1, F1⟩ := orderEq_A2 Q hA eA
  obtain ⟨hb2, E2, F2⟩ := orderEq_A3 Q' hB eB
  exact dispatch hb1 hb2 (by decide) (by decide) (by decide) (by decide)
    (fun hpp => by
      rw [← hpp] at E2
      exact same_A2_A3 Q.prime_p Q.exponent_pos Q'.exponent_pos (by rw [hpp]; exact valid_A3_ne2 hB)
        F1 (by rw [hpp]; exact F2) E1 E2)
    (fun hpp h1 h2 => cross_L3_A3 Q.prime_p Q'.prime_p hpp h1 h2 Q.exponent_pos Q'.exponent_pos E1 E2)

theorem pair_A2_U4 {S : Type} [Group S] (Q Q' : TauCeti.PrimePower)
    (hA : (TauCeti.LieTypeIndex.A 2 Q).Valid) (eA : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 Q, hA⟩)
    (hB : (TauCeti.LieTypeIndex.twistedA 3 Q').Valid)
    (eB : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 Q', hB⟩) : False := by
  obtain ⟨hb1, E1, F1⟩ := orderEq_A2 Q hA eA
  obtain ⟨hb2, E2, F2⟩ := orderEq_U4 Q' hB eB
  exact dispatch hb1 hb2 (by decide) (by decide) (by decide) (by decide)
    (fun hpp => by
      rw [← hpp] at E2
      exact same_A2_U4 Q.prime_p Q.exponent_pos Q'.exponent_pos F1 (by rw [hpp]; exact F2) E1 E2)
    (fun hpp h1 h2 => cross_L3_U4 Q.prime_p Q'.prime_p hpp h1 h2 Q.exponent_pos Q'.exponent_pos E1 E2)

theorem pair_U3_B2 {S : Type} [Group S] (Q Q' : TauCeti.PrimePower)
    (hA : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid)
    (eA : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 Q, hA⟩)
    (hB : (TauCeti.LieTypeIndex.B 2 Q').Valid) (eB : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 Q', hB⟩) :
    False := by
  obtain ⟨hb1, E1, F1⟩ := orderEq_U3 Q hA eA
  obtain ⟨hb2, E2, F2⟩ := orderEq_B2 Q' hB eB
  exact dispatch hb1 hb2 (by decide) (by decide) (by decide) (by decide)
    (fun hpp => by
      rw [← hpp] at E2
      exact same_U3_B2 Q.prime_p Q.exponent_pos Q'.exponent_pos F1 (by rw [hpp]; exact F2) E1 E2)
    (fun hpp h1 h2 => cross_U3_B2 Q.prime_p Q'.prime_p hpp h1 h2 Q.exponent_pos Q'.exponent_pos
      (valid_B2_ne3 hB) E1 E2)

theorem pair_U3_A3 {S : Type} [Group S] (Q Q' : TauCeti.PrimePower)
    (hA : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid)
    (eA : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 Q, hA⟩)
    (hB : (TauCeti.LieTypeIndex.A 3 Q').Valid) (eB : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 3 Q', hB⟩) :
    False := by
  obtain ⟨hb1, E1, F1⟩ := orderEq_U3 Q hA eA
  obtain ⟨hb2, E2, F2⟩ := orderEq_A3 Q' hB eB
  exact dispatch hb1 hb2 (by decide) (by decide) (by decide) (by decide)
    (fun hpp => by
      rw [← hpp] at E2
      exact same_U3_A3 Q.prime_p Q.exponent_pos Q'.exponent_pos F1 (by rw [hpp]; exact F2) E1 E2)
    (fun hpp h1 h2 => cross_U3_A3 Q.prime_p Q'.prime_p hpp h1 h2 Q.exponent_pos Q'.exponent_pos E1 E2)

theorem pair_U3_U4 {S : Type} [Group S] (Q Q' : TauCeti.PrimePower)
    (hA : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid)
    (eA : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 Q, hA⟩)
    (hB : (TauCeti.LieTypeIndex.twistedA 3 Q').Valid)
    (eB : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 Q', hB⟩) : False := by
  obtain ⟨hb1, E1, F1⟩ := orderEq_U3 Q hA eA
  obtain ⟨hb2, E2, F2⟩ := orderEq_U4 Q' hB eB
  exact dispatch hb1 hb2 (by decide) (by decide) (by decide) (by decide)
    (fun hpp => by
      rw [← hpp] at E2
      exact same_U3_U4 Q.prime_p Q.exponent_pos Q'.exponent_pos F1 (by rw [hpp]; exact F2) E1 E2)
    (fun hpp h1 h2 => cross_U3_U4 Q.prime_p Q'.prime_p hpp h1 h2 Q.exponent_pos Q'.exponent_pos E1 E2)

theorem _root_.CFSG.LocalAnalysis.GLTheoremA.lieTypeNonIsoAt_holds : LieTypeNonIsoAt := by
  unfold LieTypeNonIsoAt
  intro S _ Q Q' h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2
  · obtain ⟨hA, ⟨eA⟩⟩ := catalogIs_onLie_eq h1
    obtain ⟨hB, ⟨eB⟩⟩ := catalogIs_onLie_eq h2
    exact pair_A2_B2 Q Q' hA eA hB eB
  · obtain ⟨hA, ⟨eA⟩⟩ := catalogIs_onLie_eq h1
    obtain ⟨hB, ⟨eB⟩⟩ := catalogIs_onLie_eq h2
    exact pair_A2_A3 Q Q' hA eA hB eB
  · obtain ⟨hA, ⟨eA⟩⟩ := catalogIs_onLie_eq h1
    obtain ⟨hB, ⟨eB⟩⟩ := catalogIs_onLie_eq h2
    exact pair_A2_U4 Q Q' hA eA hB eB
  · obtain ⟨hA, ⟨eA⟩⟩ := catalogIs_onLie_eq h1
    obtain ⟨hB, ⟨eB⟩⟩ := catalogIs_onLie_eq h2
    exact pair_U3_B2 Q Q' hA eA hB eB
  · obtain ⟨hA, ⟨eA⟩⟩ := catalogIs_onLie_eq h1
    obtain ⟨hB, ⟨eB⟩⟩ := catalogIs_onLie_eq h2
    exact pair_U3_A3 Q Q' hA eA hB eB
  · obtain ⟨hA, ⟨eA⟩⟩ := catalogIs_onLie_eq h1
    obtain ⟨hB, ⟨eB⟩⟩ := catalogIs_onLie_eq h2
    exact pair_U3_U4 Q Q' hA eA hB eB

end Cert

end CFSG.LocalAnalysis.GLTheoremA.YS05NonIso
