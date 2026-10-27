module

public import CFSG.GH74.QTGen4.Ch5.L34Offender
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.GH74.QTGen4

open CFSG.Open

theorem card_specialLinearGroup_fin_three (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Nat.card_eq_fintype_card, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  set q := Fintype.card K with hqdef
  have e1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_one]
    congr 1
    ring
  have e2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_one]
    congr 1
  rw [e1, e2, show (q ^ 3 - 1) * (q * (q ^ 2 - 1)) * (q ^ 2 * (q - 1)) =
      (q - 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) by ring]
  exact Nat.mul_div_cancel_left _ (by omega)

theorem q_cube_dvd_ordA (n : ℕ) : (2 ^ n) ^ 3 ∣ ordA 2 (2 ^ n) := by
  have hP : (∏ i ∈ Finset.Icc 2 (2 + 1), ((2 ^ n) ^ i - 1)) =
      ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide,
      Finset.prod_pair (show (2 : ℕ) ≠ 3 by norm_num)]
  have hexp : 2 * (2 + 1) / 2 = 3 := by norm_num
  unfold ordA
  rw [hP, hexp]
  set q := 2 ^ n with hq
  have hg : Nat.gcd (2 + 1) (q - 1) ∣ q ^ 3 - 1 :=
    (Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one q 3)
  have hgP : Nat.gcd (2 + 1) (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) :=
    hg.trans (dvd_mul_left _ _)
  have hg0 : Nat.gcd (2 + 1) (q - 1) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left (q - 1) (show 0 < 2 + 1 by norm_num)).ne'
  have hY : Nat.gcd (2 + 1) (q - 1) *
      (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd (2 + 1) (q - 1)) =
        q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    Nat.mul_div_cancel' (dvd_mul_of_dvd_right hgP _)
  have h2: Nat.gcd (2 + 1) (q - 1) * q ^ 3 ∣
      Nat.gcd (2 + 1) (q - 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) /
        Nat.gcd (2 + 1) (q - 1)) := by
    rw [hY, mul_comm (Nat.gcd (2 + 1) (q - 1)) (q ^ 3)]
    exact Nat.mul_dvd_mul_left _ hgP
  exact (mul_dvd_mul_iff_left hg0).1 h2

theorem q_four_dvd_ordBC (n : ℕ) (hn : 1 ≤ n) : (2 ^ n) ^ 4 ∣ ordBC 2 (2 ^ n) := by
  have hodd : ¬ 2 ∣ 2 ^ n - 1 := by
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have hpos : 0 < 2 ^ n := by positivity
    omega
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  unfold ordBC
  rw [hg, Nat.div_one]
  exact dvd_mul_right _ _

theorem q_six_dvd_ordG2 (n : ℕ) : (2 ^ n) ^ 6 ∣ ordG2 (2 ^ n) := by
  unfold ordG2
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

theorem charTwoOrder_PSL (n : ℕ) :
    CFSG.RankThree.PartOne.S12K.charTwoOrder .PSL 3 n = ordA 2 (2 ^ n) := rfl

theorem charTwoOrder_PSp (n : ℕ) :
    CFSG.RankThree.PartOne.S12K.charTwoOrder .PSp 2 n = ordBC 2 (2 ^ n) := rfl

theorem charTwoOrder_G2 (n : ℕ) :
    CFSG.RankThree.PartOne.S12K.charTwoOrder .G2 0 n = ordG2 (2 ^ n) := rfl

theorem stmt11_0_1_gen4 :
    ∀ (G : Type) [Group G] [Finite G], Gen4 G →
      ∀ (T L : Subgroup G), IsSimpleGroup G →
        (∃ a b : G, a * b ≠ b * a) → CFSG.QuasithinUnique.quasithinIsQTKECat G →
        CFSG.Open.quasithinIsSylowTwo T → CFSG.Open.quasithinIsMaximalLocal T L →
        CFSG.Open.quasithinIsFaithfulLocal T L →
        ¬ ∃ n : ℕ, 1 < n ∧
          ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
              Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
            CFSG.Blueprint.LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 n ∨
            CFSG.Blueprint.LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n ∨
            CFSG.Blueprint.LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .G2 0 2 n) := by
  intro G _ _ hG T L _ _ hqtke hsylow _ hfaith
  obtain ⟨P, rfl⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hsylow
  have hInH : CFSG.Quasithin.InH (P : Subgroup G) (L ⊔ P) :=
    ⟨le_sup_right, hfaith.1.2.2.2⟩
  have hd := modO2_dvd_of_inH hG hqtke.2.1 P hInH (le_sup_left : L ≤ L ⊔ P)
  rintro ⟨n, hn, h⟩
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | hpsl | hpsp | hg2
  ·
    have hcardQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := Nat.card_congr e.toEquiv
    rw [card_specialLinearGroup_fin_three K, hK] at hcardQ
    rw [hcardQ] at hd
    have hdvd : (2 ^ n) ^ 3 ∣ 20160 := (dvd_mul_right _ _).trans hd
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      norm_num at hd
    · have h9 : 2 ^ 9 ∣ (2 ^ n) ^ 3 := by
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by omega)
      have := h9.trans hdvd
      norm_num at this
  ·
    obtain ⟨-, hc⟩ := CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hpsl
    rw [hc, charTwoOrder_PSL] at hd
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      exact no_L34_modO2_of_inH hG hqtke.2.1 P hInH le_sup_left hpsl
    · have h9 : 2 ^ 9 ∣ (2 ^ n) ^ 3 := by
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by omega)
      have := h9.trans ((q_cube_dvd_ordA n).trans hd)
      norm_num at this
  ·
    obtain ⟨-, hc⟩ := CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hpsp
    rw [hc, charTwoOrder_PSp] at hd
    have h8 : 2 ^ 8 ∣ (2 ^ n) ^ 4 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    have := h8.trans ((q_four_dvd_ordBC n (by omega)).trans hd)
    norm_num at this
  ·
    obtain ⟨-, hc⟩ := CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hg2
    rw [hc, charTwoOrder_G2] at hd
    have h12 : 2 ^ 12 ∣ (2 ^ n) ^ 6 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    have := h12.trans ((q_six_dvd_ordG2 n).trans hd)
    norm_num at this

end CFSG.GH74.QTGen4
