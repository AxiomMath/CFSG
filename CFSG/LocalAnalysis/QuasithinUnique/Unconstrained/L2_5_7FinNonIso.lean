module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Model
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.Timmesfeld.ClassicalOrders

namespace Fin257

def ModelNum (N n : ℕ) : Prop :=
  ∃ a R : ℕ, (a = 3 ∨ a = 4) ∧ N = (2 ^ n) ^ a * R ∧ Odd R ∧ R < (2 ^ n) ^ (a + 2) ∧ 3 ∣ N

theorem two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

theorem sq_two_pow_mod_three (n : ℕ) : (2 ^ n) ^ 2 % 3 = 1 := by
  rcases two_pow_mod_three n with h | h <;> simp [Nat.pow_mod, h]

theorem three_dvd_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h := sq_two_pow_mod_three n
  have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos n)
  omega

theorem modelNum_L {N n : ℕ} (hn : 1 ≤ n)
    (hN : N = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) / Nat.gcd 3 (2 ^ n - 1)) :
    ModelNum N n := by
  set q := 2 ^ n with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqe : Even q := by
    rw [hq]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  set g := Nat.gcd 3 (q - 1) with hg
  have hgd : g ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    refine dvd_mul_of_dvd_left ?_ _
    refine dvd_trans (Nat.gcd_dvd_right 3 (q - 1)) ?_
    simpa using Nat.sub_dvd_pow_sub_pow q 1 2
  set R := ((q ^ 2 - 1) * (q ^ 3 - 1)) / g with hR
  have hN' : N = q ^ 3 * R := by
    rw [hN, hR, Nat.mul_div_assoc _ hgd]
  have hodd1 : Odd (q ^ 2 - 1) := by
    obtain ⟨j, hj⟩ := Even.pow_of_ne_zero hqe (by norm_num : (2 : ℕ) ≠ 0)
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact ⟨j - 1, by omega⟩
  have hodd2 : Odd (q ^ 3 - 1) := by
    obtain ⟨j, hj⟩ := Even.pow_of_ne_zero hqe (by norm_num : (3 : ℕ) ≠ 0)
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact ⟨j - 1, by omega⟩
  have hRodd : Odd R := by
    have hdvd : R ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.div_dvd_of_dvd hgd
    exact Odd.of_dvd_nat (hodd1.mul hodd2) hdvd
  have hRlt : R < q ^ (3 + 2) := by
    have h1 : R ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.div_le_self _ _
    have h2 : (q ^ 2 - 1) * (q ^ 3 - 1) < q ^ 2 * q ^ 3 := by
      have a1 : q ^ 2 - 1 < q ^ 2 := by
        have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have a2 : q ^ 3 - 1 < q ^ 3 := by
        have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
        omega
      exact Nat.mul_lt_mul'' a1 a2
    calc R < q ^ 2 * q ^ 3 := lt_of_le_of_lt h1 h2
      _ = q ^ (3 + 2) := by ring
  have h3 : 3 ∣ N := by
    have hmod : q % 3 = 1 ∨ q % 3 = 2 := two_pow_mod_three n
    rcases hmod with h1 | h2
    ·
      have hg3 : g = 3 := by
        rw [hg]; apply Nat.gcd_eq_left
        omega
      have hgd3 : 3 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := hg3 ▸ hgd
      have hq1 : 3 ∣ q - 1 := by omega
      obtain ⟨t, ht⟩ := hq1
      have hqt : q = 3 * t + 1 := by
        have : 1 ≤ q := by omega
        omega
      have hN3 : N * 3 = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
        rw [hN, hg3]
        exact Nat.div_mul_cancel (Dvd.dvd.mul_left hgd3 _)
      have e2 : q ^ 2 - 1 = 3 * t * (3 * t + 2) := by
        have : q ^ 2 = 3 * t * (3 * t + 2) + 1 := by rw [hqt]; ring
        omega
      have e3 : q ^ 3 - 1 = 3 * t * (9 * t * t + 9 * t + 3) := by
        have : q ^ 3 = 3 * t * (9 * t * t + 9 * t + 3) + 1 := by rw [hqt]; ring
        omega
      rw [e2, e3] at hN3
      obtain ⟨Y, hY⟩ :
          ∃ Y, Y = q ^ 3 * (t * (3 * t + 2) * (t * (9 * t * t + 9 * t + 3))) := ⟨_, rfl⟩
      have : N * 3 = 9 * Y := by rw [hN3, hY]; ring
      exact ⟨Y, by omega⟩
    ·
      have hg1 : g = 1 := by
        rw [hg]
        have hnd : ¬ 3 ∣ q - 1 := by omega
        rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q - 1)) with h | h
        · exact h
        · exfalso; apply hnd; rw [← h]; exact Nat.gcd_dvd_right 3 (q - 1)
      have : N = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
        rw [hN, hg1, Nat.div_one]
      rw [this]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one n) _) _
  exact ⟨3, R, Or.inl rfl, hN', hRodd, hRlt, h3⟩

theorem modelNum_S {N n : ℕ} (hn : 1 ≤ n)
    (hN : N = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1))) :
    ModelNum N n := by
  set q := 2 ^ n with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqe : Even q := by
    rw [hq]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  refine ⟨4, (q ^ 2 - 1) * (q ^ 4 - 1), Or.inr rfl, hN, ?_, ?_, ?_⟩
  · have h1 : Odd (q ^ 2 - 1) := by
      obtain ⟨j, hj⟩ := Even.pow_of_ne_zero hqe (by norm_num : (2 : ℕ) ≠ 0)
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      exact ⟨j - 1, by omega⟩
    have h2 : Odd (q ^ 4 - 1) := by
      obtain ⟨j, hj⟩ := Even.pow_of_ne_zero hqe (by norm_num : (4 : ℕ) ≠ 0)
      have : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
      exact ⟨j - 1, by omega⟩
    exact h1.mul h2
  · have a1 : q ^ 2 - 1 < q ^ 2 := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have a2 : q ^ 4 - 1 < q ^ 4 := by
      have : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega
    calc (q ^ 2 - 1) * (q ^ 4 - 1) < q ^ 2 * q ^ 4 := Nat.mul_lt_mul'' a1 a2
      _ = q ^ (4 + 2) := by ring
  · rw [hN]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one n) _) _



theorem two_pow_dvd_mul_coprime {m a b : ℕ} (hab : Nat.Coprime a b) (h : 2 ^ m ∣ a * b) :
    2 ^ m ∣ a ∨ 2 ^ m ∣ b := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · left; simp
  · have hp : IsPrimePow (2 ^ m) := (Nat.prime_two.isPrimePow).pow hm.ne'
    exact (Nat.Coprime.isPrimePow_dvd_mul hab hp).1 h

theorem not_l2p_order {q s N R p : ℕ} (hq : 4 ≤ q) (hs : 1 ≤ s) (hQ : 4 * q ^ 2 ≤ 2 ^ s)
    (hN : N = 2 ^ s * R) (hR0 : 0 < R) (hR : R < 2 ^ s * q ^ 2) (hp : Odd p)
    (hNp : 2 * N + p = p ^ 3) : False := by
  obtain ⟨k, rfl⟩ := hp
  have hk : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this
    have : 0 < 2 ^ s * R := Nat.mul_pos (Nat.two_pow_pos s) hR0
    simp at hNp
    omega
  have hN2 : N = 2 * ((2 * k + 1) * (k * (k + 1))) := by
    have : 2 * N = 2 * (2 * ((2 * k + 1) * (k * (k + 1)))) := by nlinarith [hNp]
    omega
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hdiv : 2 ^ t ∣ (2 * k + 1) * (k * (k + 1)) := by
    have h1 : 2 ^ (t + 1) ∣ 2 * ((2 * k + 1) * (k * (k + 1))) := by
      rw [← hN2, hN]; exact Dvd.intro _ rfl
    rw [pow_succ, mul_comm (2 ^ t) 2] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hcop : Nat.Coprime (2 ^ t) (2 * k + 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]; exact odd_two_mul_add_one k
  have hdiv2 : 2 ^ t ∣ k * (k + 1) := hcop.dvd_of_dvd_mul_left hdiv
  have hkk : Nat.Coprime k (k + 1) := by simp
  have hle : 2 ^ t ≤ k + 1 := by
    rcases two_pow_dvd_mul_coprime hkk hdiv2 with h | h
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h
  set Q' := 2 ^ t with hQ'
  have hQ2 : 2 ^ (t + 1) = 2 * Q' := by rw [pow_succ]; ring
  rw [hQ2] at hQ hN hR
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have h1 : 2 * q ^ 2 ≤ Q' := by omega
  have hup : N < 4 * Q' ^ 2 * q ^ 2 := by
    rw [hN]
    calc 2 * Q' * R < 2 * Q' * (2 * Q' * q ^ 2) := by
          apply Nat.mul_lt_mul_of_pos_left hR (by positivity)
      _ = 4 * Q' ^ 2 * q ^ 2 := by ring
  have hlow : 2 * ((2 * Q' - 1) * ((Q' - 1) * Q')) ≤ N := by
    rw [hN2]
    apply Nat.mul_le_mul_left
    have hk1 : Q' - 1 ≤ k := by omega
    have h2k : 2 * Q' - 1 ≤ 2 * k + 1 := by omega
    exact Nat.mul_le_mul h2k (Nat.mul_le_mul hk1 (by omega))
  have hQ'2 : 2 ≤ Q' := by nlinarith
  obtain ⟨u, hu⟩ : ∃ u, Q' = u + 2 := ⟨Q' - 2, by omega⟩
  have : 4 * Q' ^ 2 * q ^ 2 ≤ 2 * ((2 * Q' - 1) * ((Q' - 1) * Q')) := by
    rw [hu]
    have e1 : 2 * (u + 2) - 1 = 2 * u + 3 := by omega
    have e2 : u + 2 - 1 = u + 1 := by omega
    rw [e1, e2]
    nlinarith [sq_nonneg (u : ℕ), hu, h1, hq2]
  omega


theorem l2two_order {s m R : ℕ} (hm : 1 ≤ m) (hR : Odd R)
    (h : 2 ^ s * R = 2 ^ m * ((2 ^ m) ^ 2 - 1)) : m = s ∧ R = (2 ^ s) ^ 2 - 1 := by
  have hodd : Odd ((2 ^ m) ^ 2 - 1) := by
    have he : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    obtain ⟨j, hj⟩ := Even.pow_of_ne_zero he (by norm_num : (2 : ℕ) ≠ 0)
    have : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos m)
    exact ⟨j - 1, by omega⟩
  have h2R : Nat.Coprime 2 R := (Nat.coprime_two_left).2 hR
  have h2R' : Nat.Coprime 2 ((2 ^ m) ^ 2 - 1) := (Nat.coprime_two_left).2 hodd
  have h1 : 2 ^ s ∣ 2 ^ m := by
    have : 2 ^ s ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := h ▸ Dvd.intro _ rfl
    exact (Nat.Coprime.pow_left s h2R').dvd_of_dvd_mul_right this
  have h2 : 2 ^ m ∣ 2 ^ s := by
    have : 2 ^ m ∣ 2 ^ s * R := h ▸ Dvd.intro _ rfl
    exact (Nat.Coprime.pow_left m h2R).dvd_of_dvd_mul_right this
  have hsm : s = m := le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1)
    ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2)
  subst hsm
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos s) h⟩

theorem not_three_dvd_suzuki {f : ℕ} (hf : Odd f) : ¬ 3 ∣ ordSuzuki (2 ^ f) := by
  obtain ⟨a, rfl⟩ := hf
  have h1 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  unfold ordSuzuki
  generalize 2 ^ (2 * a + 1) = q at h1 ⊢
  have e1 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h1]
  have e2 : (q ^ 2 + 1) % 3 = 2 := by omega
  have e3 : (q - 1) % 3 = 1 := by omega
  have : q ^ 2 * (q ^ 2 + 1) * (q - 1) % 3 = 2 := by
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 2), e1, e2, e3]
  omega

namespace ModelNum

variable {N n : ℕ}

theorem three_dvd (h : ModelNum N n) : 3 ∣ N := by
  obtain ⟨-, -, -, -, -, -, h3⟩ := h
  exact h3

theorem exp_data (h : ModelNum N n) (hn : 2 ≤ n) :
    ∃ R s : ℕ, 6 ≤ s ∧ N = 2 ^ s * R ∧ Odd R ∧ 0 < R ∧
      R < 2 ^ s * (2 ^ n) ^ 2 ∧ 4 * (2 ^ n) ^ 2 ≤ 2 ^ s ∧ 3 ∣ N := by
  obtain ⟨a, R, ha, hN, hR, hRlt, h3⟩ := h
  have ha3 : 3 ≤ a := by omega
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨R, n * a, ?_, ?_, hR, hR.pos, ?_, ?_, h3⟩
  · nlinarith
  · rw [pow_mul]; exact hN
  · calc R < (2 ^ n) ^ (a + 2) := hRlt
      _ = (2 ^ n) ^ a * (2 ^ n) ^ 2 := pow_add _ _ _
      _ = 2 ^ (n * a) * (2 ^ n) ^ 2 := by rw [pow_mul]
  · have h1 : (2 ^ n) ^ 3 ≤ (2 ^ n) ^ a := Nat.pow_le_pow_right (by omega) ha3
    calc 4 * (2 ^ n) ^ 2 ≤ 2 ^ n * (2 ^ n) ^ 2 := Nat.mul_le_mul_right _ hq4
      _ = (2 ^ n) ^ 3 := by ring
      _ ≤ (2 ^ n) ^ a := h1
      _ = 2 ^ (n * a) := (pow_mul 2 n a).symm

theorem sixtyfour_dvd (h : ModelNum N n) (hn : 2 ≤ n) : 64 ∣ N := by
  obtain ⟨R, s, hs, hN, -⟩ := h.exp_data hn
  rw [hN]
  exact Dvd.dvd.mul_right (by
    calc 64 = 2 ^ 6 := by norm_num
      _ ∣ 2 ^ s := pow_dvd_pow 2 hs) _

theorem not_l2p (h : ModelNum N n) (hn : 2 ≤ n) {p : ℕ} (hp : Odd p) (hNp : 2 * N + p = p ^ 3) :
    False := by
  obtain ⟨R, s, hs, hN, -, hR0, hR, hQ, -⟩ := h.exp_data hn
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact not_l2p_order hq4 (by omega) hQ hN hR0 hR hp hNp

theorem not_l2two (h : ModelNum N n) (hn : 2 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (hN : N = 2 ^ m * ((2 ^ m) ^ 2 - 1)) : False := by
  obtain ⟨R, s, hs, hN', hRodd, hR0, hR, hQ, -⟩ := h.exp_data hn
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨hms, hRe⟩ := l2two_order (s := s) (m := m) (by omega) hRodd (by rw [← hN', hN])
  subst hms
  have h1 : (2 ^ m) ^ 2 = 2 ^ m * 2 ^ m := sq _
  rw [hRe, h1] at hR
  have h2 : 2 ^ m * 2 ^ m - 1 < 2 ^ m * (2 ^ n) ^ 2 := hR
  have h3 : 2 ^ m * (4 * (2 ^ n) ^ 2) ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_left _ hQ
  have h3' : 4 * (2 ^ m * (2 ^ n) ^ 2) ≤ 2 ^ m * 2 ^ m := by
    calc 4 * (2 ^ m * (2 ^ n) ^ 2) = 2 ^ m * (4 * (2 ^ n) ^ 2) := by ring
      _ ≤ 2 ^ m * 2 ^ m := h3
  have h4 : 1 ≤ 2 ^ m * (2 ^ n) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

theorem not_suzuki (h : ModelNum N n) {f : ℕ} (hf : Odd f) (hN : N = ordSuzuki (2 ^ f)) :
    False := by
  exact not_three_dvd_suzuki hf (hN ▸ h.three_dvd)

end ModelNum


section Groups

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    CharP F 2 := by
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])

theorem modelNum_psl_three {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : StatedClassicalModel X .PSL 3 2 n) : ModelNum (Nat.card X) n := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F) := e
  refine modelNum_L hn ?_
  rw [Nat.card_congr e'.toEquiv, card_statedProj_statedSL (n := 3) (by norm_num), hF]
  have : Finset.Icc 2 3 = {2, 3} := by decide
  simp [this]

theorem modelNum_psp_four {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : StatedClassicalModel X .PSp 2 2 n) : ModelNum (Nat.card X) n := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F) := e
  have := charP_two_of_card hF
  refine modelNum_S hn ?_
  rw [Nat.card_congr e'.toEquiv, card_statedProj_statedSp_of_charTwo, hF]
  have : Finset.Icc 1 2 = {1, 2} := by decide
  simp [this]

theorem card_psl_two {X : Type} [Group X] {p : ℕ}
    (h : StatedClassicalModel X .PSL 2 p 1) : Odd p ∧ 2 * Nat.card X + p = p ^ 3 := by
  obtain ⟨⟨hp, -, -, h22, h23⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F) := e
  have hF' : Nat.card F = p := by rw [hF, pow_one]
  have hp2 : p ≠ 2 := fun h2 => h22 (by subst h2; rfl)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  refine ⟨hodd, ?_⟩
  have hg : Nat.gcd 2 (p - 1) = 2 := by
    apply Nat.gcd_eq_left
    rcases hodd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hN : Nat.card X = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e'.toEquiv, card_statedProj_statedSL (n := 2) (by norm_num), hF']
    simp [hg, Finset.Icc_self]
  have hev : 2 ∣ p * (p ^ 2 - 1) := by
    rcases hodd with ⟨k, hk⟩
    subst hk
    refine ⟨(2 * k + 1) * (2 * k * (k + 1)), ?_⟩
    have : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
      have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
      omega
    rw [this]
    ring
  have h2N : 2 * Nat.card X = p * (p ^ 2 - 1) := by
    rw [hN]; exact Nat.mul_div_cancel' hev
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have : p * (p ^ 2 - 1) + p = p ^ 3 := by
    obtain ⟨u, hu⟩ : ∃ u, p ^ 2 = u + 1 := ⟨p ^ 2 - 1, by omega⟩
    rw [hu]
    have : p ^ 3 = p * (u + 1) := by rw [← hu]; ring
    rw [this]
    simp [Nat.mul_add]
  omega

end Groups

theorem nonIso257 :
    NonIso257 := by
  intro K _ _ n hn hmod
  have hN : ModelNum (Nat.card (K ⧸ CFSG.pCore 2 K)) n := by
    rcases hmod with h | h
    · exact modelNum_psl_three (by omega) h
    · exact modelNum_psp_four (by omega) h
  have h64 : 64 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := hN.sixtyfour_dvd hn
  have hdvd : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
  have h64K : 64 ∣ Nat.card K := h64.trans hdvd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h3
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h3
    have e' : K ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F) := e
    have hc : Nat.card K = 5616 := by
      rw [Nat.card_congr e'.toEquiv, card_statedProj_statedSL (n := 3) (by norm_num), hF]
      have : Finset.Icc 2 3 = {2, 3} := by decide
      simp [this]
    rw [hc] at h64K
    omega
  ·
    rintro ⟨e⟩
    have hc : Nat.card K = 7920 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M11
    rw [hc] at h64K
    omega
  ·
    intro p _ h
    obtain ⟨hodd, hNp⟩ := card_psl_two h
    have hpp : p.Prime := h.1.1
    have hs : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 h).2
    have hbot : CFSG.pCore 2 K = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 K) with h0 | h0
      · exact h0
      · exfalso
        have hp2 : IsPGroup 2 K := by
          have : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
          rw [h0] at this
          exact IsPGroup.of_equiv this Subgroup.topEquiv
        obtain ⟨m, hm⟩ := hp2.exists_card_eq
        have hp3 : p ∣ p ^ 3 := dvd_pow_self p (by norm_num)
        rw [← hNp] at hp3
        have h2N : p ∣ 2 * Nat.card K := (Nat.dvd_add_left (dvd_refl p)).mp hp3
        have hdvd2 : p ∣ Nat.card K := by
          rcases (Nat.Prime.dvd_mul hpp).mp h2N with h2 | h2
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h2 ▸ hodd) (by decide)
          · exact h2
        rw [hm] at hdvd2
        have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hdvd2)
        exact absurd (this ▸ hodd) (by decide)
    have hcard : Nat.card (K ⧸ CFSG.pCore 2 K) = Nat.card K := by
      rw [hbot]
      exact Nat.card_congr (QuotientGroup.quotientBot (G := K)).toEquiv
    rw [hcard] at hN
    exact hN.not_l2p hn hodd hNp
  ·
    rintro ⟨-, -, -, hcases⟩
    rcases hcases with ⟨m, hm, h⟩ | ⟨f, hf, hf3, h⟩ | ⟨p, hp, hp5, h⟩ | ⟨⟨e⟩⟩
    ·
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
      have e' : (K ⧸ CFSG.pCore 2 K) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F) := e
      have hodd : Odd (2 ^ m - 1) := by
        have hm0 : m ≠ 0 := by omega
        obtain ⟨j, hj⟩ := Even.pow_of_ne_zero (even_two : Even 2) hm0
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        exact ⟨j - 1, by omega⟩
      have hg : Nat.gcd 2 (2 ^ m - 1) = 1 := by
        apply Nat.Coprime.gcd_eq_one
        rw [Nat.coprime_two_left]
        exact hodd
      have hc : Nat.card (K ⧸ CFSG.pCore 2 K) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
        rw [Nat.card_congr e'.toEquiv, card_statedProj_statedSL (n := 2) (by norm_num), hF]
        simp [hg, Finset.Icc_self]
      exact hN.not_l2two hn hm hc
    ·
      obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := h
      have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
      have hc : Nat.card (K ⧸ CFSG.pCore 2 K) = ordSuzuki (2 ^ f) := by
        rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF', hfa, ordSuzuki]
        exact Nat.mul_right_comm _ _ _
      exact hN.not_suzuki (f := f) hf hc
    ·
      obtain ⟨hodd, hNp⟩ := card_psl_two h
      exact hN.not_l2p hn hodd hNp
    ·
      have hc : Nat.card (K ⧸ CFSG.pCore 2 K) = 175560 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.Sporadic.J1.card_J1
      rw [hc] at h64
      omega
  ·
    rintro ⟨e⟩
    have hc : Nat.card K = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [hc] at h64K
    omega

end Fin257

end CFSG.QuasithinUnique
