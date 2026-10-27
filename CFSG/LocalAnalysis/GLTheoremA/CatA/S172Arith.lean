module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

inductive Num126 (vL vK : ℕ) : Prop
  | i (a : ℕ) (ha : 2 ≤ a) (hL : vL = a * (2 * a + 1)) (hK : vK = a * (a - 1))
  | ii (n : ℕ) (hn : 5 ≤ n) (hL : vL = n * (n - 1)) (hK : 2 * vK = (n - 1) * (n - 2))
  | iii (n k : ℕ) (hn : 4 ≤ n) (hk : 1 ≤ k) (hL : vL = k * (n * (n - 1)))
      (hK : 2 * vK = k * ((n - 1) * (n - 2)))

inductive Num172 (vL vK : ℕ) : Prop
  | i (a : ℕ) (ha : 3 ≤ a) (hL : vL = a * (2 * a + 1)) (hK : vK = (a - 1) * (2 * a - 1))
  | ii (n : ℕ) (hn : 5 ≤ n) (hL : vL = n * (n - 1)) (hK : vK = (n - 1) * (n - 2))
  | iii (n k : ℕ) (hn : 4 ≤ n) (hk : 1 ≤ k) (hn4 : n = 4 → 2 ≤ k) (hL : vL = k * (n * (n - 1)))
      (hK : vK = k * ((n - 1) * (n - 2)))

theorem num126_lt {vL vK : ℕ} (h : Num126 vL vK) : 2 * vK < vL := by
  cases h with
  | i a ha hL hK =>
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    subst hL hK
    rw [show b + 2 - 1 = b + 1 by omega]
    nlinarith
  | ii n hn hL hK =>
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 5 := ⟨n - 5, by omega⟩
    subst hL
    rw [show b + 5 - 1 = b + 4 by omega, show b + 5 - 2 = b + 3 by omega] at *
    nlinarith
  | iii n k hn hk hL hK =>
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 4 := ⟨n - 4, by omega⟩
    subst hL
    rw [show b + 4 - 1 = b + 3 by omega, show b + 4 - 2 = b + 2 by omega] at *
    nlinarith [Nat.mul_le_mul hk (le_refl ((b + 3) * (b + 2)))]

theorem num172_le_or {vL vK : ℕ} (h : Num172 vL vK) : vL ≤ 2 * vK ∨ (vL = 21 ∧ vK = 10) := by
  cases h with
  | i a ha hL hK =>
    by_cases h3 : a = 3
    · subst h3; right; subst hL hK; norm_num
    · left
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 4 := ⟨a - 4, by omega⟩
      subst hL hK
      rw [show b + 4 - 1 = b + 3 by omega, show 2 * (b + 4) - 1 = 2 * b + 7 by omega]
      nlinarith
  | ii n hn hL hK =>
    left
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 5 := ⟨n - 5, by omega⟩
    subst hL hK
    rw [show b + 5 - 1 = b + 4 by omega, show b + 5 - 2 = b + 3 by omega]
    nlinarith
  | iii n k hn hk hn4 hL hK =>
    left
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 4 := ⟨n - 4, by omega⟩
    subst hL hK
    rw [show b + 4 - 1 = b + 3 by omega, show b + 4 - 2 = b + 2 by omega]
    nlinarith [Nat.zero_le (k * ((b + 3) * b))]

theorem num126_ne_21_10 {vL vK : ℕ} (h : Num126 vL vK) (h1 : vL = 21) (h2 : vK = 10) : False := by
  cases h with
  | i a ha hL hK =>
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
    rw [show c + 2 - 1 = c + 1 by omega] at hK
    subst h2
    rcases Nat.lt_or_ge c 2 with hc | hc
    · interval_cases c <;> omega
    · nlinarith
  | ii n hn hL hK =>
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 5 := ⟨n - 5, by omega⟩
    rw [show b + 5 - 1 = b + 4 by omega] at hL
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · omega
    · nlinarith
  | iii n k hn hk hL hK =>
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 4 := ⟨n - 4, by omega⟩
    rw [show b + 4 - 1 = b + 3 by omega] at hL
    rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b <;> omega
    · nlinarith [Nat.mul_le_mul hk (le_refl ((b + 4) * (b + 3)))]

theorem not_num172_num126 {vL vK : ℕ} (h : Num172 vL vK) (h' : Num126 vL vK) : False := by
  have hlt := num126_lt h'
  rcases num172_le_or h with hle | ⟨h1, h2⟩
  · omega
  · exact num126_ne_21_10 h' h1 h2

theorem not_num126_u42 {vL vK : ℕ} (h : Num126 vL vK) (hK : vK = 6)
    (hL : vL = 10 ∨ vL = 12 ∨ vL = 15) : False := by
  cases h with
  | i a ha hL' hK' =>
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
    rw [show c + 2 - 1 = c + 1 by omega] at hK'
    subst hK
    rcases Nat.lt_or_ge c 2 with hc | hc
    · interval_cases c <;> omega
    · nlinarith
  | ii n hn hL' hK' =>
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 5 := ⟨n - 5, by omega⟩
    rw [show b + 5 - 1 = b + 4 by omega] at hL'
    rw [show b + 5 - 1 = b + 4 by omega, show b + 5 - 2 = b + 3 by omega] at hK'
    subst hK
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · omega
    · nlinarith
  | iii n k hn hk hL' hK' =>
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 4 := ⟨n - 4, by omega⟩
    rw [show b + 4 - 1 = b + 3 by omega, show b + 4 - 2 = b + 2 by omega] at hK'
    subst hK
    rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b <;> omega
    · nlinarith [Nat.mul_le_mul hk (le_refl ((b + 3) * (b + 2)))]

theorem seven_le_of_num172 {vL vK : ℕ} (h : Num172 vL vK) : 7 ≤ vK := by
  cases h with
  | i a ha hL hK =>
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
    subst hK
    rw [show b + 3 - 1 = b + 2 by omega, show 2 * (b + 3) - 1 = 2 * b + 5 by omega]
    nlinarith
  | ii n hn hL hK =>
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 5 := ⟨n - 5, by omega⟩
    subst hK
    rw [show b + 5 - 1 = b + 4 by omega, show b + 5 - 2 = b + 3 by omega]
    nlinarith
  | iii n k hn hk hn4 hL hK =>
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 4 := ⟨n - 4, by omega⟩
    subst hK
    rw [show b + 4 - 1 = b + 3 by omega, show b + 4 - 2 = b + 2 by omega]
    by_cases hb0 : b = 0
    · subst hb0
      have := hn4 rfl
      nlinarith
    · have h12 : 12 ≤ (b + 3) * (b + 2) := by
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        nlinarith
      nlinarith [Nat.mul_le_mul hk h12]

section Extract

variable {G : Type} [Group G] [Finite G]

theorem num126_of_type126 (hb : CatDistinct.OrderBridge) {p : ℕ} {L K J : Subgroup G}
    (h : Type126 p L K J) :
    Num126 (padicValNat 2 (Nat.card (PSimple p L))) (padicValNat 2 (Nat.card (PSimple p K))) := by
  rcases h with ⟨hp3, n, hn, hL, hK, hJ⟩ | ⟨hp3, n, hn, hL, hK, hJ⟩ | ⟨n, k, hn, hk, hpk, hL, hK, hJ⟩
  · subst hp3
    obtain ⟨a, rfl⟩ := hn
    obtain ⟨-, -, hv1⟩ := v2_isLnA hb (S := PSimple 3 L) (f := 1) le_rfl (by rw [pow_one]; exact hL)
    obtain ⟨h2a, -, hv2⟩ := v2_isLnA hb (S := PSimple 3 K) (f := 2) (by norm_num)
      (by rw [show ((2 : ℕ) ^ 2) = 4 by norm_num]; exact hK)
    have e1 : (2 * a + 1 - 1) / 2 = a := by omega
    rw [e1] at h2a hv2
    refine Num126.i a h2a ?_ ?_
    · have : 2 * padicValNat 2 (Nat.card (PSimple 3 L)) = 2 * (a * (2 * a + 1)) := by
        rw [hv1, show 2 * a + 1 - 1 = 2 * a by omega]; ring
      omega
    · have : 2 * padicValNat 2 (Nat.card (PSimple 3 K)) = 2 * (a * (a - 1)) := hv2
      omega
  · subst hp3
    obtain ⟨-, hv1⟩ := v2_isOmPA hb (S := PSimple 3 L) (f := 1) le_rfl (by rw [pow_one]; exact hL)
    obtain ⟨-, h3, hv2⟩ := v2_isUnA hb (S := PSimple 3 K) (f := 1) le_rfl (by rw [pow_one]; exact hK)
    have h5 : 5 ≤ n := by
      by_contra hlt
      have := h3 (by omega)
      omega
    refine Num126.ii n h5 ?_ ?_
    · rw [hv1]; ring
    · rw [hv2, show n - 1 - 1 = n - 2 by omega]; ring
  · obtain ⟨hn3, hv1⟩ := v2_isOmMA hb (S := PSimple p L) hk hL
    obtain ⟨-, -, hv2⟩ := v2_isUnA hb (S := PSimple p K) hk hK
    obtain ⟨c, hc⟩ := hn
    refine Num126.iii n k (by omega) hk hv1 ?_
    rw [hv2, show n - 1 - 1 = n - 2 by omega]

theorem num172_of_type172 (hb : CatDistinct.OrderBridge) {p : ℕ} {L K J K₁ KE : Subgroup G}
    (h : Type172 p L K J K₁ KE) :
    Num172 (padicValNat 2 (Nat.card (PSimple p L))) (padicValNat 2 (Nat.card (PSimple p K₁))) := by
  rcases h with ⟨hp3, n, hn, hL, hK, hJ, hK₁, hKE⟩ | ⟨hp3, n, hn, hL, hK, hJ, hK₁, hKE⟩ |
    ⟨n, k, hn, hk, hpk, hL, hK, hJ, hK₁, hKE⟩
  · subst hp3
    obtain ⟨a, rfl⟩ := hn
    obtain ⟨-, -, hv1⟩ := v2_isLnA hb (S := PSimple 3 L) (f := 1) le_rfl (by rw [pow_one]; exact hL)
    obtain ⟨-, -, hv2⟩ := v2_isLnA hb (S := PSimple 3 K₁) (f := 1) le_rfl (by rw [pow_one]; exact hK₁)
    obtain ⟨h2a, -, -⟩ := v2_isLnA hb (S := PSimple 3 KE) (f := 2) (by norm_num)
      (by rw [show ((2 : ℕ) ^ 2) = 4 by norm_num]; exact hKE)
    have ha3 : 3 ≤ a := by omega
    refine Num172.i a ha3 ?_ ?_
    · have : 2 * padicValNat 2 (Nat.card (PSimple 3 L)) = 2 * (a * (2 * a + 1)) := by
        rw [hv1, show 2 * a + 1 - 1 = 2 * a by omega]; ring
      omega
    · have e1 : 2 * a + 1 - 2 = 2 * a - 1 := by omega
      have e2 : 2 * a - 1 - 1 = 2 * (a - 1) := by omega
      have : 2 * padicValNat 2 (Nat.card (PSimple 3 K₁)) = 2 * ((a - 1) * (2 * a - 1)) := by
        rw [hv2, e1, e2]; ring
      omega
  · subst hp3
    obtain ⟨-, hv1⟩ := v2_isOmPA hb (S := PSimple 3 L) (f := 1) le_rfl (by rw [pow_one]; exact hL)
    obtain ⟨-, hv2⟩ := v2_isOmMA hb (S := PSimple 3 K₁) (f := 1) le_rfl (by rw [pow_one]; exact hK₁)
    obtain ⟨-, h3, -⟩ := v2_isUnA hb (S := PSimple 3 K) (f := 1) le_rfl (by rw [pow_one]; exact hK)
    have h5 : 5 ≤ n := by
      by_contra hlt
      have := h3 (by omega)
      omega
    refine Num172.ii n h5 ?_ ?_
    · rw [hv1]; ring
    · rw [hv2, show n - 1 - 1 = n - 2 by omega]; ring
  · obtain ⟨hn3, hv1⟩ := v2_isOmMA hb (S := PSimple p L) hk hL
    obtain ⟨-, hK3, -⟩ := v2_isUnA hb (S := PSimple p K) hk hK
    obtain ⟨-, hv2⟩ := v2_isOmPA hb (S := PSimple p K₁) hk hK₁
    obtain ⟨c, hc⟩ := hn
    refine Num172.iii n k (by omega) hk (fun h4 => hK3 (by omega)) hv1 ?_
    rw [hv2, show n - 1 - 1 = n - 2 by omega]

end Extract

section Final

variable {G : Type} [Group G] [Finite G]

theorem not_type126_of_type172 (hb : CatDistinct.OrderBridge) {p : ℕ} {L K J K₁ KE : Subgroup G}
    (h : Type172 p L K J K₁ KE) : ∀ J' : Subgroup G, ¬ Type126 p L K₁ J' :=
  fun _ h' => not_num172_num126 (num172_of_type172 hb h) (num126_of_type126 hb h')

theorem not_small_of_type172 (hb : CatDistinct.OrderBridge) {p : ℕ} {L K J K₁ KE : Subgroup G}
    (h : Type172 p L K J K₁ KE) : ¬ GLASmall K₁ := by
  have h7 := seven_le_of_num172 (num172_of_type172 hb h)
  let f : ↥K₁ →* PSimple p K₁ :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p K₁))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥K₁))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hdvd : Nat.card (PSimple p K₁) ∣ Nat.card ↥K₁ := Subgroup.card_dvd_of_surjective hf
  have hpos : Nat.card ↥K₁ ≠ 0 := Nat.card_pos.ne'
  have hv : padicValNat 2 (Nat.card (PSimple p K₁)) ≤ padicValNat 2 (Nat.card ↥K₁) := by
    refine (padicValNat_dvd_iff_le hpos).1 ?_
    exact (pow_padicValNat_dvd).trans hdvd
  rintro (hU | hA)
  · have hc : Nat.card ↥K₁ = 2 ^ 6 * 405 := by
      rw [CFSG.StandardType.IOneOrthEnd.card_of_isU42 hU]; norm_num
    rw [v2_of_odd_mul (by decide : Odd 405) hc] at hv
    omega
  · obtain ⟨e⟩ := hA
    have hc : Nat.card ↥K₁ = 2 ^ 3 * 45 := by
      rw [card_of_equiv_alt (n := 6) (by norm_num) e]; norm_num [Nat.factorial]
    rw [v2_of_odd_mul (by decide : Odd 45) hc] at hv
    omega

theorem not_concl121_first (hb : CatDistinct.OrderBridge) {p : ℕ} {L K J : Subgroup G}
    (h : Type126 p L K J) (hK : catalogIs (PSimple p K) S9.isU4two)
    (hL : catalogIs (PSimple p L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i)) : False := by
  have hK6 : padicValNat 2 (Nat.card (PSimple p K)) = 6 :=
    v2_of_odd_mul (m := 405) (by decide) (by rw [CatDistinct.card_isU4two hb hK]; norm_num)
  have hL' : padicValNat 2 (Nat.card (PSimple p L)) = 10 ∨ padicValNat 2 (Nat.card (PSimple p L)) = 12 ∨
      padicValNat 2 (Nat.card (PSimple p L)) = 15 := by
    obtain ⟨i, hi, e⟩ := hL
    rcases hi with hi | hi | hi
    · right; left
      exact v2_of_odd_mul (m := 42525) (by decide) (by rw [CatDistinct.card_isD4two hb ⟨i, hi, e⟩]; norm_num)
    · left
      exact v2_of_odd_mul (m := 13365) (by decide) (by rw [CatDistinct.card_isU5two hb ⟨i, hi, e⟩]; norm_num)
    · right; right
      exact v2_of_odd_mul (m := 280665) (by decide) (by rw [CatDistinct.card_isU6two hb ⟨i, hi, e⟩]; norm_num)
  exact not_num126_u42 (num126_of_type126 hb h) hK6 hL'

end Final

end CFSG.LocalAnalysis.GLTheoremA.S172

end
