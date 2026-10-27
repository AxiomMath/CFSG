module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.SolvableKit

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

theorem exists_normal_card_seven {Q : Type*} [Group Q] [Finite Q] {m : ℕ}
    (hQ : Nat.card Q = 7 * m) (hm : m ∣ 12) :
    ∃ P : Subgroup Q, P.Normal ∧ Nat.card P = 7 := by
  classical
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd : 7 ∣ Nat.card Q := ⟨m, hQ⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q) 7 hdvd
  set P : Subgroup Q := Subgroup.zpowers g with hP
  have hPcard : Nat.card P = 7 := by rw [hP, Nat.card_zpowers, hg]
  have hP7 : IsPGroup 7 P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  have hidx : P.index = m := by
    have := P.card_mul_index
    rw [hPcard, hQ] at this
    omega
  have hm12 : m ≤ 12 := Nat.le_of_dvd (by norm_num) hm
  have hnd : ¬ 7 ∣ P.index := by
    rw [hidx]
    intro h
    have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm (by norm_num)
    interval_cases m <;> omega
  let S : Sylow 7 Q := hP7.toSylow hnd
  have hSP : (S : Subgroup Q) = P := IsPGroup.toSylow_coe hP7 hnd
  have hmod := card_sylow_modEq_one 7 Q
  have hdv : Nat.card (Sylow 7 Q) ∣ m := by
    have := S.card_dvd_index
    rwa [hSP, hidx] at this
  have hone : Nat.card (Sylow 7 Q) = 1 := by
    have hle : Nat.card (Sylow 7 Q) ≤ 12 :=
      (Nat.le_of_dvd (by omega) hdv).trans hm12
    have hmod' : Nat.card (Sylow 7 Q) % 7 = 1 := hmod
    have hdv' : Nat.card (Sylow 7 Q) ∣ 12 := hdv.trans hm
    interval_cases h : Nat.card (Sylow 7 Q) <;> omega
  have hsub : Subsingleton (Sylow 7 Q) := by
    have : Nonempty (Sylow 7 Q) := ⟨S⟩
    exact (Nat.card_eq_one_iff_unique.mp hone).1
  have hn : (S : Subgroup Q).Normal := Sylow.normal_of_subsingleton S
  exact ⟨P, hSP ▸ hn, hPcard⟩

theorem eq_one_of_simple_card_seven_mul {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {m : ℕ} (hQ : Nat.card Q = 7 * m) (hm : m ∣ 12) : m = 1 := by
  obtain ⟨P, hPn, hPc⟩ := exists_normal_card_seven hQ hm
  have := hPn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hb | ht
  · rw [hb, Subgroup.card_bot] at hPc
    omega
  · rw [ht, Subgroup.card_top, hQ] at hPc
    omega

theorem card_eq_168_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) (hd : Nat.card Q ∣ 168) (h3 : 3 ∣ Nat.card Q) :
    Nat.card Q = 168 := by
  have hle : Nat.card Q ≤ 168 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hsolv : Group.IsSolvable Q → False := by
    intro hs
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := Q)).mpr hs a b)
  have hcases : Nat.card Q = 3 ∨ Nat.card Q = 6 ∨ Nat.card Q = 12 ∨ Nat.card Q = 24 ∨
      Nat.card Q = 21 ∨ Nat.card Q = 42 ∨ Nat.card Q = 84 ∨ Nat.card Q = 168 := by
    obtain ⟨k, hk⟩ := h3
    have hk' : k ≤ 56 := by omega
    interval_cases k <;> simp_all
  have hs : ∀ a b : ℕ, Nat.card Q ∣ 2 ^ a * 3 ^ b → False := fun a b h =>
    hsolv (isSolvable_of_card_dvd_two_three h)
  rcases hcases with h | h | h | h | h | h | h | h
  · exact (hs 3 1 (by rw [h]; norm_num)).elim
  · exact (hs 3 1 (by rw [h]; norm_num)).elim
  · exact (hs 3 1 (by rw [h]; norm_num)).elim
  · exact (hs 3 1 (by rw [h]; norm_num)).elim
  · have := eq_one_of_simple_card_seven_mul (m := 3) (by omega) (by norm_num)
    omega
  · have := eq_one_of_simple_card_seven_mul (m := 6) (by omega) (by norm_num)
    omega
  · have := eq_one_of_simple_card_seven_mul (m := 12) (by omega) (by norm_num)
    omega
  · exact h

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
