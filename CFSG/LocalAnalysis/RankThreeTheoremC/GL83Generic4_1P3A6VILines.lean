module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VITools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6vi_exists_three_cycle {Q : Subgroup G} {x y y₂ n n' : G}
    (hQsyl : IsSylowOf 3 Q (centralizer ({x} : Set G))) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hL01 : zpowers x ≠ zpowers y) (hL02 : zpowers x ≠ zpowers y₂)
    (hL12 : zpowers y ≠ zpowers y₂)
    (hperm : ∀ h ∈ normalizer (Q : Set G), ∀ w : G,
      (w = x ∨ w = y ∨ w = y₂) → (zpowers (h * w * h⁻¹) = zpowers x ∨
        zpowers (h * w * h⁻¹) = zpowers y ∨ zpowers (h * w * h⁻¹) = zpowers y₂))
    (hn : n ∈ normalizer (Q : Set G)) (hnx : zpowers (n * x * n⁻¹) = zpowers y)
    (hn' : n' ∈ normalizer (Q : Set G)) (hn'x : n' * x * n'⁻¹ = x)
    (hn'y : zpowers (n' * y * n'⁻¹) = zpowers y₂) :
    ∃ r ∈ normalizer (Q : Set G), (∃ e : ℕ, r ^ (3 ^ e) = 1) ∧ r ^ 3 ∈ Q ∧
      zpowers (r * x * r⁻¹) = zpowers y ∧ zpowers (r * y * r⁻¹) = zpowers y₂ ∧
      zpowers (r * y₂ * r⁻¹) = zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn'x' : zpowers (n' * x * n'⁻¹) = zpowers x := by rw [hn'x]
  have hn'y₂ : zpowers (n' * y₂ * n'⁻¹) = zpowers y := by
    rcases hperm n' hn' y₂ (Or.inr (Or.inr rfl)) with h | h | h
    · exact absurd (a6vi_zpowers_of_conj (h.trans hn'x'.symm)) hL02.symm
    · exact h
    · exact absurd (a6vi_zpowers_of_conj (h.trans hn'y.symm)) hL12.symm
  obtain ⟨m, hm, hmx, hmy, hmy₂⟩ : ∃ m ∈ normalizer (Q : Set G),
      zpowers (m * x * m⁻¹) = zpowers y ∧ zpowers (m * y * m⁻¹) = zpowers y₂ ∧
        zpowers (m * y₂ * m⁻¹) = zpowers x := by
    have hny : zpowers (n * y * n⁻¹) = zpowers x ∨ zpowers (n * y * n⁻¹) = zpowers y₂ := by
      rcases hperm n hn y (Or.inr (Or.inl rfl)) with h | h | h
      · exact Or.inl h
      · exact absurd (a6vi_zpowers_of_conj (h.trans hnx.symm)) hL01.symm
      · exact Or.inr h
    rcases hny with hny | hny
    ·
      have hny₂ : zpowers (n * y₂ * n⁻¹) = zpowers y₂ := by
        rcases hperm n hn y₂ (Or.inr (Or.inr rfl)) with h | h | h
        · exact absurd (a6vi_zpowers_of_conj (h.trans hny.symm)) hL12.symm
        · exact absurd (a6vi_zpowers_of_conj (h.trans hnx.symm)) hL02.symm
        · exact h
      refine ⟨n * n', mul_mem hn hn', ?_, ?_, ?_⟩
      · have e : n * n' * x * (n * n')⁻¹ = n * (n' * x * n'⁻¹) * n⁻¹ := by group
        rw [e, hn'x]
        exact hnx
      · have e : n * n' * y * (n * n')⁻¹ = n * (n' * y * n'⁻¹) * n⁻¹ := by group
        rw [e, a6vi_zpowers_conj_congr hn'y n]
        exact hny₂
      · have e : n * n' * y₂ * (n * n')⁻¹ = n * (n' * y₂ * n'⁻¹) * n⁻¹ := by group
        rw [e, a6vi_zpowers_conj_congr hn'y₂ n]
        exact hny
    ·
      have hny₂ : zpowers (n * y₂ * n⁻¹) = zpowers x := by
        rcases hperm n hn y₂ (Or.inr (Or.inr rfl)) with h | h | h
        · exact h
        · exact absurd (a6vi_zpowers_of_conj (h.trans hnx.symm)) hL02.symm
        · exact absurd (a6vi_zpowers_of_conj (h.trans hny.symm)) hL12.symm
      exact ⟨n, hn, hnx, hny, hny₂⟩
  have hfix : ∀ w : G, (w = x ∨ w = y ∨ w = y₂) →
      zpowers (m ^ 3 * w * (m ^ 3)⁻¹) = zpowers w := by
    have e : ∀ w : G, m ^ 3 * w * (m ^ 3)⁻¹ = m * (m * (m * w * m⁻¹) * m⁻¹) * m⁻¹ := by
      intro w; rw [pow_three]; group
    rintro w (rfl | rfl | rfl)
    · rw [e, a6vi_zpowers_conj_congr (a6vi_zpowers_conj_congr hmx m) m,
        a6vi_zpowers_conj_congr hmy m, hmy₂]
    · rw [e, a6vi_zpowers_conj_congr (a6vi_zpowers_conj_congr hmy m) m,
        a6vi_zpowers_conj_congr hmy₂ m, hmx]
    · rw [e, a6vi_zpowers_conj_congr (a6vi_zpowers_conj_congr hmy₂ m) m,
        a6vi_zpowers_conj_congr hmx m, hmy]
  have hfixq : ∀ q : ℕ, ∀ w : G, (w = x ∨ w = y ∨ w = y₂) →
      zpowers ((m ^ 3) ^ q * w * ((m ^ 3) ^ q)⁻¹) = zpowers w := by
    intro q
    induction q with
    | zero => intro w _; simp
    | succ q ih =>
      intro w hw
      have e : (m ^ 3) ^ (q + 1) * w * ((m ^ 3) ^ (q + 1))⁻¹ =
          m ^ 3 * ((m ^ 3) ^ q * w * ((m ^ 3) ^ q)⁻¹) * (m ^ 3)⁻¹ := by group
      rw [e, a6vi_zpowers_conj_congr (ih w hw) (m ^ 3), hfix w hw]
  have hmo : orderOf m ≠ 0 := (orderOf_pos m).ne'
  obtain ⟨e, b, hb3, hbo⟩ := Nat.exists_eq_pow_mul_and_not_dvd hmo 3 (by norm_num)
  obtain ⟨b', hb'b, hb'3⟩ : ∃ b' : ℕ, b ∣ b' ∧ b' % 3 = 1 := by
    have hb : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hb with hb | hb
    · exact ⟨b, dvd_rfl, hb⟩
    · exact ⟨2 * b, dvd_mul_left b 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, b' = 3 * q + 1 := ⟨b' / 3, by omega⟩
  set r := m ^ b' with hr
  have hrm : r = (m ^ 3) ^ q * m := by rw [hr, hq, pow_succ, pow_mul]
  have hract : ∀ w : G, zpowers (r * w * r⁻¹) =
      zpowers ((m ^ 3) ^ q * (m * w * m⁻¹) * ((m ^ 3) ^ q)⁻¹) := by
    intro w
    rw [hrm]
    congr 1
    group
  have hrx : zpowers (r * x * r⁻¹) = zpowers y := by
    rw [hract, a6vi_zpowers_conj_congr hmx, hfixq q y (Or.inr (Or.inl rfl))]
  have hry : zpowers (r * y * r⁻¹) = zpowers y₂ := by
    rw [hract, a6vi_zpowers_conj_congr hmy, hfixq q y₂ (Or.inr (Or.inr rfl))]
  have hry₂ : zpowers (r * y₂ * r⁻¹) = zpowers x := by
    rw [hract, a6vi_zpowers_conj_congr hmy₂, hfixq q x (Or.inl rfl)]
  have hre : r ^ (3 ^ e) = 1 := by
    rw [hr, ← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hbo, mul_comm b' (3 ^ e)]
    exact Nat.mul_dvd_mul_left _ hb'b
  refine ⟨r, pow_mem hm b', ⟨e, hre⟩, ?_, hrx, hry, hry₂⟩
  have hrN : r ∈ normalizer (Q : Set G) := pow_mem hm b'
  have hr3x : zpowers (r ^ 3 * x * (r ^ 3)⁻¹) = zpowers x := by
    have e3 : r ^ 3 * x * (r ^ 3)⁻¹ = r * (r * (r * x * r⁻¹) * r⁻¹) * r⁻¹ := by
      rw [pow_three]; group
    rw [e3, a6vi_zpowers_conj_congr (a6vi_zpowers_conj_congr hrx r) r,
      a6vi_zpowers_conj_congr hry r, hry₂]
  have hr3e : (r ^ 3) ^ (3 ^ e) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hre, one_pow]
  have hr3c : r ^ 3 * x * (r ^ 3)⁻¹ = x :=
    p34_conj_eq_of_pow hx1 hx3 hr3e (by rw [← hr3x]; exact mem_zpowers _)
  have hr3C : r ^ 3 ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc r ^ 3 * x = r ^ 3 * x * (r ^ 3)⁻¹ * r ^ 3 := by group
      _ = x * r ^ 3 := by rw [hr3c]
  have hVp : IsPGroup 3 ↥(Q ⊔ zpowers (r ^ 3)) :=
    hQsyl.isPGroup.to_sup_of_normal_left' (a6vi_isPGroup_zpowers hr3e)
      (zpowers_le.mpr (pow_mem hrN 3))
  have hV : Q ⊔ zpowers (r ^ 3) = Q :=
    hQsyl.eq_of_le le_sup_left (sup_le hQsyl.le (zpowers_le.mpr hr3C)) hVp
  rw [← hV]
  exact mem_sup_right (mem_zpowers _)

end CFSG.LocalAnalysis.RankThreeTheoremC
