module

public import CFSG.CGT.PushingUpLit.BHS.GlaubNatural
public import CFSG.CGT.PushingUpLit.BHS.GlaubNaturalOne
public import CFSG.CGT.PushingUpLit.BHS.GlaubRankOne

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Timmesfeld CFSG.CGT.PushingUpLit.BHS.Glauberman

variable {V : Type} [CommGroup V]

theorem glauberman_natural
    [Finite V] {G M S A : Subgroup (MulAut V)} (h : GlHyp G M S A) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card A = 2 ^ n ∧ Nat.card V = 4 ^ n ∧ IsSLNatSection G ⊤ ⊥ n ∧
      commV A = fixV A ∧ Nat.card (fixV A) = Nat.card A ∧
      ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A := by
  obtain ⟨k, hk⟩ := h.exists_glPair
  obtain ⟨hcomm, -, -, hfixA, -, hVcard⟩ := hk.lemma_three
  obtain ⟨n, hn⟩ := (h.syl.2.1.to_le h.le).exists_card_eq
  have hA1 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 h.ne
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hn
      omega
    · exact h0
  have hV4 : Nat.card V = 4 ^ n := by
    rw [hVcard, hn, ← pow_mul, mul_comm, pow_mul]
    norm_num
  refine ⟨n, hn1, hn, hV4, ?_, hcomm, hfixA, fun a ha ha1 => hk.fixV_zpowers_eq ha ha1⟩
  by_cases hn2 : n = 1
  · subst hn2
    have hq2 : Nat.card A = 2 := by simpa using hn
    exact isSLNatSection_one h.hV (by simpa using hV4) (hk.card_G_eq_six hq2)
  · have hq4 : 4 ≤ Nat.card A := by
      rw [hn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨n', hn'2, hn', φ, hφA, -⟩ := hk.exists_mulEquiv_SL2 hq4
    have hnn : n' = n := Nat.pow_right_injective (le_refl 2) (by rw [← hn', hn] : 2 ^ n' = 2 ^ n)
    subst hnn
    have hup : (A.subgroupOf G).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n') := hφA
    refine isSLNatSection_of_quadratic hn1 φ hup h.quad h.fix ?_ hV4
    exact hk.fixV_ne_bot

end CFSG.CGT.PushingUpLit.BHS
