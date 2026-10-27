module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.GH74.QTGen4.Leaves.L14742

theorem card_mulAut_dvd_168 {W : Type*} [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hpow : ∀ a : W, a ^ 2 = 1) (hle : Nat.card W ≤ 8) : Nat.card (MulAut W) ∣ 168 := by
  have hp : IsPGroup 2 W := fun g => ⟨1, by simpa using hpow g⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hk
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases k <;> decide

end CFSG.GH74.QTGen4.Leaves.L14742

end
