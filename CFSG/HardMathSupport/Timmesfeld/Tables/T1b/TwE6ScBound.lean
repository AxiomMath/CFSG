module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6ScBound

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6 CFSG.Open
  CFSG.SectionRank


private theorem three_dvd_pow_two_mul_sub_one {p f : ℕ} (hp : p.Prime) (h3 : 3 ∣ p ^ f + 1) :
    3 ∣ p ^ (2 * f) - 1 := by
  have hmod : ((p : ZMod 3) ^ f) = -1 := by
    have hz : ((p : ZMod 3) ^ f + 1) = 0 := by
      have h := (ZMod.natCast_eq_zero_iff (p ^ f + 1) 3).2 h3
      push_cast at h
      exact h
    rw [eq_neg_iff_add_eq_zero]
    exact hz
  have hsq : ((p : ZMod 3) ^ (2 * f)) = 1 := by
    calc ((p : ZMod 3)) ^ (2 * f) = ((p : ZMod 3) ^ f) ^ 2 := by
          rw [show 2 * f = f * 2 by ring, pow_mul]
      _ = (-1) ^ 2 := by rw [hmod]
      _ = 1 := by decide
  have hcast : ((p ^ (2 * f) : ℕ) : ZMod 3) = 1 := by
    push_cast
    exact hsq
  have h1 : 1 ≤ p ^ (2 * f) := Nat.succ_le_of_lt (pow_pos hp.pos _)
  rw [← ZMod.natCast_eq_zero_iff (p ^ (2 * f) - 1) 3,
    Nat.cast_sub h1, hcast]
  norm_num

theorem pRank_three_twistedE6Sc_le_six {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h3 : 3 ∣ p ^ f + 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (twistedE6Group p f)) ≤ 6 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField p (2 * f) with hK
  have hKcard : Nat.card K = p ^ (2 * f) := by
    rw [hK, GaloisField.card p (2 * f) (by omega)]
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hKcard]
    exact three_dvd_pow_two_mul_sub_one Fact.out h3
  have hB1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(e6Data_valid.minGroup K)) ≤ 6 :=
    pRank_three_e6Sc_le_six (K := K) h3K
  have hinj : Function.Injective (Subgroup.subtype (fixedGroup K (frobQ p f))) :=
    Subgroup.subtype_injective _
  exact (pRank_top_le_of_injective (p := 3) (by norm_num)
    (Subgroup.subtype (fixedGroup K (frobQ p f))) hinj).trans hB1

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
