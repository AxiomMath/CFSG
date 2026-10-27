module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXT

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer P211

theorem not_sixteen_dvd_ordRee (k : ℕ) : ¬ 16 ∣ Open.ordRee (3 ^ (2 * k + 1)) := by
  rw [← ZMod.natCast_eq_zero_iff]
  have h9 : (9 : ZMod 16) ^ k = 1 ∨ (9 : ZMod 16) ^ k = 9 := by
    induction k with
    | zero => exact Or.inl (pow_zero _)
    | succ k ih =>
      rcases ih with h | h
      · exact Or.inr (by rw [pow_succ, h, one_mul])
      · exact Or.inl (by rw [pow_succ, h]; decide)
  have hq1 : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hq : ((3 : ℕ) : ZMod 16) ^ (2 * k + 1) = 3 * 9 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [Open.ordRee, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_add, Nat.cast_pow,
    Nat.cast_pow, Nat.cast_one, hq]
  rcases h9 with h | h <;> rw [h] <;> decide

theorem p211For_ree :
    P211For fun G _ => ∃ f : ℕ, Blueprint.LieModel G .twistedG2 0 3 f := by
  intro X _ _ hsimp hC ⟨f₀, hLie⟩ p f hp hp2 hf a J D _ _ _ _ hJt _ hDJ hDsyl hbound b K hb
    hb1 hKC hK hKt
  exfalso
  have hR : Blueprint.ReeTitsModel (generalizedFitting X) .twistedG2 3 f₀ := by
    rcases hLie with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
  obtain ⟨-, hsolv, -⟩ := LieType.Ree.small_Ree_model_Schreier _ 3 f₀ hR
  obtain ⟨n, hn⟩ := exists_derivedSeries_le_of_isSolvable (OuterAutomorphisms.inner _) hsolv
  have hKF : K ≤ generalizedFitting X :=
    le_fstar_of_perfect hC (MulEquiv.refl _) hn (commutator_eq_of_isPComp hKC hK)
  obtain ⟨k, -, hcard⟩ := GH74.card_of_lieModel_twistedG2 hLie
  obtain ⟨hm3, hKv, -⟩ := p211_two_adic hp hp2 hf hJt hDJ hDsyl hbound hKt
  have h16 : 16 ∣ Open.ordRee (3 ^ (2 * k + 1)) := by
    rw [← hcard]
    refine dvd_trans ?_ ((pow_dvd_card_of_v2 hKv).trans (Subgroup.card_dvd_of_le hKF))
    exact pow_dvd_pow 2 (by omega : 4 ≤ 2 * padicValNat 2 ((p ^ f) ^ 2 - 1))
  exact not_sixteen_dvd_ordRee k h16

end P211X

end CFSG.ComponentClassification.GSThmB
