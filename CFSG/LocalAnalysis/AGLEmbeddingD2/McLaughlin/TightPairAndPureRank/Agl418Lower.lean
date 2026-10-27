module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven

theorem psl_three_le_pRank_of_dvd {K : Type} [Field K] [Finite K] {n : ℕ}
    (h3 : 3 ∣ Nat.card K - 1) (hn : 4 ≤ n) :
    3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [Nat.card_units]; exact h3)
  exact three_le_pRank_torus (by norm_num) hζ (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩)
    (i₂ := ⟨2, by omega⟩) (i₃ := ⟨3, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) fun j => torusDiag_mem_SL (prod_torusVec ζ j _)

theorem psu_three_le_pRank_of_dvd {K : Type} [Field K] [Finite K] {n q : ℕ} (hq : q ≠ 0)
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) (hn : 4 ≤ n) :
    3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n q K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = (q + 1) * (q - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [hcard]; exact h3.mul_right _)
  have hζq : ζ ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact h3)
  exact three_le_pRank_torus (by norm_num) hζ (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩)
    (i₂ := ⟨2, by omega⟩) (i₃ := ⟨3, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) fun j => torusDiag_mem_SU hq (prod_torusVec ζ j _)
      (by rw [torusVec_pow, hζq, torusVec_one])

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
