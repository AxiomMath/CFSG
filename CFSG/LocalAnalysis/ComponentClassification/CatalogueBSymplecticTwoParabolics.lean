module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherIntrinsicPoints

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Module Submodule CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

variable {K : Type} [Field K]

theorem ne_bot_of_finrank_pos {r : ℕ} {W : Submodule K (Fin r ⊕ Fin r → K)}
    (h : 0 < finrank K W) : W ≠ ⊥ := fun h0 => by
  rw [h0, finrank_bot] at h
  exact lt_irrefl 0 h

theorem one_le_finrank_of_ne_bot {r : ℕ} {W : Submodule K (Fin r ⊕ Fin r → K)} (hW0 : W ≠ ⊥) :
    1 ≤ finrank K W :=
  Nat.one_le_iff_ne_zero.mpr fun h => hW0 (Submodule.finrank_eq_zero.mp h)

theorem isTotallyIsotropic_of_finrank_eq_one {r : ℕ} {L : Submodule K (Fin r ⊕ Fin r → K)}
    (hL : finrank K L = 1) : IsTotallyIsotropic (pairedSympForm K r) L :=
  isTotallyIsotropic_line ⟨L, hL⟩

theorem finrank_le_two {W : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K 2) W) : finrank K W ≤ 2 :=
  finrank_le_of_isTotallyIsotropic SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate finrank_standard hW

theorem finrank_eq_one_or_two {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K 2) W) : finrank K W = 1 ∨ finrank K W = 2 := by
  have h1 := one_le_finrank_of_ne_bot hW0
  have h2 := finrank_le_two hW
  omega

theorem projStabilizer_inj {r : ℕ} {W W' : Submodule K (Fin r ⊕ Fin r → K)} (hW0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) (hW0' : W' ≠ ⊥)
    (hW' : IsTotallyIsotropic (pairedSympForm K r) W')
    (h : projStabilizer r K W = projStabilizer r K W') : W = W' := by
  have hS : stabilizer r K W = stabilizer r K W' := by
    rw [← comap_projStabilizer, h, comap_projStabilizer]
  exact (eq_of_stabilizer_le hW0 hW hW0' hW' hS.le).symm

theorem index_projStabilizer_two [Finite K] {q : ℕ} (hq : Nat.card K = q)
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K 2) W) :
    (projStabilizer 2 K W).index = (q + 1) * (q ^ 2 + 1) := by
  have hq2 : 2 ≤ q := hq ▸ Finite.one_lt_card
  have h := index_projStabilizer_eq_isoGaussian hq hW
  have key : isoGaussian 2 (finrank K W) q = ((q : ℚ) + 1) * ((q : ℚ) ^ 2 + 1) := by
    rcases finrank_eq_one_or_two hW0 hW with h1 | h2
    · rw [h1, isoGaussian_one]
      have hq1 : (q : ℚ) - 1 ≠ 0 := by
        have : (2 : ℚ) ≤ q := by exact_mod_cast hq2
        linarith
      rw [div_eq_iff hq1]
      ring
    · rw [h2, isoGaussian_self hq2]
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, zero_add, pow_one]
  rw [key] at h
  exact_mod_cast h

theorem extremal_parabolics [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] {q : ℕ}
    (hq : Nat.card K = q) :
    spExtremalParabolics 2 K p = spMaximalParabolics 2 K p ∧
    spExtremalParabolics 2 K p = pointParabolics K ∪ planeParabolics K ∧
    Disjoint (pointParabolics K) (planeParabolics K) ∧
    (pointParabolics K).Nonempty ∧ (planeParabolics K).Nonempty ∧
    Set.BijOn (projStabilizer 2 K)
      {W | W ≠ ⊥ ∧ IsTotallyIsotropic (pairedSympForm K 2) W} (spExtremalParabolics 2 K p) ∧
    (∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), W ≠ ⊥ →
      IsTotallyIsotropic (pairedSympForm K 2) W → finrank K W = 1 ∨ finrank K W = 2) ∧
    ∀ M ∈ spExtremalParabolics 2 K p, M.index = (q + 1) * (q ^ 2 + 1) := by
  obtain ⟨hM, -, -⟩ := maximal_parabolics (K := K) p (by norm_num : 1 ≤ 2)
  have hidx : ∀ M ∈ spMaximalParabolics 2 K p, M.index = (q + 1) * (q ^ 2 + 1) := by
    intro M hMm
    rw [hM] at hMm
    obtain ⟨W, hW0, hW, rfl⟩ := hMm
    exact index_projStabilizer_two hq hW0 hW
  have hEM : spExtremalParabolics 2 K p = spMaximalParabolics 2 K p := by
    ext M
    exact ⟨fun h => h.1, fun h => ⟨h, fun M' hM' => by rw [hidx M h, hidx M' hM']⟩⟩
  have hXY : spMaximalParabolics 2 K p = pointParabolics K ∪ planeParabolics K := by
    rw [hM]
    ext M
    constructor
    · rintro ⟨W, hW0, hW, rfl⟩
      rcases finrank_eq_one_or_two hW0 hW with h1 | h2
      · exact Or.inl ⟨W, h1, rfl⟩
      · exact Or.inr ⟨W, hW, h2, rfl⟩
    · rintro (⟨L, hL, rfl⟩ | ⟨W, hW, h2, rfl⟩)
      · exact ⟨L, ne_bot_of_finrank_pos (by omega), isTotallyIsotropic_of_finrank_eq_one hL, rfl⟩
      · exact ⟨W, ne_bot_of_finrank_pos (by omega), hW, rfl⟩
  refine ⟨hEM, hEM.trans hXY, Set.disjoint_left.mpr ?_, ⟨_, flag 2 K 1, ?_, rfl⟩,
    ⟨_, flag 2 K 2, isCompleteIsotropicFlag_flag.2.2 2 le_rfl, finrank_flag (by norm_num),
      rfl⟩, ⟨fun W hW => ?_, fun W hW W' hW' h => ?_, fun M hM' => ?_⟩,
    fun W hW0 hW => finrank_eq_one_or_two hW0 hW, fun M hM' => hidx M (hEM ▸ hM')⟩
  · rintro _ ⟨L, hL, rfl⟩ ⟨W, hW, h2, hLW⟩
    have := projStabilizer_inj (ne_bot_of_finrank_pos (by omega))
      (isTotallyIsotropic_of_finrank_eq_one hL) (ne_bot_of_finrank_pos (by omega)) hW hLW
    rw [this, h2] at hL
    exact absurd hL (by norm_num)
  · exact finrank_flag (by norm_num)
  · rw [hEM, hM]
    exact ⟨W, hW.1, hW.2, rfl⟩
  · exact projStabilizer_inj hW.1 hW.2 hW'.1 hW'.2 h
  · rw [hEM, hM] at hM'
    obtain ⟨W, hW0, hW, rfl⟩ := hM'
    exact ⟨W, ⟨hW0, hW⟩, rfl⟩

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
