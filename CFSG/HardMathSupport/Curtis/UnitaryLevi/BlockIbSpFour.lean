module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSpMain
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSpBar

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical CFSG.AGLEmbedding.ToralCensus
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {f r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem exists_blocks_sp_three (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r)
    {v : StatedSp r K} (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) : SpPrimaryBlocks 2 f 3 v (proj r K v) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hov : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hinj := proj_injective_of_charTwo (K := K) hr
  have hoa : orderOf (proj r K v) = 3 := by
    rw [orderOf_injective (proj r K) hinj v, hov]
  exact (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK Nat.prime_three
    (by norm_num) (by norm_num) hr (proj r K v) hoa).2 v rfl hov

theorem exists_perfect_cent_sp_two (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {v : StatedSp 2 K} (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) :
    ∃ V : Subgroup (StatedSp 2 K), V ≤ Subgroup.centralizer ({v} : Set (StatedSp 2 K)) ∧
      ⁅V, V⁆ = V ∧ V ≠ ⊥ := by
  have HB := exists_blocks_sp_three (by omega) hK (by norm_num) hv3 hv1
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have key : PerfectThreeIn (Subgroup.centralizer ({v} : Set (StatedSp 2 K))) ∨
      PerfectNoncycThreeIn (Subgroup.centralizer ({v} : Set (StatedSp 2 K))) := by
    obtain ⟨s, hs, -⟩ := HB.rank
    by_cases hs2 : 2 ≤ s
    · exact Or.inr ((perfectNoncycThreeIn_spFixed HB (by omega)).mono
        (spSupported_le_centralizer _))
    refine Or.inl ?_
    by_cases hs1 : s = 1
    · subst hs1
      exact (perfectThreeIn_spFixed HB (by omega) h4).mono (spSupported_le_centralizer _)
    · have hs0 : s = 0 := by omega
      subst hs0
      obtain ⟨h, hX, hm, hdeg, hdeg1⟩ := exists_factor_of_lt HB hv3 hs (by omega)
      have hrecX : reciprocalPolynomial (h : K[X]) ≠ X - 1 := fun h1 => by
        have hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd v) := h1 ▸ HB.bijOn.mapsTo h.2
        exact hX (HB.bijOn.injOn h.2 hX1 (by rw [h1, reciprocalPolynomial_X_sub_one]))
      by_cases hself : reciprocalPolynomial (h : K[X]) = h
      · exact (perfectThreeIn_spSelfDual HB hf h hX hself hdeg (by omega)).mono
          (spSupported_le_centralizer _)
      · exact (perfectThreeIn_spPaired HB hf h (Ne.symm hself) hX (by omega)).mono
          (spSupported_le_centralizer _)
  rcases key with ⟨V, hV, hVp, x, hxV, -, hx1⟩ | ⟨V, hV, hVp, Q, hQV, -, hQ⟩
  · refine ⟨V, hV, hVp, fun h => hx1 ?_⟩
    have := hxV
    rw [h, Subgroup.mem_bot] at this
    exact this
  · refine ⟨V, hV, hVp, fun h => hQ ?_⟩
    have hQbot : Q = ⊥ := le_bot_iff.mp (h ▸ hQV)
    subst hQbot
    infer_instance

theorem false_of_blockBar_sp_four (hK : 4 ≤ Nat.card K) {J : Subgroup (StatedSp 2 K)}
    {v : StatedSp 2 K} (h : BlockBarData J v) : False := by
  obtain ⟨f, hf⟩ : ∃ f, Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have : f ≤ 1 := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
    omega
  obtain ⟨V, hV, hVp, hVbot⟩ := exists_perfect_cent_sp_two hf hf2 h.pow h.ne_one
  exact hVbot (h.free V hV hVp)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
