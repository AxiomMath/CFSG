module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bO8
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


section Ge5

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem false_of_o8p2_ge5 (hp : p.Prime) (hp5 : 5 ≤ p) {K B : Subgroup Y} (h : KHyp p K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3)
    (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isD4two) : False := by
  have hp2 : p ≠ 2 := by omega
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.qs.2
  have hZ : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
    center_eq_bot_of_simple_nonprime (card_o8p2 hcat) (by norm_num)
  have hmodel := D4XF.statedModel_of_d4two hcat
  obtain ⟨φ⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hmodel
    CFSG.EvenSmallLie.OmegaEight.statedClassicalModel_omegaT
  have hOutc : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) = 6 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv]
    exact CFSG.EvenSmallLie.OmegaEight.card_outer_omegaT
  have hOut : ¬ p ∣ Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) := by
    rw [hOutc]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases p
    · norm_num at hd
    · exact absurd hp (by norm_num)
  obtain ⟨-, K₀, _, _, hK₀, ⟨e'⟩⟩ := hmodel
  have hK₀' : Nat.card K₀ = 2 := by rw [hK₀]; norm_num
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK₀']; norm_num)
  have hrank : CFSG.Assembly.RankThreeEven.localRank p (↥K ⧸ Subgroup.center ↥K) ≤ 1 := by
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e' hp]
    have h1 := CFSG.RankThree.PartOne.KFU.localRank_statedProj_statedOmega_quadPlus_le (K := K₀)
      (n := 4) (by norm_num) hp
    have h2 := CFSG.RankThree.PartOne.KFU.localRank_statedSp_four_le_one (K := K₀) hK₀' hp hp5
    omega
  exact false_of_rank_bound hp hp2 h hc (MulEquiv.refl _) hZ
    (inner_of_pow_eq_one_of_not_dvd_outer hp hOut) (rankBound_of_localRank_le_one hp hrank)

end Ge5

theorem kDescFam_o8p2 (hR : ∀ (Y : Type) [Group Y] [Finite Y], Rank23At Y) (p : ℕ) :
    KDescFam p fO8p2 := by
  intro hp hp2 Y _ _ K B h hc hcB
  have hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isD4two := hc
  by_cases hp3 : p = 3
  · subst hp3
    exact (false_of_o8p2 (hR Y) h hcB hcat).elim
  · have hp5 : 5 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p
      · exact Nat.not_prime_zero hp
      · exact Nat.not_prime_one hp
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by norm_num)
    exact (false_of_o8p2_ge5 hp hp5 h hcB hcat).elim

end CFSG.LocalAnalysis.GLTheoremA
