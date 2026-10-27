module

public import CFSG.Milestones.SE_simple_strong_embedding_models
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.Models.BenderSuzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.Open

theorem strong_embedding_sylow_sixty_four_center_four
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (M : Subgroup G) (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M)
    (S : Sylow 2 G) (hS : Nat.card (S : Subgroup G) = 64)
    (hZ : Nat.card (Subgroup.center (S : Subgroup G)) = 4) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 2 := by
  have h2 : Function.Injective (fun k : ℕ => 2 ^ k) := Nat.pow_right_injective le_rfl
  cases CFSG.Milestones.bender_suzuki M hM with
  | isPSL2 n hn e =>
    have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_equiv G e.toEquiv
    obtain ⟨-, -, -, hZq, hSq⟩ := (bender_psl2_borel_full n hn).map_mulEquiv e.symm S
    rw [hZ] at hZq
    rw [hS, pow_one, ← hZq] at hSq
    norm_num at hSq
  | isSuzuki n hn e =>
    have hmodel : CFSG.Theory.Comparator.SzModel n = Sz n := CFSG.Models.benderSzModel_eq_sz n
    have : Finite (Sz n) := Finite.of_equiv G (e.trans (MulEquiv.subgroupCongr hmodel)).toEquiv
    obtain ⟨-, -, -, hZq, -⟩ := (bender_suzuki_borel_full n hn).map_mulEquiv
      (e.trans (MulEquiv.subgroupCongr hmodel)).symm S
    rw [hZ, show (4 : ℕ) = 2 ^ 2 by norm_num] at hZq
    have := h2 hZq
    omega
  | isPSU3 n hn e =>
    have hmodel : CFSG.Theory.Comparator.PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
    have : Finite (PSU3 2 n) := Finite.of_equiv G (e.trans (MulEquiv.subgroupCongr hmodel)).toEquiv
    obtain ⟨-, -, -, -, hSq⟩ := (bender_psu3_borel_full n hn).map_mulEquiv
      (e.trans (MulEquiv.subgroupCongr hmodel)).symm S
    rw [hS, ← pow_mul, show (64 : ℕ) = 2 ^ 6 by norm_num] at hSq
    have hn2 : n = 2 := by have := h2 hSq; omega
    subst hn2
    exact (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff G 2 le_rfl).mpr ⟨e⟩

end CFSG.LyonsUnitaryFour
