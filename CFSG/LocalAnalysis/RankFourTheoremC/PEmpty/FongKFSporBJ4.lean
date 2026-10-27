module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBWit
public import CFSG.Sporadic.Schreier.J4SEleven

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Blueprint
open scoped commutatorElement

theorem j4Eleven_reach : ∀ w : Fin 2 → ZMod 11, w ≠ 0 → ∃ s : ZMod 11, s ≠ 0 ∧
    s • w ∈ Heis.reach [!![((7 : ℕ) : ZMod 11), ((3 : ℕ) : ZMod 11); ((3 : ℕ) : ZMod 11),
      ((3 : ℕ) : ZMod 11)], !![((8 : ℕ) : ZMod 11), ((10 : ℕ) : ZMod 11);
      ((6 : ℕ) : ZMod 11), ((5 : ℕ) : ZMod 11)]] 6 := by
  decide +kernel

theorem j4Eleven_oneClassE_J :
    OneClassE 11 J := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨x, y, z, h₁, h₂, c, -, hext, -, hexp, hz, hcenter, -, -, h1x, h1y, -, h2x, h2y, -, -,
    -, -, -, -, -, -⟩ := R3E_J4_eleven_normalizer_transitivity_and_fixed_dimensions
  subst hz
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set J) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set J) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx : x ^ 11 = 1 := pow_eq_one_of_mem_exponent hxQ hexp
  have hy : y ^ 11 = 1 := pow_eq_one_of_mem_exponent hyQ hexp
  have hzmem : ⁅x, y⁆ ∈ (Subgroup.center (Subgroup.closure ({x, y} : Set J))).map
      (Subgroup.closure ({x, y} : Set J)).subtype := by
    rw [hcenter]
    exact Subgroup.mem_zpowers _
  have hzx : Commute ⁅x, y⁆ x :=
    commute_of_mem_center_map (S := Subgroup.closure ({x, y} : Set J)) hzmem hxQ
  have hzy : Commute ⁅x, y⁆ y :=
    commute_of_mem_center_map (S := Subgroup.closure ({x, y} : Set J)) hzmem hyQ
  have hne : ⁅x, y⁆ ≠ 1 :=
    ne_one_of_center_card (S := Subgroup.closure ({x, y} : Set J)) hcenter hext.2.2.2 (by norm_num)
  have hsyl : ¬ 11 ^ 4 ∣ Nat.card J := by
    rw [CFSG.Sporadic.J4.card_J CFSG.Sporadic.J4.j4Facts]
    decide
  haveI : Finite J := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.J4.card_J CFSG.Sporadic.J4.j4Facts]; norm_num)
  exact oneClassE_of_witness (by norm_num) hsyl hx hy hne hzx hzy h1x h1y h2x h2y 6
    j4Eleven_reach

theorem j4Eleven_oneClassE :
    OneClassE 11 NativeSporadic.J4 :=
  @OneClassE.of_mulEquiv 11 J NativeSporadic.J4 _ _
    (seedEquiv CFSG.Sporadic.J4.j4Facts.mat).symm j4Eleven_oneClassE_J

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
