module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem515
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_11_three_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D : Subgroup G) (n : ℕ), Hyp5_1_8 G T M L H n →
    IsNotation5_1_9 T M L H B D → IsLieRankTwoK T H →
      (∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
          pCoreOf 2 (M ⊓ H) ≤ Subgroup.normalizer (P : Set G)) ∨
        (LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 ∧
          (oTwoUpper H ⊔ pCoreOf 2 H).relIndex (oTwoUpper H ⊔ pCoreOf 2 (M ⊓ H)) = 2 ∧
          E2.IsDiagramNontrivial (pCoreOf 2 (M ⊓ H)) (oTwoUpper H) (T ⊓ oTwoUpper H))

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L : Subgroup G} {n : ℕ}

theorem inf_L_eq_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    {H : Subgroup G} (hH : IsHStar T M H) : pCoreOf 2 (M ⊓ H) ⊓ L = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm (inf_le_inf_right L (h.pCoreOf_inf_le hH.1.1))
  refine le_inf ?_ inf_le_right
  have hN : M ⊓ H ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [inf_comm]
    exact h.inf_le_normalizer_inf_F4 h331 hR hH
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans (le_inf h.T_le hH.1.1)) hN
    (h.sylow.1.to_le inf_le_left)

end Hyp5_0_1

theorem stmt5_1_11_of_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (h510 : Stmt5_1_10_F4)
    (h3 : Stmt5_1_11_three_F4) : Stmt5_1_11_F4 := by
  intro G _ _ T M L H B D n hyp hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left h.sup_le_normalizer
  obtain ⟨k, -, hBorel, -⟩ := h510 G T M L H B D n hyp hN
  refine ⟨?_, ?_, h3 G T M L H B D n hyp hN⟩
  · rw [hyp.inf_oTwoUpper_eq hBorel]
    exact hTK
  · rw [h.inf_L_eq_F4 h331 hR hyp.hStar]
    exact hSL

end CFSG.Quasithin.H13
