module

public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Lie

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Open CFSG.RankThree.PartOne.OutStructure
open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem meets_inner_of_outPChain {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (h : OutPChain p S) (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) :
    ∃ x ∈ D ⊓ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : D ⊓ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hcon x hx
  have hDel : CFSG.IsElementaryAbelian p ↥D :=
    { toIsMulCommutative := hD.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hD.2 x x.2) }
  exact CFSG.RankThree.PartOne.PlaneCases.no_plane_of_outPChain hp h D hDel hcard hbot

theorem pRank_mulAut_le_of_outPChain {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥) (h : OutPChain p S) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ CFSG.Open.pRank p (⊤ : Subgroup S) + 1 :=
  pRank_mulAut_le_of_meets hp hcen 1 fun D hD hc =>
    meets_inner_of_outPChain hp h D hD (by simpa using hc)

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
