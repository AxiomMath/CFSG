module

public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import CFSG.RankThree.PartOne.CTP.StrongPLinear
import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.Heisenberg
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Monster.B.Pinned
open scoped commutatorElement

theorem hasNoncommPair_of_commData {G : Type*} [Group G] {p n : ℕ} (hp : p.Prime)
    {q : Fin n → G} {z : G} {M : Matrix (Fin n) (Fin n) (ZMod p)} (h : CommData p q z M)
    {i j : Fin n} (hij : bcomm (q i) (q j) = z) :
    CFSG.RankThree.PartOne.StrongP.HasNoncommPair p G := by
  have hz1 : z ≠ 1 := by
    intro h1
    have := h.orderOf_z
    rw [h1, orderOf_one] at this
    exact hp.one_lt.ne this
  have hc : ⁅(q i)⁻¹, (q j)⁻¹⁆ = z := by
    rw [commutatorElement_eq_bcomm, inv_inv, inv_inv]
    exact hij
  refine CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_of_central_commutator hp
    (x := (q i)⁻¹) (y := (q j)⁻¹) ?_ ?_ (by rw [hc]; exact hz1) ?_ ?_
  · rw [inv_pow, h.pow_q i, inv_one]
  · rw [inv_pow, h.pow_q j, inv_one]
  · rw [hc]
    exact (show Commute z (q i) from (h.comm_z i).symm).inv_right
  · rw [hc]
    exact (show Commute z (q j) from (h.comm_z j).symm).inv_right

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
