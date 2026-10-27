module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110n
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenD5Index
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Recog

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o

open CFSG.Open CFSG.Blueprint
open CFSG.Open.StatedAPI
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110n

theorem card_ne_of_mulEquiv_lie {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex)
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : ∀ q : TauCeti.PrimePower, d.1 = .D 4 q → q.card ≠ 2) :
    Nat.card X ≠ 174182400 := by
  intro hX
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hcard : Nat.card X = lieOrderFormula d.1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d X ⟨e⟩
  have h : lieOrderFormula d.1 = 174182400 := hcard.symm.trans hX
  obtain ⟨q, hq, hq2⟩ := eq_D4_two_of_lieOrderFormula_d4n d.2 h
  exact hd q hq hq2

theorem card_statedClassicalModel_PSU_ne_d4n {G : Type} [Group G] {m p f : ℕ}
    (h : StatedClassicalModel G .PSU (m + 1) p f) :
    Nat.card G ≠ 174182400 := by
  obtain ⟨q, hv, -, -, ⟨e⟩⟩ :=
    exists_twistedA_of_statedClassicalModel_PSU h
  refine card_ne_of_mulEquiv_lie ⟨.twistedA m q, hv⟩ e ?_
  intro q' hq'
  cases hq'

theorem card_statedClassicalModel_PSL_ne_d4n {G : Type} [Group G] {n p f : ℕ}
    (h : StatedClassicalModel G .PSL n p f) : Nat.card G ≠ 174182400 := by
  intro hc
  have hn2 : 2 ≤ n := h.1.2.2.1
  have hcard := card_of_statedClassicalModel_psl (by omega : 0 < n) h
  have horder : Nat.card G = CFSG.Open.orderA (n - 1) (p ^ f) := by
    rw [hcard, CFSG.Open.orderA, Nat.sub_add_cancel (by omega : 1 ≤ n),
      Nat.mul_comm n (n - 1)]
  have hn1 : 1 ≤ n - 1 := Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn2)
  have hf0 : f ≠ 0 := Nat.ne_of_gt h.1.2.1
  have hpkw : IsPrimePow (p ^ f) := h.1.1.isPrimePow.pow (k := f) hf0
  exact orderA_ne_d4n hn1 hpkw (horder.symm.trans hc)

theorem card_lieModel_POmegaMinus_ne_d4n {G : Type} [Group G] {n r e : ℕ}
    (h : LieModel G .POmegaMinus n r e) : Nat.card G ≠ 174182400 := by
  have hclass : StatedClassicalModel G .POmegaMinus n r e := h.statedClassicalModel (by decide)
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨eG⟩⟩ := hclass
  haveI : Fintype K := Fintype.ofFinite K
  have hn4 : 4 ≤ n := h.admissible.2.2
  obtain ⟨q, hv, -, ⟨eq⟩⟩ :=
    exists_twistedD_of_statedProj_minus (K := K) n hn4 hirr
  refine card_ne_of_mulEquiv_lie ⟨.twistedD n q, hv⟩ (eG.trans eq) ?_
  intro q' hq'
  cases hq'

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o
