module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.GenToralLinear
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.GenToralUnitary

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

open CFSG.LieType.SeitzGeneration

theorem coverThree_gen_toral
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {K : Type} [Group K]
    [Finite K] (hK : Open.IsQuasisimple K) (d : TauCeti.ValidLieTypeIndex)
    (h9 : (∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ 9 ∣ q.card - 1) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ 9 ∣ q.card + 1))
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hz : 3 ∣ Nat.card (Subgroup.center K))
    (P : Subgroup K) (hPc : IsMulCommutative P) (hP : Nat.card P = 3 ^ 3)
    (hPZ : Nat.card (P ⊓ Subgroup.center K : Subgroup K) = 3)
    (hP3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center K) :
    ∀ k : K, k ∈ Subgroup.closure {k : K | ∃ x ∈ P, x ∉ Subgroup.center K ∧ k * x = x * k} := by
  obtain ⟨dd, hv⟩ := d
  obtain ⟨e⟩ := e
  intro k
  rcases h9 with ⟨q, hq, h9⟩ | ⟨q, hq, h9⟩
  · simp only at hq
    subst hq
    rw [coverThree_gen_toral_linear hK q hv h9 e hz P hPc hP hPZ hP3]
    exact Subgroup.mem_top k
  · simp only at hq
    subst hq
    rw [coverThree_gen_toral_unitary hGA hK q hv h9 e hz P hPc hP hPZ hP3]
    exact Subgroup.mem_top k

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
