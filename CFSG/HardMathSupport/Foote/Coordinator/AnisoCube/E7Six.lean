module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Skeleton
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.OrderSix
public import CFSG.HardMathSupport.Malle.SeitzCube.E7High

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.Open CFSG.LieType.SeitzGeneration

@[expose] def E7SixPlane : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) (p : ℕ), p.Prime →
    p ≠ 3 → p ≠ q.p → orderOf ((q.card : ℕ) : ZMod p) = 6 →
    ∃ E A : Subgroup (Cat ⟨.E7 q, hv⟩), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ A ≤ E ∧
      A ≠ ⊥ ∧ NormalizesRSub ⟨.E7 q, hv⟩ A ∧
      ∀ B : Subgroup (Cat ⟨.E7 q, hv⟩), B ≤ A → B.relIndex A = p →
        ∀ k, (∀ f ∈ B, f * k = k * f) → k ∈ hyperClosure p ⊤ E


theorem excCubeHighAt_E7_six_of_plane (h : E7SixPlane) :
    CFSG.HardMathSupport.Malle.SeitzCube.ExcCubeHighAt TauCeti.LieTypeIndex.E7 6 := by
  intro q hv p hp _ hpq _ _ hord _
  obtain ⟨-, hp3⟩ := dvd_sq_sub_add_one_of_orderOf_eq_six hp hord
  obtain ⟨E, A, hE, hc, hAE, hA1, hR, hlines⟩ := h q hv p hp hp3 hpq hord
  have hA : IsElemAbelian p A := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => hE.2 x (hAE hx)⟩
    apply Subtype.ext
    have h := congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨a, hAE a.2⟩ ⟨b, hAE b.2⟩)
    exact h
  refine ⟨E, hE, hc, Or.inr (hyperGen_of_hyperGen_of_le ?_ hlines)⟩
  exact seitzExcParabolicHyperUntw ⟨TauCeti.LieTypeIndex.E7 q, hv⟩ p hp
    (by rw [TauCeti.LieTypeIndex.characteristic_E7]; exact hpq)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))) A hA hA1 hR

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
