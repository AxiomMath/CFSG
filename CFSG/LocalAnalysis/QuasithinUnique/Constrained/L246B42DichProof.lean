module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup

@[expose] def ThreeA7Exclusion : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → X1.IsIrrOn L →
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
      Subgroup.center ↥L ≠ ⊥ → E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ →
      IsElemAbelian2 E → IsQuadratic E → Nat.card E * Nat.card (fixV E) < Nat.card W

namespace Dichotomy

theorem isIrrOn_of_isIrrSec {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (h : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤) : X1.IsIrrOn L := by
  refine ⟨?_, TypeList.irr_of_isIrrSec h⟩
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt h.1
  exact ⟨⟨x, 1, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _)⟩⟩

theorem exists_quadratic_offender {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {E : Subgroup (MulAut W)} (hE : E ≠ ⊥) (hel : IsElemAbelian2 E)
    (hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E)) :
    ∃ A : Subgroup (MulAut W), A ≤ E ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧ IsQuadratic A ∧
      Nat.card W ≤ Nat.card A * Nat.card (fixV A) := by
  have hV : ∀ v : W, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hW v
  have hFF : IsFFModule E := ⟨E, le_rfl, hE, hel, hoff⟩
  obtain ⟨A₀, hA₀⟩ := ((B1_4_5 hV E).out 1 2).1 hFF
  obtain ⟨A, hA, hmin⟩ := Set.exists_min_image {A | IsFFStarOffender E A}
    (fun B => Nat.card B) (Set.toFinite _) ⟨A₀, hA₀⟩
  have hquad : IsQuadratic A := B1_4_3_of_minimal hV hA fun B hB hBA =>
    Subgroup.eq_of_le_of_card_ge hBA (hmin B hB)
  refine ⟨A, hA.1, hA.2.1, hA.2.2.1, hquad, ?_⟩
  have h := hA.2.2.2 ⊥ bot_le
  rwa [B1.card_bot_mul_card_fixV] at h

end Dichotomy

end CFSG.QuasithinUnique.Bridge
