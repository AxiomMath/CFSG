module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def Sec8T84FactModB : Prop :=
  ∀ (G : Type) [Group G] (E B : Subgroup G), IsElemAb2 E 8 → IsElemAb2 B 4 → B ≤ E →
    ∀ (u : MulAut ↥E) (A : Subgroup (MulAut ↥E)) (h : MulAut ↥E),
      u * u = 1 →
      (∀ e : ↥E, u e = e ↔ (e : G) ∈ B) →
      (∀ b ∈ B, ∃ e : ↥E, (e : G) * ((u e : ↥E) : G)⁻¹ = b) →
      Nonempty (↥A ≃* alternatingGroup (Fin 6)) →
      (∀ a ∈ A, a * u = u * a) →
      (∀ a ∈ A, (∀ e : ↥E, (e : G) ∈ B → a e = e) → a = 1) →
      h * u = u * h → (∀ a ∈ A, h * a * h⁻¹ ∈ A) →
      (∀ e : ↥E, (e : G) ∈ B → h (h e) = e) →
      Nat.card {e : ↥E // (e : G) ∈ B ∧ h e = e} = 8 →
        ∃ h' : MulAut ↥E, (h' = h ∨ h' = h * u) ∧ h' * h' = 1 ∧
          Nat.card {e : ↥E // h' e = e} = 64 ∧
          ∀ k : MulAut ↥E, k * u = u * k → (∀ a ∈ A, k * a * k⁻¹ ∈ A) →
            (∀ e : ↥E, (e : G) ∈ B → k (h e) = h (k e)) → k * h' = h' * k

end CFSG.OddStandard.SmallF3.Omega
