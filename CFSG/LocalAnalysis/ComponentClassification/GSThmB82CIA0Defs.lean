module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA7

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

@[expose] def GS82Step2ConjInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
    ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
    (c.s.h.secG0 c.s.y).relIndex c.s.h.S ≠ 2 →
    ∃ u ∈ c.s.h.S, u⁻¹ * c.b * u = c.s.h.a * c.b

@[expose] def GS82Step6PumpInputA0 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
    ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
    ¬ (c.s.p = 3 ∧ c.s.f = 1) →
    ¬ ((Seven.Lay c.s.h c.s.y).subgroupOf (centralizer ({c.b} : Set X))).IsSubnormal →
    ∃ N : Subgroup X, N ≤ centralizer ({c.b} : Set X) ⊓
        centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({c.b} : Set X) ⊓
        centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ∧
      c.s.h.a * c.b * c.Z.z ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n))

@[expose] def GS82Step6ThreeInputA0 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
    ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
    ∀ g : X, g⁻¹ * c.s.h.a * g = c.s.h.a * c.b * c.Z.z → g⁻¹ * c.Z.z * g = c.b →
    c.s.p = 3 → c.s.f = 1 → False

end CFSG.ComponentClassification.GSThmB
