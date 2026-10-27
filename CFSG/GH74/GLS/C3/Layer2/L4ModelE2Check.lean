module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE2
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelTab
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelClaim
public meta import CFSG.GH74.GLS.C3.Layer2.L4ModelGen
public meta import CFSG.GH74.GLS.C3.Layer2.L4ModelE1
public meta import CFSG.GH74.GLS.C3.Layer2.L4ModelE2
public import Certificates.Certificate5038
public import Certificates.Certificate5039
public import Certificates.Certificate5041
public import Certificates.Certificate5043
public import CFSG.GH74.GLS.C3.Layer2.FinModelClaimCheck

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

theorem e2Claim1_6 :
    (mkTab 6).claimG (mkTab 6).e2P1 = true :=
  Certificates.certificate5043.1

theorem e2Claim1_7 :
    (mkTab 7).claimG (mkTab 7).e2P1 = true :=
  Certificates.certificate5043.2.1

theorem e2Claim2_6 :
    (mkTab 6).claimG (mkTab 6).e2P2 = true :=
  Certificates.certificate5043.2.2.1

theorem e2Claim2_7 :
    (mkTab 7).claimG (mkTab 7).e2P2 = true :=
  Certificates.certificate5043.2.2.2.1

theorem e2Claim3_6 :
    (mkTab 6).claimG (mkTab 6).e2P3 = true :=
  Certificates.certificate5043.2.2.2.2.1

theorem e2Claim3_7 :
    (mkTab 7).claimG (mkTab 7).e2P3 = true :=
  Certificates.certificate5043.2.2.2.2.2.1

theorem e2Claim4_6 :
    (mkTab 6).claimG (mkTab 6).e2P4 = true :=
  Certificates.certificate5043.2.2.2.2.2.2.1

theorem e2Claim4_7 :
    (mkTab 7).claimG (mkTab 7).e2P4 = true :=
  Certificates.certificate5043.2.2.2.2.2.2.2

theorem model_E2
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7)
    (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n))
    (hx : α (x0T n) ≠ x0T n) (hu : α u = u) (hsq : ∀ x, α (α x) = u * x * u⁻¹)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (x : T0 n) (hx : (x : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(x : Amb n), hx⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α x : T0 n) : Amb n))
    (hX : x0T n ∈ X) (hV : x0T n * α (x0T n) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V)
    (E : Subgroup (T0 n))
    (hE : ∀ t : T0 n, t ∈ E ↔ (t = 1 ∨ t = vHat n α ∨
      (orderOf t = 2 ∧ t ∈ X ∧ t * vHat n α = vHat n α * t ∧ t * vHat n α ∈ X))) :
    ∃ A : Subgroup (T0 n),
      (∀ t : T0 n, t ∈ A ↔ ∀ e ∈ E, t * e = e * t) ∧
      Nat.card A = 16 ∧ (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) ∧ (∀ a ∈ A, a * a = 1) ∧
      (∃ b : Fin 4 → T0 n, Function.Injective b ∧
        (∀ i, b i ∈ A ∧ orderOf (b i) = 2 ∧ b i ∈ X ∧ b i ∉ E) ∧
        (∀ t ∈ A, orderOf t = 2 → t ∈ X → t ∉ E → ∃ i, t = b i) ∧
        (∀ t ∈ A, t ∈ Subgroup.closure (Set.range b))) ∧
      (∀ t₀ : T0 n, t₀ * α t₀ * u = 1 → ∃ R : Subgroup (T0 n), R ⊓ A = ⊥ ∧
        (∀ r ∈ R, t₀ * α r * t₀⁻¹ ∈ R) ∧ A ⊔ R = ⊤) ∧
      (∀ s : T0 n, (∀ t : T0 n, s * t = t * s) → α s = s → s * s = 1 → s ≠ 1 →
        s = vHat n α) := by
  have hvB : (mkTab n).validB = true := by
    rcases hn with rfl | rfl
    · exact validB6
    · exact validB7
  have hcB : (mkTab n).claimB = true := by
    rcases hn with rfl | rfl
    · exact claimB6
    · exact claimB7
  have hc1 : (mkTab n).claimG (mkTab n).e2P1 = true := by
    rcases hn with rfl | rfl
    · exact e2Claim1_6
    · exact e2Claim1_7
  have hc2 : (mkTab n).claimG (mkTab n).e2P2 = true := by
    rcases hn with rfl | rfl
    · exact e2Claim2_6
    · exact e2Claim2_7
  have hc3 : (mkTab n).claimG (mkTab n).e2P3 = true := by
    rcases hn with rfl | rfl
    · exact e2Claim3_6
    · exact e2Claim3_7
  have hc4 : (mkTab n).claimG (mkTab n).e2P4 = true := by
    rcases hn with rfl | rfl
    · exact e2Claim4_6
    · exact e2Claim4_7
  exact model_E2_aux n hn (mkTab n) (Tab.valid_of_validB _ hvB) hcB hc1 hc2 hc3 hc4 α u X V
    hx hu hsq hext hX hV hdisj hclX hclV hQ E hE

end CFSG.GH74.GLS.C3.Layer2.Model
