module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE1
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelTab
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelClaim
public meta import CFSG.GH74.GLS.C3.Layer2.L4ModelGen
public meta import CFSG.GH74.GLS.C3.Layer2.L4ModelE1
public import Certificates.Certificate5038
public import Certificates.Certificate5039
public import Certificates.Certificate5041
public import Certificates.Certificate5042
public import CFSG.GH74.GLS.C3.Layer2.FinModelClaimCheck

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

theorem e1Claim1_6 :
    (mkTab 6).claimG (mkTab 6).e1P1 = true :=
  Certificates.certificate5042.1

theorem e1Claim1_7 :
    (mkTab 7).claimG (mkTab 7).e1P1 = true :=
  Certificates.certificate5042.2.1

theorem e1Claim2_6 :
    (mkTab 6).claimG (mkTab 6).e1P2 = true :=
  Certificates.certificate5042.2.2.1

theorem e1Claim2_7 :
    (mkTab 7).claimG (mkTab 7).e1P2 = true :=
  Certificates.certificate5042.2.2.2.1

theorem e1Claim3_6 :
    (mkTab 6).claimG (mkTab 6).e1P3 = true :=
  Certificates.certificate5042.2.2.2.2.1

theorem e1Claim3_7 :
    (mkTab 7).claimG (mkTab 7).e1P3 = true :=
  Certificates.certificate5042.2.2.2.2.2.1

theorem e1Cover6 : (mkTab 6).cfCoverE1 = true :=
  Certificates.certificate5042.2.2.2.2.2.2.1

theorem e1Cover7 : (mkTab 7).cfCoverE1 = true :=
  Certificates.certificate5042.2.2.2.2.2.2.2.1

theorem e1CfCard6 : (cfSetE1 6).card = 64 :=
  Certificates.certificate5042.2.2.2.2.2.2.2.2.1

theorem e1CfCard7 : (cfSetE1 7).card = 192 :=
  Certificates.certificate5042.2.2.2.2.2.2.2.2.2

theorem model_E1
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
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V) :
    ∃ E : Subgroup (T0 n),
      (∀ t : T0 n, t ∈ E ↔ (t = 1 ∨ t = vHat n α ∨
        (orderOf t = 2 ∧ t ∈ X ∧ t * vHat n α = vHat n α * t ∧ t * vHat n α ∈ X))) ∧
      Nat.card E = 8 ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
      (∀ t : T0 n, ∀ e ∈ E, t * e * t⁻¹ ∈ E) ∧ (∀ e ∈ E, α e ∈ E) ∧
      (∀ g ∈ Fgrp n, g * ((vHat n α : T0 n) : Amb n) = ((vHat n α : T0 n) : Amb n) * g →
        ∀ e ∈ E, g * (e : Amb n) * g⁻¹ ∈ liftT n E) ∧
      (∀ s t : T0 n, orderOf s = 2 → orderOf t = 2 → s ∈ V → t ∈ V → x0T n * s ∈ X →
        x0T n * t ∈ X → ∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∧
      Nat.card (Hgrp n ((vHat n α : T0 n) : Amb n)) = (if n = 6 then 64 else 192) := by
  have hvB : (mkTab n).validB = true := by
    rcases hn with rfl | rfl
    · exact validB6
    · exact validB7
  have hcB : (mkTab n).claimB = true := by
    rcases hn with rfl | rfl
    · exact claimB6
    · exact claimB7
  have hc1 : (mkTab n).claimG (mkTab n).e1P1 = true := by
    rcases hn with rfl | rfl
    · exact e1Claim1_6
    · exact e1Claim1_7
  have hc2 : (mkTab n).claimG (mkTab n).e1P2 = true := by
    rcases hn with rfl | rfl
    · exact e1Claim2_6
    · exact e1Claim2_7
  have hc3 : (mkTab n).claimG (mkTab n).e1P3 = true := by
    rcases hn with rfl | rfl
    · exact e1Claim3_6
    · exact e1Claim3_7
  have hcov : (mkTab n).cfCoverE1 = true := by
    rcases hn with rfl | rfl
    · exact e1Cover6
    · exact e1Cover7
  have hcf : (cfSetE1 n).card = if n = 6 then 64 else 192 := by
    rcases hn with rfl | rfl
    · exact e1CfCard6.trans (by decide)
    · exact e1CfCard7.trans (by decide)
  exact model_E1_aux n hn (mkTab n) (Tab.valid_of_validB _ hvB) hcB hc1 hc2 hc3 hcov hcf α u X V
    hx hu hsq hext hX hV hdisj hclX hclV hQ

end CFSG.GH74.GLS.C3.Layer2.Model
