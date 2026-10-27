module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf8Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace ThmE

section Steps


class PrintedQuotOdd (r : ℕ) : Prop where
  exists_W : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) (N : Subgroup G) [N.Normal],
    EStand r Ω K S R W → TwinThmEW.CentPairs Ω (S : Subgroup G) W H → Odd (Nat.card N) → N ≤ H →
      ∃ Wb ∈ WSet (quotFamily Ω N),
        Wb ≤ (S : Subgroup G).map (QuotientGroup.mk' N) ∧
        (∀ s ∈ (S : Subgroup G).map (QuotientGroup.mk' N), conjSub s Wb = Wb) ∧
        TwinThmEW.CentPairs (quotFamily Ω N) ((S : Subgroup G).map (QuotientGroup.mk' N)) Wb
          (H.map (QuotientGroup.mk' N))

class PrintedQuotCent (r : ℕ) : Prop where
  exists_W : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) (N : Subgroup G) [N.Normal],
    MinCex r Ω K S R W H → N ≤ Subgroup.center G → IsPGroup 2 ↥N → N ≤ H →
      (∀ J ∈ Ω, J ⊓ N = ⊥) →
      ∃ Wb ∈ WSet (quotFamily Ω N),
        Wb ≤ (S : Subgroup G).map (QuotientGroup.mk' N) ∧
        (∀ s ∈ (S : Subgroup G).map (QuotientGroup.mk' N), conjSub s Wb = Wb) ∧
        TwinThmEW.CentPairs (quotFamily Ω N) ((S : Subgroup G).map (QuotientGroup.mk' N)) Wb
          (H.map (QuotientGroup.mk' N))

class PrintedHull (r : ℕ) : Prop where
  exists_W : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) (w : G),
    MinCex r Ω K S R W H → w ≠ 1 → w * w = 1 →
    ∀ S₁ : Sylow 2 ↥(coreHull Ω w), R ≤ (S₁ : Subgroup ↥(coreHull Ω w)).map (TwinThmE.secEmb Ω w) →
      ∃ W₁ ∈ WSet (hullFam Ω w), W₁ ≤ (S₁ : Subgroup ↥(coreHull Ω w)) ∧
        (∀ s ∈ (S₁ : Subgroup ↥(coreHull Ω w)), conjSub s W₁ = W₁) ∧
        TwinThmEW.CentPairs (hullFam Ω w) (S₁ : Subgroup ↥(coreHull Ω w)) W₁
          (H.comap (TwinThmE.secEmb Ω w))

@[expose] def E18_1 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      (∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) ∧ ∃ J ∈ Ω, J ∉ dstarComp Ω K

@[expose] def E18_3 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H → ∀ J ∈ Ω, ∃ g : G, conjSub g K = J

@[expose] def E18_4C (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → IsPGroup 2 ↥(R ⊔ R') →
        ∀ w : G, w ≠ 1 → w * w = 1 → R ⊔ R' ≤ Subgroup.centralizer ({w} : Set G) →
          Subgroup.centralizer ({w} : Set G) ≠ ⊤ → Subgroup.centralizer ({w} : Set G) ≤ H

@[expose] def E18_5 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H → (⨆ J ∈ Ω, J) = ⊤

@[expose] def E18_6O2 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q →
        Q ≤ Subgroup.center G ∧ ∀ J ∈ Ω, J ⊓ Q = ⊥

@[expose] def E18_6 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      classicalInvolutionOddCore G = ⊥ ∧
        ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
          Subgroup.centralizer (F : Set G) = ⊥

@[expose] def E18_7 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      ∀ a : G, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H →
        ∀ g : G, g * a * g⁻¹ ∈ H → ∃ h ∈ H, h * a * h⁻¹ = g * a * g⁻¹

@[expose] def E18_8z (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → FixesUniqueCoset z H

@[expose] def E18_9 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → ∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) →
        h⁻¹ * z * h ≠ z → z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z →
          FixesUniqueCoset (z * (h⁻¹ * z * h)) H

@[expose] def E18_endC (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      (∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
        Subgroup.centralizer (F : Set G) = ⊥) →
      ∀ z : G, IsUniqueInvolution K z →
        IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
          (Subgroup.centralizer ({z} : Set G)) →
        FixesUniqueCoset z H →
        (∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) → h⁻¹ * z * h ≠ z →
          z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z → FixesUniqueCoset (z * (h⁻¹ * z * h)) H) →
        False

@[expose] def ConfigSylowCentralizer (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H → ∀ z : G, IsUniqueInvolution K z →
      ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCex r Ω K S' R W' H ∧
        IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
          (Subgroup.centralizer ({z} : Set G))

theorem minCexFalse_of_steps {r : ℕ} (hC : ConfigSylowCentralizer r) (h6 : E18_6 r) (h8 : E18_8z r)
    (h9 : E18_9 r) (hend : E18_endC r) : MinCexFalse r := by
  intro G _ _ Ω K S R W H c
  obtain ⟨K', ⟨-, z, hz1, -⟩, -⟩ := c.stand.twin
  obtain ⟨S', W', c', hSyl⟩ := hC G Ω K S R W H c z hz1
  obtain ⟨-, hF⟩ := h6 G Ω K S' R W' H c'
  have hzc : FixesUniqueCoset z H := h8 G Ω K S' R W' H c' z hz1
  exact hend G Ω K S' R W' H c' hF z hz1 hSyl hzc fun h h1 h2 h3 =>
    h9 G Ω K S' R W' H c' z hz1 h h1 h2 h3

end Steps

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
