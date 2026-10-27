module

public import CFSG.Open.FusionDefs
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

abbrev sec19BPrime {G : Type} [Group G] (K : Subgroup G) (S : Sylow 2 G) (W L : Subgroup G) :
    Subgroup G :=
  (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
    Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L

abbrev sec19T {G : Type} [Group G] (K : Subgroup G) (z : G) (S : Sylow 2 G) : Subgroup G :=
  (S : Subgroup G) ⊓ centralizerModOdd ⊤ (sec19X K z)

@[expose] def ControlCMod {G : Type} [Group G] (J : Subgroup G) : Prop :=
  ∀ t : G, t ≠ 1 → IsPGroup 2 (Subgroup.zpowers t) →
    ∀ A ∈ conjugateSet J, ∀ B ∈ conjugateSet J,
      t ∈ centralizerModOdd ⊤ A → t ∈ centralizerModOdd ⊤ B → B ∈ deltaComp J A

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_11bN3Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      ∀ b ∈ sec19BPrime K S W L, ∀ g : G, g * b * g⁻¹ ∈ (S : Subgroup G) →
        g * b * g⁻¹ ∈ Subgroup.centralizer (W : Set G)

@[expose] def GoldschmidtB1Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (S : Sylow 2 G) (B : Subgroup G), B ≤ (S : Subgroup G) → B ≠ ⊥ →
      fusionStronglyClosed (B : Set G) (S : Subgroup G) →
        (CFSG.perfectResidual (Subgroup.centralizer (B : Set G))).map
          (Subgroup.centralizer (B : Set G)).subtype = ⊥

@[expose] def C19_9s3Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      ∀ a ∈ sec19T K z S, ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ z →
        h * z * h⁻¹ * z = z * (h * z * h⁻¹) →
        (∃ u ∈ K, orderOf u = 4 ∧ u * (h * z * h⁻¹) = (h * z * h⁻¹) * u) →
          ∃ g : G, g * a = a * g ∧ g * z * g⁻¹ = t

@[expose] def C19_9s2Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      ∀ a ∈ sec19T K z S, (∃ h : G, h * a = a * h ∧ h * z * h⁻¹ ≠ z ∧
          h * z * h⁻¹ * z = z * (h * z * h⁻¹)) →
        ∃ h : G, h * a = a * h ∧ h * z * h⁻¹ ≠ z ∧ h * z * h⁻¹ * z = z * (h * z * h⁻¹) ∧
          ∃ u ∈ K, orderOf u = 4 ∧ u * (h * z * h⁻¹) = (h * z * h⁻¹) * u

@[expose] def C19_9s1Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      ∀ b ∈ sec19T K z S ⊓ centralizerModOdd ⊤ L, b ≠ 1 → ∀ g : G,
        g * z * g⁻¹ * b = b * (g * z * g⁻¹) → ∃ h : G, h * b = b * h ∧
          (h * z * h⁻¹ = g * z * g⁻¹ ∨ h * t * h⁻¹ = g * z * g⁻¹)

@[expose] def C19_11cTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      sec19T K z S ⊓ centralizerModOdd ⊤ L = ⊥

@[expose] def C19_QStarTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      ∀ x ∈ (S : Subgroup G), ∀ J₁ ∈ CoreAssembly.conjClass K, ∀ J₂ ∈ CoreAssembly.conjClass K,
        J₁ ≠ J₂ → x ∈ centralizerModOdd ⊤ J₁ → x ∈ centralizerModOdd ⊤ J₂ →
          x ∈ centralizerModOdd ⊤ K ∧ x ∈ centralizerModOdd ⊤ L

@[expose] def C19_14NoGraphTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W →
        ∀ x ∈ (S : Subgroup G) ⊓ centralizerModOdd ⊤ K, x ∉ sec19X K z →
          Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({z} : Set G) → False

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
