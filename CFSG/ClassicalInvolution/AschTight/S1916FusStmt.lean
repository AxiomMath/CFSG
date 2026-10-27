module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_16InvTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → p ^ f ≠ 9 →
      ¬ (S : Subgroup G) ≤ sec19X K z ⊔ centralizerModOdd ⊤ K →
        ∃ a ∈ (S : Subgroup G), a * a = 1 ∧ a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K

@[expose] def C19_16FusTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → p ^ f ≠ 9 →
      ∀ a ∈ (S : Subgroup G), a * a = 1 → a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K →
        ∀ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) →
          ∃ c ∈ Subgroup.centralizer ({a} : Set G), c * z * c⁻¹ = g * z * g⁻¹

@[expose] def C19_16Fus9Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → p ^ f = 9 →
      ∀ a ∈ (S : Subgroup G), a * a = 1 → a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K →
        ∀ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) →
          ∃ c ∈ Subgroup.centralizer ({a} : Set G), c * z * c⁻¹ = g * z * g⁻¹

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
