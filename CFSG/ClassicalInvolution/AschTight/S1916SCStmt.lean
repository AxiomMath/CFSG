module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_14SCTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W →
        ∀ x ∈ (S : Subgroup G) ⊓ sec19X K z, ∀ g : G, g * x * g⁻¹ ∈ (S : Subgroup G) →
          g * x * g⁻¹ ∈ sec19X K z

@[expose] def C19_14ZTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W →
        ∀ g : G, g * z * g⁻¹ ∈ (S : Subgroup G) → g * z * g⁻¹ ∈ sec19X K z

@[expose] def C19_14CTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W →
        (S : Subgroup G) ⊓ centralizerModOdd ⊤ K ≤ sec19X K z

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
