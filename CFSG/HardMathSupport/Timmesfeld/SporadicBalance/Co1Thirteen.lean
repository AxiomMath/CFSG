module

public import Certificates.Certificate16956
public import CFSG.Assembly.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Thirteen

@[expose] def NoEvenNormalizer {K : Type*} [Group K] (x : K) : Prop :=
  ∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ z ∈ Subgroup.centralizer ({x} : Set K),
    orderOf z = 3 → g * z * g⁻¹ ∈ Subgroup.zpowers z → g ^ 39 = 1

theorem co1_thirteen_facts
    (x : CFSG.Blueprint.NativeSporadic.Co1) (hx : orderOf x = 13) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) = 156 ∧
      NoEvenNormalizer x :=
  Certificates.certificate16956 x hx

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Thirteen
