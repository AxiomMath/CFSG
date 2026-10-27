module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzAssump
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

structure FzbStruct {G : Type} [Group G] (t : G) (S : Subgroup G) (x₁ x₂ lam rho tau : G)
    (T₂ P : Subgroup G) (q s : G) : Prop where
  isPGroup : IsPGroup 2 T₂
  card_T₂ : Nat.card T₂ = 2 ^ 10
  S_le : S ≤ T₂
  P_le : P ≤ T₂
  P_norm : ∀ g ∈ T₂, ∀ p ∈ P, g * p * g⁻¹ ∈ P
  card_P : Nat.card P = 64
  P_iso : Nonempty (↥P ≃* SylSL3_4)
  E_le_P : baseGrp x₁ x₂ ≤ P
  rho_norm : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P
  rho_fpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1
  cent_t : P ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂
  q_gen : zpowers q = twoCore t
  s_cases : s = tau ∨ s = q * tau
  s_comm_P : ∀ p ∈ P, ⁅s, p⁆ ∈ fourGrp x₁ x₂
  gen : T₂ = P ⊔ closure {q, s, lam}

@[expose] def FzbStructProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho tau : G), ¬ 2 ^ 11 ∣ Nat.card G → FzAssumptionII G →
    Ctx t L S x₁ x₂ lam rho tau → Nat.card (twoCore t) = 4 →
    ∃ (T₂ P : Subgroup G) (q s : G), FzbStruct t S x₁ x₂ lam rho tau T₂ P q s

end CFSG.OddStandard.SmallF3.FritzII
