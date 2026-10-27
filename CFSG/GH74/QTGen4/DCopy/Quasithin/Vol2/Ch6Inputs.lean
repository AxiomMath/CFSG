module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.E2Seventeen
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

@[expose] def StmtKuM22_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M H P : Subgroup G) (z : G), IsSimpleGroup G →
    quasithinIsSylowTwo T → T ≤ M → T ≤ H →

    IsElemAbelian 2 (pCoreOf 2 M) → Nat.card (pCoreOf 2 M) = 16 →
    M = Subgroup.normalizer (pCoreOf 2 M : Set G) →
    M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) = pCoreOf 2 M →
    (∃ φ : ↥M →* Equiv.Perm (Fin 5), Function.Surjective φ ∧ φ.ker = (pCoreOf 2 M).subgroupOf M) →
    IsNatModCh5 (oTwoUpper M) (pCoreOf 2 M) 2 →

    P ≤ H → H ≤ Subgroup.normalizer (P : Set G) → E2.IsExtraspecialPlus 2 P →
    (∃ φ : ↥H →* Equiv.Perm (Fin 3) × Multiplicative (ZMod 2), Function.Surjective φ ∧
      φ.ker = P.subgroupOf H) →
    H ⊓ Subgroup.centralizer (P : Set G) ≤ P →
    P ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers z →
    (∃ X : Subgroup G, IsSylowIn 3 X H ∧
      P ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z) →
    H = Subgroup.centralizer ({z} : Set G) →

    (∃ d : G, d⁻¹ * z * d ∈ P ∧ d⁻¹ * z * d ≠ z ∧
      IsElemAbelian 2 (P ⊓ CFSG.Quasithin.conjSubgroup P d) ∧
      Nat.card ↥(P ⊓ CFSG.Quasithin.conjSubgroup P d) = 4) →
    Nonempty (G ≃* NativeSporadic.M22)

end CFSG.Quasithin.H13
