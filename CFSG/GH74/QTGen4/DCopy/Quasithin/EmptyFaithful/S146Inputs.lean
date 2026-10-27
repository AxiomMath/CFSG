module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Stage14610Five_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      4 < (pCoreOf 2 H).relIndex T →
      4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) →
      ∀ I₂ : Subgroup G, T ⊓ I ≤ I₂ → I₂ ≤ H → Nonempty (OTwoQuot I₂ ≃* Equiv.Perm (Fin 3)) →
        I = (lI T M I ⊔ (T ⊓ I)) ⊔ I₂ →
        (T ⊓ I = tU T u → I ≤ Subgroup.centralizer ({u} : Set G)) →
          Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3

end CFSG.Quasithin
