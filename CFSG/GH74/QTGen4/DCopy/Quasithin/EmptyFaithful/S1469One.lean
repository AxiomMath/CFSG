module

public import CFSG.Quasithin.EmptyFaithful.S1469One
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M : Subgroup G}

open CFSG.LieType.BorelTits in

@[expose] def Stage14610FiveW_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      2 ^ 11 < Nat.card T →
      4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) →
      ∀ I₂ : Subgroup G, T ⊓ I ≤ I₂ → I₂ ≤ H → Nonempty (OTwoQuot I₂ ≃* Equiv.Perm (Fin 3)) →
        I = (lI T M I ⊔ (T ⊓ I)) ⊔ I₂ →
        (T ⊓ I = tU T u → I ≤ Subgroup.centralizer ({u} : Set G)) →
          Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3

theorem stage14610Five_of_W_F4 (h : Stage14610FiveW_F4) : Stage14610Five_F4 := by
  intro G _ _ T M H u S hH hu I hIs hindex hrank I₂ hI₂ hI₂H hS3 hIeq hcent
  exact h G T M H u S hH hu I hIs (S.two_pow_eleven_lt_card hH hindex hrank) hrank I₂ hI₂ hI₂H hS3
    hIeq hcent

end CFSG.Quasithin
