module

public import CFSG.GH74.Generic.S1.Props
public import CFSG.GH74.Generic.S1.SymKey
public import CFSG.GH74.Generic.S45.PumpC1
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.Assembly.LowTwoRank

@[expose] def IsSL4ModelAt (K : Type) [Group K] (ε : ℤ) (q : ℕ) : Prop :=
  (ε = 1 ∧ q % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (K ≃* StatedSL 4 F)) ∨
  (ε = -1 ∧ q % 4 = 1 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧
      Nonempty (K ≃* StatedSU 4 q F))

@[expose] def S1LayerNoPrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (ε : ℤ) (q : ℕ), IsSL4ModelAt ↥K ε q → 5 ≤ q →
      ∀ (c : G) (hc : c ∈ centralizer ({x} : Set G)), orderOf c = 2 →
        (⟨c, hc⟩ : ↥(centralizer ({x} : Set G))) ∈ liftL x K →
        barOf hc ≠ xbar x →
        ¬ layer (CentralizerBar c) ≤ S45.barSub c (resCent ({x, c} : Set G)) →
        ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ q ^ 2 + 1 → ¬ r ∣ Nat.card ↥(layer (CentralizerBar c))

end CFSG.GH74.Generic.S1.Exo
