module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

@[expose] def FinCellB (Y : Type) [Group Y] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X U I Q : Subgroup (MulAut Y)), IsPGroup p ↥X →
    IVK.IsFourSubgroup U → IVK.IsFourSubgroup Q → Q ≤ I → U ⊓ Q = ⊥ → ⁅I, I⁆ = I →
    I ≤ centralizer (U : Set (MulAut Y)) → U ≤ normalizer (X : Set (MulAut Y)) →
    I ≤ normalizer (X : Set (MulAut Y)) → ∀ b ∈ X, orderOf b = p → HHObs p Y b

@[expose] def FinCellA (Y : Type) [Group Y] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X I : Subgroup (MulAut Y)), IsPGroup p ↥X → X ≠ ⊥ →
    I ≠ ⊥ → ⁅I, I⁆ = I → I ≤ normalizer (X : Set (MulAut Y)) → False

@[expose] def ResB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55E G z k S T Tstar p H P g X Y →
    ∀ (t : G) (q : ℕ) (I Q₁ : Subgroup G), Data5A2 z k S T Tstar p H P t q I Q₁ →
    ∀ J : Subgroup (HBar H), BridgeB k p H P g J →
      barIn H I ≤ centralizer (J : Set (HBar H)) → False

theorem FinCellA.finCellB {Y : Type} [Group Y] (h : FinCellA Y) : FinCellB Y := by
  intro p hp hp2 X U I Q hX _ hQ hQI _ hI _ _ hIX b hb hbp
  exfalso
  refine h p hp hp2 X I hX ?_ ?_ hI hIX
  · intro hbot
    rw [hbot, mem_bot] at hb
    rw [hb, orderOf_one] at hbp
    exact hp.one_lt.ne hbp
  · intro hbot
    have hQ1 : Q = ⊥ := le_bot_iff.mp (hbot ▸ hQI)
    have h4 := hQ.2
    rw [hQ1, card_bot] at h4
    omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
