module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResF
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResJ
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FinalBase

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

@[expose] def DiagSolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55E G z k S T Tstar p H P g X Y →
    ∀ (t : G) (q : ℕ) (I Q₁ : Subgroup G), Data5A2 z k S T Tstar p H P t q I Q₁ →
    ∀ w : G, (w = z ∨ w = t) → ∀ W : Subgroup (HBar H),
      W ≤ centralizer (barIn H (zpowers w) : Set (HBar H)) →
      W ≤ centralizer (barIn H I : Set (HBar H)) → Group.IsSolvable ↥W

@[expose] def DiagSwap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55E G z k S T Tstar p H P g X Y →
    ∀ (t : G) (q : ℕ) (I Q₁ : Subgroup G), Data5A2 z k S T Tstar p H P t q I Q₁ →
    ∀ w : G, (w = z ∨ w = t) → ∀ y : G, y ∈ H → orderOf y = 2 → IsConj z y →
      y * w = w * y → y ≠ w →
      barIn H (zpowers y) ≤ centralizer (barIn H I : Set (HBar H)) → ¬ IsConj z (y * w)

theorem resB_of_diag (hS : DiagSolv) (hW : DiagSwap) : ResB := by
  intro G _ _ z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hIJ
  have hL31 : Lemma31Narrow := final_hL31
  have hJ : IsComponent J := by
    obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', -, -, hL⟩ := hB
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hJ, _⟩ := hL
    exact hJ
  have hDS : ∀ {w : G}, (w = z ∨ w = t) → ∀ {W : Subgroup (HBar H)},
      W ≤ centralizer (barIn H (zpowers w) : Set (HBar H)) →
      W ≤ centralizer (barIn H I : Set (HBar H)) → Group.IsSolvable ↥W :=
    fun hw _ hWw hWI => hS G z k S T Tstar p H P g X Y h t q I Q₁ hd _ hw _ hWw hWI
  have hDW : ∀ {w : G}, (w = z ∨ w = t) → ∀ {y : G}, y ∈ H → orderOf y = 2 → IsConj z y →
      y * w = w * y → y ≠ w →
      barIn H (zpowers y) ≤ centralizer (barIn H I : Set (HBar H)) → ¬ IsConj z (y * w) :=
    fun hw _ hyH hy2 hyz hyw hne hyI =>
      hW G z k S T Tstar p H P g X Y h t q I Q₁ hd _ hw _ hyH hy2 hyz hyw hne hyI
  rcases quot_type hL31 h hd hJ hIJ with hA7 | hL2
  · exact false_of_resB_a7 hL31 h hd hB hIJ hDS hDW hA7
  · exact false_of_resB_l2 hL31 h hd hB hIJ hDS hL2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
