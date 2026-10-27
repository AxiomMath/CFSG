module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal9

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type} [Group H] [Finite H] {R M V : Subgroup H}

theorem solvable_reduced_action_produces_A3_family
    (hchar : CharTwo (⊤ : Subgroup H)) (hsylow : IsSylowTwoOf R (⊤ : Subgroup H))
    (hnonnormal : ¬ R.Normal) (hRM : R ≤ M) (hMlt : M < ⊤)
    (hmax : ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M) (hnoChar : NoCharNormal R ⊤)
    (hV : IsTwoReducedIn (⊤ : Subgroup H) V)
    (hVH : ¬ (⊤ : Subgroup H) ≤ Subgroup.centralizer (V : Set H))
    (hsolv : Group.IsSolvable ↥(autOn (⊤ : Subgroup H) V)) :
    ∃ (r : ℕ) (I : Fin r → Subgroup H) (W F : Subgroup H)
      (Pm : Subgroup (Equiv.Perm (Fin r))) (hw : WreathHyp R M V W F I Pm)
      (K : Fin r → Subgroup H),
      (∃ k : ℕ, r = 2 ^ k) ∧ ⁅V, oddOrderSubgroup (⊤ : Subgroup H)⁆ = W ∧
        F = V ⊓ Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H) ∧
        A3FamilyConclusion hw K := by
  have g : GateHyp R M V :=
    GateHyp.of_noChar hsylow hnonnormal hRM hMlt hmax hnoChar hV hVH hsolv
  have := g.V_normal
  obtain ⟨Wm, _, _, _, θ, -, -⟩ := Layer.exists_binModel g.V_elem g.reduced.2.1
  obtain ⟨r, I, W, F, Pm, hpow, hw⟩ := g.exists_wreathHyp_model θ
  obtain ⟨K, hK⟩ := A3_family_exists hw hchar hnoChar
  obtain ⟨t, hTC⟩ := internal_S3_wreath_transfer hw
  exact ⟨r, I, W, F, Pm, hw, K, hpow, hTC.W_eq, hTC.F_eq, hK⟩

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
