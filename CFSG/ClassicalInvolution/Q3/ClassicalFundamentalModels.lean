module

public import CFSG.ClassicalInvolution.Q3.Quasisimple
public import CFSG.ClassicalInvolution.Q3.ClassicalFundamental

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def ClassicalMembersFundamental3 : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) (hp : Nat.Prime 3), IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
    ∀ (L : Subgroup (modelUniv t n 3 1 hp).K) (z : (modelUniv t n 3 1 hp).K),
      IsClassicalMember3 L z → classicalInvolutionOddCore L = ⊥ →
        L ∈ fundamentalSubgroups t (modelUniv t n 3 1 hp).D

@[expose] def ModelFiniteCenterTwoGroup3 : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) (hp : Nat.Prime 3), IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
    Finite (modelUniv t n 3 1 hp).K ∧ IsPGroup 2 (Subgroup.center (modelUniv t n 3 1 hp).K)

@[expose] def ModelOddCentralizerFree3 : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) (hp : Nat.Prime 3), IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n 3 1 hp).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ →
      ∀ x : X, orderOf x = 2 → CFSG.Assembly.Dichotomy.involutionOddCore x = ⊥

theorem classicalIsFundamental3_of_models (h1 : ClassicalMembersFundamental3)
    (h2 : ModelFiniteCenterTwoGroup3) (h3 : ModelOddCentralizerFree3) :
    ClassicalIsFundamental3 := by
  intro t n hp hFT hadm X _ _ ψ hψ hker L z hL
  obtain ⟨hfin, hZ2⟩ := h2 t n hp hFT hadm
  have hO : classicalInvolutionOddCore L = ⊥ :=
    hL.oddCore_eq_bot_of_centralizer (h3 t n hp hFT hadm X ψ hψ hker z hL.orderOf_eq_two)
  obtain ⟨L', z', hL', hmap, -, hO'⟩ := hL.exists_lift ψ hψ hker (hZ2.to_le hker) hO
  refine ⟨⟨L', h1 t n hp hFT hadm L' z' hL' hO', hmap.symm⟩, ?_⟩
  obtain ⟨e⟩ := hL.nonempty_equiv_sl2 hO
  rw [Nat.card_congr e.toEquiv, natCard_sl2Three]

end CFSG.ClassicalInvolution.Q3
