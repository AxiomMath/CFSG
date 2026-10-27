module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodA2Two
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyClassTriQuad
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Lattice Polynomial
  CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

set_option linter.unusedSectionVars false


section E8Two

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem prime_eq_seven_of_order_three (hp : p.Prime) (hq : ((2 : ℕ) : ZMod p) ≠ 0 ∨ True)
    (he : orderOf (((2 : ℕ)) : ZMod p) = 3) : p = 7 := by
  have h8 : ((2 : ℕ) : ZMod p) ^ 3 = 1 := by
    rw [← he]; exact pow_orderOf_eq_one _
  have h7 : ((7 : ℕ) : ZMod p) = 0 := by
    push_cast at h8 ⊢
    linear_combination h8
  have hd : p ∣ 7 := (ZMod.natCast_eq_zero_iff 7 p).1 h7
  exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd

theorem setupRigid_E8_three_two (S : LangSetup .E8 L p) (hAlg : S.IsAlgebraic)
    (hq : S.D.q = 2) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 3)
    (hC : S.IsWeylClass (wordMat Tag.E8 e8ThreeWord)) : SetupRigid S := by
  have hp7 : p = 7 := by
    rw [hq] at he
    exact prime_eq_seven_of_order_three S.hp (Or.inr trivial) he
  obtain ⟨Fr, hFr, hΦ, w, hn, hw, hMΓ⟩ := hC
  set M := wordMat Tag.E8 e8ThreeWord with hM
  have hρ : ∀ γ, IsRoot Tag.E8 γ → S.ρ γ = M *ᵥ γ := fun γ hγ => by
    rw [S.rho_eq_smul_of_frob hFr hΦ hn hγ, hw]
  have hρroot : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (S.ρ γ) := fun γ hγ => by
    rw [S.rho_eq_smul_of_frob hFr hΦ hn hγ]
    exact IsRoot.smul hγ w
  have hMM := e8ThreeMat_rel
  have hM3 : M * M * M = 1 := by
    calc M * M * M = (-M - 1) * M := by rw [hMM]
      _ = -(M * M) - M := by noncomm_ring
      _ = -(-M - 1) - M := by rw [hMM]
      _ = 1 := by noncomm_ring
  have hsl := symmetrizer_diag_one (τ := Tag.E8) (Or.inr (Or.inr rfl))
  have hgood : ∀ β, IsRoot Tag.E8 β → IsGoodRoot S β := by
    intro β hβ
    have hβ' := hρroot β hβ
    have h2 : S.ρ (S.ρ β) = -(β + S.ρ β) := by
      rw [hρ _ hβ', hρ _ hβ, Matrix.mulVec_mulVec, hMM, Matrix.sub_mulVec, Matrix.neg_mulVec,
        Matrix.one_mulVec]
      abel
    have h3 : S.ρ (-(β + S.ρ β)) = β := by
      calc S.ρ (-(β + S.ρ β)) = S.ρ (S.ρ (S.ρ β)) := by rw [h2]
        _ = M *ᵥ (M *ᵥ (M *ᵥ β)) := by rw [hρ _ (hρroot _ hβ'), hρ _ hβ', hρ _ hβ]
        _ = (M * M * M) *ᵥ β := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        _ = β := by rw [hM3, Matrix.one_mulVec]
    have hab : iform β (S.ρ β) = -1 := by
      have e1 : iform (S.ρ β) (S.ρ (S.ρ β)) = iform β (S.ρ β) := by
        rw [S.rho_eq_smul_of_frob hFr hΦ hn hβ', S.rho_eq_smul_of_frob hFr hΦ hn hβ]
        exact iform_smul w β _
      have e2 : iform (S.ρ β) (S.ρ (S.ρ β)) = -iform β (S.ρ β) - 2 := by
        rw [h2, SimplyLacedCover.iform_neg_right, iform_add_right,
          SimplyLacedCover.iform_self_eq_two hsl hβ', iform_comm (S.ρ β) β]
        ring
      omega
    exact isGoodRoot_of_A2orbit_two S (Or.inr (Or.inr rfl)) hq hp7 hβ hβ' hab h2 h3
  have hgen : GoodRootsGenerate S := fun γ hγ => ReflClosure.base (hgood γ hγ)
  refine setupRigid_E8 S (by omega) hAlg ?_ ?_
  · intro D₁ hD₁E hc
    exact noFrobeniusInner_of_goodRootsGenerate S hgen hD₁E hc
  · intro D₁ hD₁E hc
    exact centralizerTrivial_of_goodRoots S hgen hD₁E hc

end E8Two

end CFSG.HardMathSupport.Timmesfeld.LangTorus
