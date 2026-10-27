module

import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut

set_option linter.unusedSectionVars false

theorem rootDiagUnit_pow_eq_one_of_forall {τ : Tag} {L : Type} [Field L] {p : ℕ}
    {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1) : rootDiagUnit τ a ^ p = 1 := by
  have key : ∀ n : ℕ, rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]
  rw [key p, show a ^ p = 1 from funext fun i => by simpa using hap i, rootDiagUnit_one]

section Kinds

section OuterKinds

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem langSetup_tame_exc (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .exc) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  excQuasisimpleAtT_of twistedE6TrialityComponents_provedT τ L p S a hT hTp h1 i hk

theorem langSetup_tame_suN (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .suN) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨h2, hn⟩ := suN_rank_ncard hk
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T g2LongA2Frame_proved S hTp i h2 hn
  exact rationalComponent_suN_tame_of_frame_T S hT i hk hν hψ hκ hnorm hΨ

theorem langSetup_tame_twoD (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · have hr := le_trans h5 (compRank_le_rank (componentRoots (rootCharHom a) i))
    have hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
      cases τ <;> simp_all [Tag.rank]
    exact S.isQuasisimple_rationalComponent_twoDT (Or.inr hτ) hT i hk h5
  · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hcard, hr]
    exact isQuasisimple_rationalComponent_rank_four_T e6FixDNAll_proved S hT hTp h1 i hr hc hnin

end OuterKinds

section Inner

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
  (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}

theorem langSetup_tame_inner (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  · exact Or.inl (rationalComponent_quasisimple_inner_of_four_leT S rootAutIsWeyl_holds hT i hk hQ)
  · have hp5 : 5 ≤ p := by
      rcases S.hq with h | h
      · exact h
      · exfalso
        apply hQ
        obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
        exact h.trans (Nat.le_self_pow hs0.ne' _)
    exact rationalComponent_inner_small_tame S rootAutIsWeyl_holds hT hTp h1 i hk hp5
      (not_le.1 hQ)

end Inner

end Kinds

section Main

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem langSetup_tame (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner => exact langSetup_tame_inner S hT hTp h1 i hk
  | suN => exact langSetup_tame_suN S hT hTp i hk
  | twoD => exact Or.inl (langSetup_tame_twoD S hT hTp h1 i hk)
  | exc => exact Or.inl (langSetup_tame_exc S hT hTp h1 i hk)

theorem langSetup_hTame (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) :
    ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  fun i => langSetup_tame S hT hap h1 i

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
