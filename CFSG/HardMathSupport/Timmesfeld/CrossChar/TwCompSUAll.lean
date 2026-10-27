module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUG2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorusDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem suN_rank_ncard {τ : Tag} {L : Type} [Field L] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {i : KernelComponent χ}
    (h : twistKind ρ χ i = .suN) :
    2 ≤ compRank (componentRoots χ i) ∧ (componentRoots χ i).ncard =
      compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1) := by
  unfold twistKind at h
  split_ifs at h with h1 h2 h3 h4
  exact h4

theorem exists_frame_of_typeA_tag_T_of_prime (hG2 : G2LongA2Frame) {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ) (κ : ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) ∧
        componentRoots (rootCharHom a) i = frameRoots σ := by
  cases τ with
  | G2 => exact exists_frame_of_typeA_G2_T_of_prime hG2 S hp hpL hTp i h2 hn
  | F4 => exact exists_frame_of_typeA_F4_T_of_prime S hp hpL hTp i h2 hn
  | D4 =>
    obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨ⟩ := exists_frame_of_typeA_D4_T_of_prime S hp hpL hTp i h2 hn
    exact ⟨ν, ψ, σ, 1, hν, hψ, one_ne_zero, hnorm, hΨ⟩
  | E6 =>
    obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨ⟩ := exists_frame_of_typeA_E6_T_of_prime S hp hpL hTp i h2 hn
    exact ⟨ν, ψ, σ, 1, hν, hψ, one_ne_zero, hnorm, hΨ⟩
  | E7 =>
    obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨ⟩ := exists_frame_of_typeA_E7_T_of_prime S hp hpL hTp i h2 hn
    exact ⟨ν, ψ, σ, 1, hν, hψ, one_ne_zero, hnorm, hΨ⟩
  | E8 =>
    obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨ⟩ := exists_frame_of_typeA_E8_T_of_prime S hp hpL hTp i h2 hn
    exact ⟨ν, ψ, σ, 1, hν, hψ, one_ne_zero, hnorm, hΨ⟩

theorem exists_frame_of_typeA_tag_T (hG2 : G2LongA2Frame) {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ) (κ : ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) ∧
        componentRoots (rootCharHom a) i = frameRoots σ :=
  exists_frame_of_typeA_tag_T_of_prime hG2 S S.hp S.natCast_ne_zero hTp i h2 hn

theorem langComponentsQuasisimpleT_suN (hG2 : G2LongA2Frame) :
    LangComponentsQuasisimpleT .suN := by
  intro τ L _ _ p S a hT hTp _ i hkind hbig
  obtain ⟨h2, hn⟩ := suN_rank_ncard hkind
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T hG2 S hTp i h2 hn
  exact rationalComponent_quasisimple_suN_of_frame_T S hT i hkind hbig hν hψ hκ hnorm hΨ

theorem langComponentsQuasisimple_suN (hG2 : G2LongA2Frame) : LangComponentsQuasisimple .suN :=
  langComponentsQuasisimple_of_T (langComponentsQuasisimpleT_suN hG2)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
