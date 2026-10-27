module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut

set_option linter.unusedSectionVars false

section Residuals

@[expose] def TwoDHighE8 : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup .E8 L p)
    (a : Fin Tag.E8.rank → Lˣ), rootDiagUnit .E8 a ∈ S.E → rootDiagUnit .E8 a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .twoD →
      5 ≤ compRank (componentRoots (rootCharHom a) i) →
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def TwoDHighTranscendental : Prop :=
  ∀ (τ : Tag), (τ = .E6 ∨ τ = .E7) → ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ)
    (S : LangSetup τ L p),
    (∃ (r : ℕ) (_ : Fact r.Prime) (_ : CharP L r),
      letI := ZMod.algebra L r; ¬ Algebra.IsAlgebraic (ZMod r) L) →
    ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.E → rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .twoD →
      5 ≤ compRank (componentRoots (rootCharHom a) i) →
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def TwoDHighE8T : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup .E8 L p)
    (a : Fin Tag.E8.rank → Lˣ), rootDiagUnit .E8 a ∈ S.D.torus → rootDiagUnit .E8 a ^ p = 1 →
    rootDiagUnit .E8 a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .twoD →
      5 ≤ compRank (componentRoots (rootCharHom a) i) →
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def TwoDHighTranscendentalT : Prop :=
  ∀ (τ : Tag), (τ = .E6 ∨ τ = .E7) → ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ)
    (S : LangSetup τ L p),
    (∃ (r : ℕ) (_ : Fact r.Prime) (_ : CharP L r),
      letI := ZMod.algebra L r; ¬ Algebra.IsAlgebraic (ZMod r) L) →
    ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ^ p = 1 →
    rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .twoD →
      5 ≤ compRank (componentRoots (rootCharHom a) i) →
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem twoDHighE8_of_T (h : TwoDHighE8T) : TwoDHighE8 :=
  fun L _ _ p S a hE ha1 i hk h5 hbig =>
    h L p S a (S.E_le hE).1 (S.E_exp _ hE) ha1 i hk h5 hbig

theorem twoDHighTranscendental_of_T (h : TwoDHighTranscendentalT) : TwoDHighTranscendental :=
  fun τ hτ L _ _ p S hL a hE ha1 i hk h5 hbig =>
    h τ hτ L p S hL a (S.E_le hE).1 (S.E_exp _ hE) ha1 i hk h5 hbig

end Residuals

theorem twoDHighComponentsT_proved : TwoDHighComponentsT := by
  intro τ L _ _ p S a hTa _ _ i hkind h5 _
  have hr := le_trans h5 (compRank_le (componentRoots (rootCharHom a) i))
  have hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    cases τ <;> simp_all [Tag.rank]
  exact S.isQuasisimple_rationalComponent_twoDT (Or.inr hτ) hTa i hkind h5

theorem twoDHighComponents_proved : TwoDHighComponents :=
  twoDHighComponents_of_T twoDHighComponentsT_proved

theorem twoDHighE8T_proved : TwoDHighE8T :=
  fun _ _ _ _ S _ hTa _ _ i hkind h5 _ =>
    S.isQuasisimple_rationalComponent_twoDT (Or.inr (Or.inr (Or.inr rfl))) hTa i hkind h5

theorem twoDHighTranscendentalT_proved : TwoDHighTranscendentalT :=
  fun _ hτ _ _ _ _ S _ _ hTa _ _ i hkind h5 _ =>
    S.isQuasisimple_rationalComponent_twoDT (Or.inr (Or.imp_right Or.inl hτ)) hTa i hkind h5

theorem twoDHighComponents_of (_h8 : TwoDHighE8) (_hT : TwoDHighTranscendental) :
    TwoDHighComponents :=
  twoDHighComponents_proved

theorem twoDHighComponentsT_of (_h8 : TwoDHighE8T) (_hT : TwoDHighTranscendentalT) :
    TwoDHighComponentsT :=
  twoDHighComponentsT_proved

end CFSG.HardMathSupport.Timmesfeld.LangTorus
