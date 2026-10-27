module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

abbrev L3U3 (X : Type) [Group X] : Prop :=
  catalogIs X CFSG.LocalAnalysis.GLTheoremA.l3u3Index

@[expose] def L3U3Pumpup (S : Type) [Group S] (β : MulAut S) : Prop :=
  β ^ 3 = 1 ∧ β ≠ 1 ∧ ∃ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J ∧ L3U3 (PQuot 3 J)

@[expose] def NoL3U3Layer {P : Type} [Group P] (ψ : MulAut P) : Prop :=
  ∀ A : Subgroup P, GLAPComponent 3 (fixSubgroup ψ) A → ¬ L3U3 (PQuot 3 A)

@[expose] def L3U3Order (N : ℕ) : Prop :=
  ∃ n : ℕ, ((n % 6 = 2 ∨ n % 6 = 4) ∧
      3 * N = 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1))) ∨
    ((n % 6 = 1 ∨ n % 6 = 5) ∧ 1 < n ∧
      3 * N = 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)))

structure L3U3Facts : Prop where
  order : ∀ (X : Type) [Group X] [Finite X], L3U3 X → L3U3Order (Nat.card X)
  elem9 : ∀ (X : Type) [Group X] [Finite X], L3U3 X →
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9

section Residual


@[expose] def Char2L3U3 (τ : Tag) (k : TwistKind) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      twistKind S.ρ (rootCharHom a) i = k →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      L3U3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      ∃ z : ModGL τ L, z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        (∀ g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, g * z = z * g) ∧
        z ^ 3 = 1 ∧ z ≠ 1

end Residual

@[expose] def I1419ExcS : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 2 S → ¬ catalogIs S CFSG.LocalAnalysis.GLTheoremA.K1419.I1419Classical2 →
    ∀ (labK : GLALabel) (β : MulAut S),
      CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labK β → ¬ L3U3Pumpup S β

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
