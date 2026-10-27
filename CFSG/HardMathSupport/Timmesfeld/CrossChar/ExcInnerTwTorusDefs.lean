module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwAnyKind

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def LangSubnormalT : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ^ p = 1 →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
          S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        ((rationalComponent S.ρ S.Γ (rootCharHom a) i).subgroupOf
          (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})).IsSubnormal

@[expose] def LangComponentsQuasisimpleT (k : TwistKind) : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ^ p = 1 →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      twistKind S.ρ (rootCharHom a) i = k →
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def AnyKindCommuteT : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p), τ ≠ .G2 →
    ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ^ p = 1 →
    ∀ i : KernelComponent (rootCharHom a),
      3 ≤ S.D.q → 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) →
      ∀ z : ModGL τ L, (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) →
        ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g

theorem mem_torus_pow_of_mem_E {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p)
    {x : ModGL τ L} (hx : x ∈ S.E) : x ∈ S.D.torus ∧ x ^ p = 1 :=
  ⟨(S.E_le hx).1, S.E_exp x hx⟩

theorem langComponentsQuasisimple_of_T {k : TwistKind} (h : LangComponentsQuasisimpleT k) :
    LangComponentsQuasisimple k := fun τ L _ _ p S a hE ha1 i hk hbig =>
  h τ L p S a (mem_torus_pow_of_mem_E S hE).1 (mem_torus_pow_of_mem_E S hE).2 ha1 i hk hbig

theorem anyKindCommute_of_T (h : AnyKindCommuteT) : AnyKindCommute :=
  fun τ L _ _ p S hτ a hE i hq3 hQ4 z hz =>
    h τ L p S hτ a (mem_torus_pow_of_mem_E S hE).1 (mem_torus_pow_of_mem_E S hE).2 i hq3 hQ4 z hz

end CFSG.HardMathSupport.Timmesfeld.CrossChar
