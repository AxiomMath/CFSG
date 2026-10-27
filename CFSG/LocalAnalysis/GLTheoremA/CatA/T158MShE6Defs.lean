module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)

section Defs


@[expose] def E6ShapeSetup {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) : Prop :=
  ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧
    ((S.D.Φ = Units.map (entrywiseHom Fr) ∧ 3 ∣ S.D.q - 1) ∨
      (S.D.Φ = twistHom TwistTag.E6 L Fr ∧ 3 ∣ S.D.q + 1))

@[expose] def T158E6LangData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (hP : PreSetup 3 L J A d b),
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧ (i = .E6 q ∨ i = .twistedE6 q)) →
    ∃ (Lf : Type) (_ : Field Lf) (_ : IsAlgClosed Lf) (_ : CharP Lf 2) (S : LangSetup Tag.E6 Lf 5)
      (a : Fin Tag.E6.rank → Lfˣ) (i : KernelComponent (rootCharHom a)) (y : ModGL Tag.E6 Lf)
      (hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
      E6ShapeSetup S ∧ rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      y ∈ toralCentralizer Tag.E6 Lf a ∧ S.D.step y = y ∧
      Nonempty (PSimple 3 J ≃* (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) ∧
      (centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i) ⟨MulAut.conj y, hyStab⟩) ∈
          innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
        MI.indAut 3 J b hP.b_norm ∈ innAutDerived (PSimple 3 J)) ∧
      ((∀ j, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) j) →
          rationalComponent S.ρ S.Γ (rootCharHom a) j = rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
          GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J) ∧
      (rootDiagUnit Tag.E6 a ∉ S.Γ → ¬ InducesInnerMod 3 L d)

@[expose] def T158E6ModelData {G : Type} [Group G] (L J A : Subgroup G) (d b : G) : Prop :=
  ∃ (C : Type) (_ : Group C) (_ : Finite C) (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) (β φ : MulAut C)
    (Lf : Type) (_ : Field Lf) (_ : IsAlgClosed Lf) (_ : CharP Lf 2) (S : LangSetup Tag.E6 Lf 5)
    (a : Fin Tag.E6.rank → Lfˣ) (ι : C →* ModGL Tag.E6 Lf) (y : ModGL Tag.E6 Lf),
    Subgroup.center C = ⊥ ∧
    CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) β ∧
    CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ ∧
    E6ShapeSetup S ∧ rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
    Function.Injective ι ∧ ι.range = S.Γ ∧
    (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
    (∀ c, ι (φ c) = y * ι c * y⁻¹) ∧
    y ∈ toralCentralizer Tag.E6 Lf a ∧ S.D.step y = y ∧
    (rootDiagUnit Tag.E6 a ∉ S.Γ → β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner C)

@[expose] def T158E6ModelOf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G), PreSetup 3 L J A d b →
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧ (i = .E6 q ∨ i = .twistedE6 q)) →
    T158E6ModelData L J A d b

@[expose] def E6ShortOrbit : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ), rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    rootDiagUnit Tag.E6 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    ∀ y ∈ toralCentralizer Tag.E6 L a, S.D.step y = y →
    MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    y ∉ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) →
    ((kernelRoots (rootCharHom a)).ncard = 18 ∧
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3) ∨
      (kernelRoots (rootCharHom a)).ncard = 24

@[expose] def E6D4T2CosetAction : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    E6ShapeSetup S → ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    (kernelRoots (rootCharHom a)).ncard = 24 → ∀ i : KernelComponent (rootCharHom a),
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    ∀ y ∈ toralCentralizer Tag.E6 L a, S.D.step y = y →
    ∀ hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i),
    y ∉ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) →
    catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        (onLie fun | .trialityD4 _ => True | _ => False) ∨
      centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i) ⟨MulAut.conj y, hyStab⟩) ∈
        innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

@[expose] def E6OrbitThreeUnique : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ), rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    (kernelRoots (rootCharHom a)).ncard = 18 → ∀ i : KernelComponent (rootCharHom a),
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 →
    ∀ j, rationalComponent S.ρ S.Γ (rootCharHom a) j = rationalComponent S.ρ S.Γ (rootCharHom a) i

@[expose] def E6A2OrbitThreeOuter : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    E6ShapeSetup S → ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    (kernelRoots (rootCharHom a)).ncard = 18 → ∀ i : KernelComponent (rootCharHom a),
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 → rootDiagUnit Tag.E6 a ∉ S.Γ

end Defs

@[expose] def D4InnAutDerivedNotFG : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X J : Subgroup G) (b : G),
    GLAPComponent 3 X J →
    catalogIs (PSimple 3 J) (onLie fun i => ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) →
    b ^ 3 = 1 → ∀ hb : b ∈ Subgroup.normalizer (J : Set G),
    MI.indAut 3 J b hb ∈ innAutDerived (PSimple 3 J) → ¬ FGOn 3 b J

end CFSG.LocalAnalysis.GLTheoremA.T158

end
