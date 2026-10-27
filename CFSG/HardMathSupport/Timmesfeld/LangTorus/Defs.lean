module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar

set_option linter.unusedSectionVars false


@[expose] noncomputable def diagramAt (τ : Tag) (L : Type) [Field L] (t : TwistTag)
    (h : t.tag = τ) : ModGL τ L := h ▸ diagramMap t L

@[expose] def IsSteinbergEnd (τ : Tag) (L : Type) [Field L] (q : ℕ)
    (Φ : ModGL τ L →* ModGL τ L) : Prop :=
  ∃ Fr : L →+* L, (∀ c, Fr c = c ^ q) ∧ ∃ P : ModGL τ L,
    (P = 1 ∨ ∃ (t : TwistTag) (h : t.tag = τ), P = diagramAt τ L t h) ∧
      ∀ g, Φ g = P * Units.map (entrywiseHom Fr) g * P⁻¹

structure LangDatum (τ : Tag) (L : Type) [Field L] where
  Φ : ModGL τ L →* ModGL τ L
  q : ℕ
  n : ModGL τ L
  g0 : ModGL τ L
  steinberg : IsSteinbergEnd τ L q Φ
  n_weyl : ∃ w : WeylGroup τ, n = canonicalRep (coxeterSystem τ) L w
  g0_mem : g0 ∈ adjointGroup τ L
  lang : Φ g0 = g0 * n

namespace LangDatum

variable {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)

@[expose] noncomputable def step : ModGL τ L →* ModGL τ L :=
  (MulAut.conj D.n).toMonoidHom.comp D.Φ

@[expose] noncomputable def model : Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓ D.step.eqLocus (MonoidHom.id _)

@[expose] noncomputable def torus : Subgroup (ModGL τ L) := twistedTorusOf D.n D.Φ

@[expose] noncomputable def Γ : Subgroup (ModGL τ L) := ⁅D.model, D.model⁆

theorem mem_model {y : ModGL τ L} :
    y ∈ D.model ↔ y ∈ adjointGroup τ L ∧ D.n * D.Φ y * D.n⁻¹ = y := Iff.rfl

end LangDatum

structure FrobRootMap {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) : Prop where
  isRoot_iff : ∀ γ, IsRoot τ (ρ γ) ↔ IsRoot τ γ
  neg_eq : ∀ γ, ρ (-γ) = -ρ γ
  iform_eq : ∀ γ δ, CFSG.LieType.Steinberg.Adjoint.iform (ρ γ) (ρ δ) =
    CFSG.LieType.Steinberg.Adjoint.iform γ δ
  map_rootSubgroup : ∀ γ, IsRoot τ γ →
    (rootSubgroup τ L γ).map D.step = rootSubgroup τ L (ρ γ)
  rootChar_eq : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D.torus → ∀ γ, IsRoot τ γ →
    rootChar a (ρ γ) = rootChar a γ ^ D.q

@[expose] def FrobeniusOnRoots : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (D : LangDatum τ L), ∃ ρ : Equiv.Perm (Fin τ.rank → ℤ),
    FrobRootMap D ρ

structure LangSetup (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) where
  D : LangDatum τ L
  ρ : Equiv.Perm (Fin τ.rank → ℤ)
  frob : FrobRootMap D ρ
  E : Subgroup (ModGL τ L)
  hp : p.Prime
  hq : 5 ≤ p ∨ 4 ≤ D.q
  hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0
  hpq : ¬ p ∣ D.q
  finite : Finite D.model
  E_le : E ≤ D.torus ⊓ D.Γ
  E_exp : ∀ x ∈ E, x ^ p = 1
  E_all : ∀ x ∈ D.torus ⊓ D.Γ, x ^ p = 1 → x ∈ E

namespace LangSetup

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

@[expose] noncomputable def Γ : Subgroup (ModGL τ L) := S.D.Γ

end LangSetup

section Rational

variable {τ : Tag} {L : Type} [Field L]

@[expose] def rationalRoots (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ) :
    Set (Fin τ.rank → ℤ) :=
  {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ componentRoots χ i ∧ γ = (ρ : (Fin τ.rank → ℤ) → _)^[k] δ}

@[expose] noncomputable def rationalSpan (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Γ : Subgroup (ModGL τ L)) (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    (i : KernelComponent χ) : Subgroup (ModGL τ L) :=
  rootSpan τ L (rationalRoots ρ χ i) ⊓ Γ

@[expose] noncomputable def rationalComponent (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Γ : Subgroup (ModGL τ L)) (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    (i : KernelComponent χ) : Subgroup (ModGL τ L) :=
  ⁅rationalSpan ρ Γ χ i, rationalSpan ρ Γ χ i⁆

end Rational

inductive TwistKind
  | inner
  | suN
  | twoD
  | exc
  deriving DecidableEq

section Kind

variable {τ : Tag} {L : Type} [Field L]

@[expose] noncomputable def compRank (Ψ : Set (Fin τ.rank → ℤ)) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ))

@[expose] def twistInner (Ψ : Set (Fin τ.rank → ℤ)) (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) :
    Prop :=
  ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}, ∀ γ ∈ Ψ, σ γ = w • γ

@[expose] noncomputable def componentOrbitLength (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) : ℕ :=
  sInf {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}

@[expose] def HasDiagramSymmetryType (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  (2 ≤ compRank Ψ ∧ Ψ.ncard = compRank Ψ * (compRank Ψ + 1)) ∨
    (4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) ∨
    (compRank Ψ = 6 ∧ Ψ.ncard = 72)

open Classical in
@[expose] noncomputable def twistKind (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ) : TwistKind :=
  if twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) then .inner
  else if (compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)])) then .exc
  else if 4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = 2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1)
    then .twoD
  else if 2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1)
    then .suN
  else .inner

@[expose] def RootAutIsWeyl : Prop :=
  ∀ (τ : Tag) (Ψ : Set (Fin τ.rank → ℤ)), IsRootComponent Ψ → ¬ HasDiagramSymmetryType Ψ →
    ∀ σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ), Set.BijOn σ Ψ Ψ →
      (∀ γ ∈ Ψ, ∀ δ ∈ Ψ, CFSG.LieType.Steinberg.Adjoint.iform (σ γ) (σ δ) =
        CFSG.LieType.Steinberg.Adjoint.iform γ δ) → (∀ γ ∈ Ψ, σ (-γ) = -σ γ) →
      twistInner Ψ σ

end Kind

@[expose] def LangSubnormal : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.E → rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a),
      rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
          S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        ((rationalComponent S.ρ S.Γ (rootCharHom a) i).subgroupOf
          (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})).IsSubnormal

@[expose] def LangComponentsQuasisimple (k : TwistKind) : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.E → rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = k →
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def LangGeneration (P : ℕ → Prop) : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p), P p →
    ∀ (D₁ : Subgroup (ModGL τ L)), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
    S.Γ ≤ Subgroup.closure {x | ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ ∧
      rootDiagUnit τ a ≠ 1 ∧ ∃ i : KernelComponent (rootCharHom a),
        ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧
        x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i}

@[expose] def excTag : LieFamily → Tag
  | .E6 | .twistedE6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .F4 => .F4
  | .G2 => .G2
  | .trialityD4 => .D4
  | _ => .G2

@[expose] def LangTorusAt (k : LieFamily) (R : ℕ → ℕ → Prop) : Prop :=
  IsExceptionalFam k → ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ),
    p.Prime → R p q.card → p ≠ q.p →
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup (excTag k) L p),
      S.D.q = q.card ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (CatT ⟨excIndex k q, hv⟩ ≃* S.Γ)

@[expose] def LangTorusAtP (k : LieFamily) (e : ℕ) (R : ℕ → Prop) : Prop :=
  LangTorusAt k fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e

structure LangPieces (P : ℕ → Prop) : Prop where
  frobenius : FrobeniusOnRoots
  subnormal : LangSubnormal
  generation : LangGeneration P
  inner : LangComponentsQuasisimple .inner
  suN : LangComponentsQuasisimple .suN
  twoD : LangComponentsQuasisimple .twoD
  exc : LangComponentsQuasisimple .exc

end CFSG.HardMathSupport.Timmesfeld.LangTorus
