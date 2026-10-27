module

public import CFSG.LieType.Multipliers.U43Data
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43 CFSG.ClassicalInvolution

open scoped commutatorElement Matrix

@[expose] def zU : Fin 2 → List (Fin 2 × Bool)
  | 0 => [(0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true),
      (1, false)]
  | 1 => [(1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, false), (1, false)]

@[expose] def zV : Fin 2 → List (Fin 2 × Bool)
  | 0 => [(0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true),
      (1, true), (0, true), (1, false), (1, false), (0, true), (1, true)]
  | 1 => [(1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true)]

@[expose] def zW : Fin 2 → FreeGroup (Fin 2) := fun i => FreeGroup.mk (commWords (coverPairs i))

abbrev ZetaCover : Type := PresentedCover (wordSet rels) zW

@[expose] def zCommP (k : Fin 2) : ZetaCover :=
  PresentedGroup.mk _ ⁅FreeGroup.mk (zU k), FreeGroup.mk (zV k)⁆

@[expose] def zCanon {E : Type*} [Group E] (eh : Fin 2 → E) : Fin 2 → E :=
  fun i => FreeGroup.lift eh (zW i)

@[expose] def zComm {E : Type*} [Group E] (e : Fin 2 → E) (k : Fin 2) : E :=
  ⁅FreeGroup.lift e (FreeGroup.mk (zU k)), FreeGroup.lift e (FreeGroup.mk (zV k))⁆

@[expose] def zWordEval {M : Type*} [Monoid M] (X Y : Fin 2 → M) (w : List (Fin 2 × Bool)) : M :=
  (w.map fun l => if l.2 then X l.1 else Y l.1).prod

@[expose] def zRefl (v : Fin 6 → ZMod 3) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 - (2 * (v ⬝ᵥ v)) • Matrix.vecMulVec v v

@[expose] def zVecsA : List (Fin 6 → ZMod 3) := [![2, 2, 0, 1, 1, 0], ![1, 0, 1, 0, 1, 1]]

@[expose] def zVecsB : List (Fin 6 → ZMod 3) :=
  [![2, 0, 2, 0, 0, 0], ![0, 2, 0, 2, 0, 0], ![2, 2, 0, 2, 1, 0], ![1, 0, 1, 1, 0, 1]]

@[expose] def zVecsG : List (Fin 6 → ZMod 3) := [![1, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0]]

@[expose] def zMatA : Matrix (Fin 6) (Fin 6) (ZMod 3) := (zVecsA.map zRefl).prod

@[expose] def zMatB : Matrix (Fin 6) (Fin 6) (ZMod 3) := -(zVecsB.map zRefl).prod

@[expose] def zMatG : Matrix (Fin 6) (Fin 6) (ZMod 3) := (zVecsG.map zRefl).prod

@[expose] def zEvalM (w : List (Fin 2 × Bool)) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  zWordEval ![zMatA, zMatB] ![zMatAᵀ, zMatBᵀ] w

@[expose] def ZetaPermSide : Prop :=
  ∃ ρ : ZetaCover →* Equiv.Perm (Fin 756),
    ρ (zCommP 0) ^ 3 = 1 ∧ ρ (zCommP 1) ^ 3 = 1 ∧ Commute (ρ (zCommP 0)) (ρ (zCommP 1)) ∧
      ∀ i j : Fin 3, ρ (zCommP 0) ^ (i : ℕ) * ρ (zCommP 1) ^ (j : ℕ) = 1 → i = 0 ∧ j = 0

@[expose] def ZetaMatrixFacts : Prop :=
  (∀ v ∈ zVecsA ++ zVecsB ++ zVecsG, v ⬝ᵥ v ≠ 0) ∧
  (zVecsA.map fun v => v ⬝ᵥ v).prod = 1 ∧
  (zVecsB.map fun v => v ⬝ᵥ v).prod = 1 ∧
  (zVecsG.map fun v => v ⬝ᵥ v).prod = 2 ∧
  (∀ r ∈ rels, zEvalM r = 1 ∨ zEvalM r = -1) ∧
  (∀ i, zEvalM (commWords (coverPairs i)) = ![zMatA, zMatB] i) ∧
  zMatA ≠ 1 ∧ zMatA ≠ -1 ∧
  ∀ k : Fin 2, zEvalM (zU k) * zEvalM (zV k) = zEvalM (zV k) * zEvalM (zU k) ∧
    zMatG * zEvalM (zU k) = zEvalM (zU k) * zMatG ∧
    zMatG * zEvalM (zV k) * zMatGᵀ = (zEvalM (zV k))ᵀ

@[expose] def ZetaFrameHom : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate),
    Module.finrank (ZMod 3) V = 6 → quadSign Q = -1 →
    ∃ ι : OGroup Q →* Matrix (Fin 6) (Fin 6) (ZMod 3),
      Function.Injective ι ∧ (∀ g, ι g * (ι g)ᵀ = 1) ∧ ι (piOrth Q) = -1 ∧
      piOrth Q ∈ omegaGroup hQ ∧
      ∀ (v : Fin 6 → ZMod 3) (h : v ⬝ᵥ v ≠ 0), ∃ r : OGroup Q, ι r = zRefl v ∧
        detSpinorNorm hQ r = (-1, TauCeti.squareClassHom (Units.mk0 (v ⬝ᵥ v) h))

@[expose] def ZetaOmegaData : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate),
    Module.finrank (ZMod 3) V = 6 → quadSign Q = -1 →
    ∃ (A B : omegaGroup hQ) (g : OGroup Q),
      (detSpinorNorm hQ g).1 = 1 ∧ (detSpinorNorm hQ g).2 ≠ 1 ∧
      (∀ r ∈ wordSet rels, FreeGroup.lift ![A, B] r ∈ Subgroup.center (omegaGroup hQ)) ∧
      (∀ i, FreeGroup.lift ![A, B] (zW i) = ![A, B] i) ∧
      A ∉ Subgroup.center (omegaGroup hQ) ∧
      ∀ k : Fin 2,
        ⁅((FreeGroup.lift ![A, B] (FreeGroup.mk (zU k)) : omegaGroup hQ) : OGroup Q),
          ((FreeGroup.lift ![A, B] (FreeGroup.mk (zV k)) : omegaGroup hQ) : OGroup Q)⁆ = 1 ∧
        g * ((FreeGroup.lift ![A, B] (FreeGroup.mk (zU k)) : omegaGroup hQ) : OGroup Q) * g⁻¹ =
          ((FreeGroup.lift ![A, B] (FreeGroup.mk (zU k)) : omegaGroup hQ) : OGroup Q) ∧
        g * ((FreeGroup.lift ![A, B] (FreeGroup.mk (zV k)) : omegaGroup hQ) : OGroup Q) * g⁻¹ =
          ((FreeGroup.lift ![A, B] (FreeGroup.mk (zV k)) : omegaGroup hQ) : OGroup Q)⁻¹

@[expose] def ZetaPresentation : Prop :=
  ∀ (S : Type) [Group S] (s : Fin 2 → S),
    CFSG.Blueprint.LieModel S .PSU 4 3 1 → (∀ r ∈ wordSet rels, FreeGroup.lift s r = 1) →
      s 0 ≠ 1 → IsPresentation s (wordSet rels)

@[expose] def ZetaLift : Prop :=
  ∀ {S E : Type} [Group S] [Group E] (q : E →* S), Function.Surjective q →
    q.ker ≤ Subgroup.center E → commutator E = ⊤ →
    ∀ (s : Fin 2 → S) (hP : IsPresentation s (wordSet rels))
      (hwg : ∀ i, FreeGroup.lift s (zW i) = s i) (eh : Fin 2 → E), (∀ i, q (eh i) = s i) →
      ∃ lam : ZetaCover →* E,
        (∀ i, lam (PresentedGroup.of i) = zCanon eh i) ∧
        (∀ p, q (lam p) = coverMap (w := zW) hP hwg p) ∧ Function.Surjective lam

@[expose] def ZetaCount : Prop :=
  ∀ {M H : Type} [Group M] [Group H] (_ : M ≃* Multiplicative (ZMod 4 × ZMod 3 × ZMod 3))
    (ρ : M →* H) (c₀ c₁ : M), ρ c₀ ^ 3 = 1 → ρ c₁ ^ 3 = 1 →
    (∀ i j : Fin 3, ρ c₀ ^ (i : ℕ) * ρ c₁ ^ (j : ℕ) = 1 → i = 0 ∧ j = 0) →
    ∀ m : M, ∃ i j : Fin 3, m ^ 4 = c₀ ^ (4 * (i : ℕ)) * c₁ ^ (4 * (j : ℕ))

@[expose] def ZetaCore : Prop :=
  ∀
    {E S : Type} [Group E] [Group S] (q : E →* S),
    Function.Surjective q → q.ker ≤ Subgroup.center E → commutator E = ⊤ →
    CFSG.Blueprint.LieModel S .PSU 4 3 1 →
    ∀ eh : Fin 2 → E, (∀ r ∈ wordSet rels, FreeGroup.lift (fun i => q (eh i)) r = 1) →
      q (eh 0) ≠ 1 → (∀ i, FreeGroup.lift (fun j => q (eh j)) (zW i) = q (eh i)) →
      (∀ k, zComm (zCanon eh) k ∈ q.ker) →
      (∀ x ∈ q.ker, x ^ 12 = 1) ∧
      ∀ x ∈ q.ker, x ^ 3 = 1 → ∃ i j : Fin 3,
        x = zComm (zCanon eh) 0 ^ (4 * (i : ℕ)) * zComm (zCanon eh) 1 ^ (4 * (j : ℕ))

@[expose] def ZetaCorrect : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} (φ : ↥L →* omegaGroup hQ),
    Function.Surjective φ → ∀ (w : G) (o : OGroup Q), CoverAct L φ w (orthToSim Q o) →
      (detSpinorNorm hQ o).1 = 1 → (detSpinorNorm hQ o).2 ≠ 1 →
      ∀ g : OGroup Q, (detSpinorNorm hQ g).1 = 1 → (detSpinorNorm hQ g).2 ≠ 1 →
        ∃ ω : ↥L, ∀ l l' : ↥L, (l' : G) = w * (ω : G) * l * (w * (ω : G))⁻¹ →
          ((φ l' : omegaGroup hQ) : OGroup Q) = g * ((φ l : omegaGroup hQ) : OGroup Q) * g⁻¹

@[expose] def ZetaInvert : Prop :=
  ∀ {G H : Type} [Group G] [Group H] (L : Subgroup G) (φ : ↥L →* H),
    φ.ker ≤ Subgroup.center ↥L → ∀ (w' : G), w' ∈ Subgroup.normalizer (L : Set G) →
    ∀ g : H, (∀ l l' : ↥L, (l' : G) = w' * l * w'⁻¹ → φ l' = g * φ l * g⁻¹) →
      ∀ u v : ↥L, ⁅φ u, φ v⁆ = 1 → g * φ u * g⁻¹ = φ u → g * φ v * g⁻¹ = (φ v)⁻¹ →
        ⁅u, v⁆ ∈ φ.ker ∧ w' * ((⁅u, v⁆ : ↥L) : G) * w'⁻¹ = (((⁅u, v⁆ : ↥L) : G))⁻¹

end CFSG.OddStandard.SmallF3.Omega
