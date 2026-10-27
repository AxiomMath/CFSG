module

public import Mathlib
public import CFSG.Open.StatedDefs
public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.Assembly

open scoped MatrixGroups

noncomputable section

section Lie

inductive LargeEvenLieTag
  | A | twA | B | C | D | twD | E6 | E7 | E8 | F4 | twE6 | triD4 | G2 | twB2 | twF4
  | B2der | G2der | twF4der
  deriving DecidableEq

structure LargeEvenLabel where
  tag : LargeEvenLieTag
  rank : ℕ
  n : ℕ

@[expose] def LargeEvenInLambda2 (lab : LargeEvenLabel) : Prop :=
  1 ≤ lab.n ∧
    match lab.tag with
    | .A => 1 ≤ lab.rank ∧ (lab.rank = 1 → 2 ≤ lab.n)
    | .twA => 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n)
    | .B | .C => 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n)
    | .D => 3 ≤ lab.rank
    | .twD => 2 ≤ lab.rank
    | .E6 | .E7 | .E8 | .F4 | .twE6 | .triD4 => lab.rank = 0
    | .G2 => lab.rank = 0 ∧ 2 ≤ lab.n
    | .twB2 | .twF4 => lab.rank = 0 ∧ Odd lab.n ∧ 3 ≤ lab.n
    | .B2der | .G2der | .twF4der => lab.rank = 0 ∧ lab.n = 1

@[expose] def LargeEvenUntwisted : LargeEvenLieTag → Prop
  | .A | .B | .C | .D | .E6 | .E7 | .E8 | .F4 | .G2 | .B2der | .G2der => True
  | _ => False

@[expose] def LargeEvenSplit (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (LargeEvenUntwisted lab.tag ∧ p ∣ 2 ^ lab.n - 1) ∨
    (¬ LargeEvenUntwisted lab.tag ∧ lab.tag ≠ .triD4 ∧ p ∣ 2 ^ lab.n + 1) ∨
    ((lab.tag = .twD ∨ lab.tag = .triD4) ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.n = 1 ∧ p = 3)

@[expose] def LargeEvenHalfSplit (p : ℕ) (lab : LargeEvenLabel) (centerTrivial : Prop) : Prop :=
  LargeEvenSplit p lab ∨
    ((lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧
      p ∣ 2 ^ lab.n + 1) ∨
    (((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 2 ∧ centerTrivial ∧ p = 5) ∨
    (lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1 ∧ p = 7) ∨
    (lab.tag = .E6 ∧ lab.n = 1 ∧ p = 7)

@[expose] def LargeEvenGraphAut {H R : Type*} [Group H] [Group R] (π : H →* R) (rel : H → H → Prop)
    (φ : MulAut R) : Prop :=
  ∀ h h' : H, rel h h' → φ (π h) = π h'

@[expose] def LargeEvenInnSet (R : Type*) [Group R] : Set (MulAut R) :=
  Set.range MulAut.conj

section Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

variable (ι K) in
abbrev LargeEvenScalars : Subgroup (GL ι K) :=
  CFSG.Open.StatedScalars ι K

theorem largeEvenScalars_def : LargeEvenScalars ι K = (Matrix.GeneralLinearGroup.scalar ι).range :=
  rfl

instance LargeEvenScalars.normal : (LargeEvenScalars ι K).Normal :=
  CFSG.Open.StatedScalars.normal ι K

abbrev LargeEvenProj (H : Subgroup (GL ι K)) : Type :=
  ↥H ⧸ (LargeEvenScalars ι K).subgroupOf H

abbrev LargeEvenProjMk (H : Subgroup (GL ι K)) : ↥H →* LargeEvenProj H :=
  QuotientGroup.mk' _

variable (ι K) in
@[expose] def LargeEvenSLGroup : Subgroup (GL ι K) :=
  matrix_model% CFSG.MatrixModel.slCore ι K

variable (ι K) in
@[expose] def LargeEvenSUGroup (q : ℕ) : Subgroup (GL ι K) :=
  matrix_model% CFSG.MatrixModel.unitaryCore ι K q

variable (K) in
abbrev LargeEvenSpForm (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  CFSG.PGLModel.sympForm m K

theorem largeEvenSpForm_def (m : ℕ) : LargeEvenSpForm K m = Matrix.fromBlocks 0 1 (-1) 0 :=
  rfl

variable (K) in
abbrev LargeEvenSpGroup (m : ℕ) : Subgroup (GL (Fin m ⊕ Fin m) K) :=
  CFSG.Open.StatedSp m K

theorem largeEvenSpGroup_def (m : ℕ) :
    LargeEvenSpGroup K m = Subgroup.closure {g : GL (Fin m ⊕ Fin m) K |
    Matrix.transpose (g : Matrix _ _ K) * LargeEvenSpForm K m * (g : Matrix _ _ K) =
      LargeEvenSpForm K m} :=
  rfl

abbrev LargeEvenOrthGroup (Q : (ι → K) → K) : Subgroup (GL ι K) :=
  CFSG.PGLModel.orthogonalGroup Q

theorem largeEvenOrthGroup_def (Q : (ι → K) → K) :
    LargeEvenOrthGroup Q =
      Subgroup.closure {g : GL ι K | ∀ v : ι → K, Q ((g : Matrix ι ι K).mulVec v) = Q v} :=
  rfl

abbrev LargeEvenOmega (Q : (ι → K) → K) : Subgroup (GL ι K) :=
  CFSG.Open.StatedOmega Q

theorem largeEvenOmega_def (Q : (ι → K) → K) :
    LargeEvenOmega Q = ⁅LargeEvenOrthGroup Q, LargeEvenOrthGroup Q⁆ :=
  rfl

variable (K) in
abbrev LargeEvenQPlus (m : ℕ) : (Fin m ⊕ Fin m → K) → K :=
  CFSG.Open.StatedQuadPlus m K

theorem largeEvenQPlus_def (m : ℕ) :
    LargeEvenQPlus K m = fun w => ∑ i, w (Sum.inl i) * w (Sum.inr i) :=
  rfl

abbrev LargeEvenMinusIdx (m : ℕ) : Type :=
  (Fin m ⊕ Fin m) ⊕ Fin 2

@[expose] def LargeEvenQMinus (m : ℕ) (b c : K) : (LargeEvenMinusIdx m → K) → K :=
  fun w => (∑ i, w (Sum.inl (Sum.inl i)) * w (Sum.inl (Sum.inr i))) + w (Sum.inr 0) ^ 2 +
    b * w (Sum.inr 0) * w (Sum.inr 1) + c * w (Sum.inr 1) ^ 2

variable (ι K) in
@[expose] def LargeEvenGUSet (q : ℕ) : Set (GL ι K) :=
  {A | ∃ μ : K, μ ≠ 0 ∧ μ ^ q = μ ∧
    Matrix.transpose ((A : Matrix ι ι K).map (· ^ q)) * (A : Matrix ι ι K) = μ • (1 : Matrix ι ι K)}

variable (K) in
@[expose] def LargeEvenGSpSet (m : ℕ) : Set (GL (Fin m ⊕ Fin m) K) :=
  {A | ∃ μ : K, μ ≠ 0 ∧
    Matrix.transpose (A : Matrix _ _ K) * LargeEvenSpForm K m * (A : Matrix _ _ K) =
    μ • LargeEvenSpForm K m}

@[expose] def LargeEvenMatConjImage {H : Subgroup (GL ι K)} {R : Type} [Group R] (π : ↥H →* R)
    (S : Set (GL ι K)) : Set (MulAut R) :=
  {φ | ∃ A ∈ S, LargeEvenGraphAut π (fun h h' => (h' : GL ι K) = A * h * A⁻¹) φ}

@[expose] def LargeEvenMatFieldImage {H : Subgroup (GL ι K)} {R : Type} [Group R] (π : ↥H →* R) :
    Set (MulAut R) :=
  {φ | ∃ σ : K ≃+* K, LargeEvenGraphAut π
    (fun h h' => ((h' : GL ι K) : Matrix ι ι K) = ((h : GL ι K) : Matrix ι ι K).map σ) φ}

@[expose] def LargeEvenFrobBlock (m : ℕ) (b c : K) (k : ℕ) :
    Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K :=
  let rk : QuadraticAlgebra K c b := (⟨0, 1⟩ : QuadraticAlgebra K c b) ^ 2 ^ k
  Matrix.fromBlocks 1 0 0 !![1, rk.re; 0, rk.im]

@[expose] def LargeEvenPhiQ (m : ℕ) (b c : K) {H : Subgroup (GL (LargeEvenMinusIdx m) K)} {R : Type}
    [Group R] (π : ↥H →* R) : Set (MulAut R) :=
  {φ | ∃ k : ℕ, LargeEvenGraphAut π
    (fun h h' =>
      ((h' : GL (LargeEvenMinusIdx m) K) : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *
        LargeEvenFrobBlock m b c k =
      LargeEvenFrobBlock m b c k *
        ((h : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K).map
          (· ^ 2 ^ k)) φ}

end Classical

abbrev LargeEvenRawCont : Type 1 :=
  (R : Type) → [Group R] → Set (MulAut R) → Set (MulAut R) → Prop

@[expose] def LargeEvenRecipeLinear (d N : ℕ) (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = N ∧
    Q (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk _))

@[expose] def LargeEvenRecipeUnitary (d q : ℕ) (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧
    Q (LargeEvenProj (LargeEvenSUGroup (Fin d) K q))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K q))
      (LargeEvenMatFieldImage (LargeEvenProjMk _))

@[expose] def LargeEvenRecipeSymplectic (m q : ℕ) (derived : Bool) (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Q (LargeEvenProj
        (if derived then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆ else LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m))
      (LargeEvenMatFieldImage (LargeEvenProjMk _))

@[expose] def LargeEvenRecipeOmegaPlus (m q : ℕ) (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Q (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk _))

@[expose] def LargeEvenRecipeOmegaMinus (m q : ℕ) (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      Q (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) (LargeEvenInnSet _)
        (LargeEvenPhiQ m b c (LargeEvenProjMk _))

section Chevalley

variable {r : ℕ}

@[expose] def LargeEvenCartanG2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -1; -3, 2]

@[expose] def LargeEvenCartanF4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]

@[expose] def LargeEvenCartanD4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 0, -1, 0; 0, 2, -1, 0; -1, -1, 2, -1; 0, 0, -1, 2]

@[expose] def LargeEvenCartanE (r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j =>
    if i = j then 2
    else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨ (i.val = 1 ∧ j.val = 3) ∨
        (i.val = 3 ∧ j.val = 1) ∨ (2 ≤ i.val ∧ j.val = i.val + 1) ∨
        (2 ≤ j.val ∧ i.val = j.val + 1) then -1
    else 0

@[expose] def LargeEvenRhoE6 : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 5 * Equiv.swap 2 4

@[expose] def LargeEvenRhoD4 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 1 3

@[expose] def LargeEvenRhoF4 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 3 * Equiv.swap 1 2

@[expose] def LargeEvenReflect (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) (v : Fin r → ℤ) : Fin r → ℤ :=
  v - (∑ j, A i j * v j) • Pi.single i 1

inductive LargeEvenIsRoot (A : Matrix (Fin r) (Fin r) ℤ) : (Fin r → ℤ) → Prop
  | simple (j : Fin r) : LargeEvenIsRoot A (Pi.single j 1)
  | reflect (i : Fin r) {v : Fin r → ℤ} :
      LargeEvenIsRoot A v → LargeEvenIsRoot A (LargeEvenReflect A i v)

abbrev LargeEvenRootIndex (A : Matrix (Fin r) (Fin r) ℤ) : Type :=
  Fin r ⊕ {v : Fin r → ℤ // LargeEvenIsRoot A v}

abbrev LargeEvenChevModule (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K] : Type :=
  LargeEvenRootIndex A →₀ K

abbrev LargeEvenChevGL (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K] : Type :=
  LinearMap.GeneralLinearGroup K (LargeEvenChevModule A K)

variable (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

@[expose] noncomputable def LargeEvenHVec (i : Fin r) : LargeEvenChevModule A K :=
  Finsupp.single (Sum.inl i) 1

open Classical in
@[expose] noncomputable def LargeEvenRootVec (β : Fin r → ℤ) : LargeEvenChevModule A K :=
  if h : LargeEvenIsRoot A β then Finsupp.single (Sum.inr ⟨β, h⟩) 1 else 0

@[expose] noncomputable def LargeEvenStringUp (i : Fin r) (α : Fin r → ℤ) : ℕ :=
  sSup {k : ℕ | LargeEvenIsRoot A (α + (k : ℤ) • Pi.single i 1)}

@[expose] noncomputable def LargeEvenStringDown (i : Fin r) (α : Fin r → ℤ) : ℕ :=
  sSup {k : ℕ | LargeEvenIsRoot A (α - (k : ℤ) • Pi.single i 1)}

open Classical in
@[expose] noncomputable def LargeEvenXOp (i : Fin r) (c : K) : Module.End K (LargeEvenChevModule A K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl j =>
      LargeEvenHVec A K j + (((A j i).natAbs : K) * c) • LargeEvenRootVec A K (Pi.single i 1)
    | Sum.inr α =>
      if α.1 = Pi.single i 1 then LargeEvenRootVec A K α.1
      else if α.1 = -Pi.single i 1 then
        LargeEvenRootVec A K α.1 + c • LargeEvenHVec A K i +
          c ^ 2 • LargeEvenRootVec A K (Pi.single i 1)
      else
        ∑ k ∈ Finset.range (LargeEvenStringUp A i α.1 + 1),
          (((LargeEvenStringDown A i α.1 + k).choose k : K) * c ^ k) •
            LargeEvenRootVec A K (α.1 + (k : ℤ) • Pi.single i 1)

open Classical in
@[expose] noncomputable def LargeEvenYOp (i : Fin r) (c : K) : Module.End K (LargeEvenChevModule A K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl j =>
      LargeEvenHVec A K j + (((A j i).natAbs : K) * c) • LargeEvenRootVec A K (-Pi.single i 1)
    | Sum.inr α =>
      if α.1 = -Pi.single i 1 then LargeEvenRootVec A K α.1
      else if α.1 = Pi.single i 1 then
        LargeEvenRootVec A K α.1 + c • LargeEvenHVec A K i +
          c ^ 2 • LargeEvenRootVec A K (-Pi.single i 1)
      else
        ∑ k ∈ Finset.range (LargeEvenStringDown A i α.1 + 1),
          (((LargeEvenStringUp A i α.1 + k).choose k : K) * c ^ k) •
            LargeEvenRootVec A K (α.1 - (k : ℤ) • Pi.single i 1)

@[expose] def LargeEvenChevGroup : Subgroup (LargeEvenChevGL A K) :=
  Subgroup.closure {g | ∃ (i : Fin r) (c : K),
    (g : Module.End K (LargeEvenChevModule A K)) = LargeEvenXOp A K i c ∨
      (g : Module.End K (LargeEvenChevModule A K)) = LargeEvenYOp A K i c}

@[expose] noncomputable def LargeEvenEntrywise (f : K → K) (hf : f 0 = 0)
    (g : Module.End K (LargeEvenChevModule A K)) :
    Module.End K (LargeEvenChevModule A K) :=
  Finsupp.linearCombination K fun b => Finsupp.mapRange f hf (g (Finsupp.single b 1))

@[expose] noncomputable def LargeEvenDiagramMap (ρ : Equiv.Perm (Fin r)) :
    Module.End K (LargeEvenChevModule A K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl i => LargeEvenHVec A K (ρ i)
    | Sum.inr α => LargeEvenRootVec A K (α.1 ∘ ρ.symm)

@[expose] noncomputable def LargeEvenDiagMap (a : Fin r → Kˣ) : Module.End K (LargeEvenChevModule A K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl i => LargeEvenHVec A K i
    | Sum.inr α => ((∏ i, a i ^ α.1 i : Kˣ) : K) • Finsupp.single (Sum.inr α) 1

abbrev LargeEvenCenterQuot {M : Type} [Group M] (H : Subgroup M) : Type :=
  ↥H ⧸ Subgroup.center ↥H

abbrev LargeEvenCenterMk {M : Type} [Group M] (H : Subgroup M) : ↥H →* LargeEvenCenterQuot H :=
  QuotientGroup.mk' _

@[expose] def LargeEvenChevDiagImage (H : Subgroup (LargeEvenChevGL A K)) :
    Set (MulAut (LargeEvenCenterQuot H)) :=
  {φ | ∃ a : Fin r → Kˣ,
    (∀ h : H, ∃ h' : H, ((h' : LargeEvenChevGL A K) : Module.End K _) * LargeEvenDiagMap A K a =
      LargeEvenDiagMap A K a * ((h : LargeEvenChevGL A K) : Module.End K _)) ∧
    (∀ h' : H, ∃ h : H, ((h' : LargeEvenChevGL A K) : Module.End K _) * LargeEvenDiagMap A K a =
      LargeEvenDiagMap A K a * ((h : LargeEvenChevGL A K) : Module.End K _)) ∧
    LargeEvenGraphAut (LargeEvenCenterMk H)
      (fun h h' => ((h' : LargeEvenChevGL A K) : Module.End K _) * LargeEvenDiagMap A K a =
        LargeEvenDiagMap A K a * ((h : LargeEvenChevGL A K) : Module.End K _)) φ}

@[expose] def LargeEvenChevIDImage (H : Subgroup (LargeEvenChevGL A K)) :
    Set (MulAut (LargeEvenCenterQuot H)) :=
  (Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage A K H) :
    Set (MulAut (LargeEvenCenterQuot H)))

@[expose] def LargeEvenParentConjImage {M : Type} [Group M] (P H : Subgroup M) :
    Set (MulAut (LargeEvenCenterQuot H)) :=
  {φ | ∃ g ∈ P, g ∈ Subgroup.normalizer (H : Set M) ∧
    ∀ h : H, ∃ h' : H, (h' : M) = g * (h : M) * g⁻¹ ∧
      φ (LargeEvenCenterMk H h) = LargeEvenCenterMk H h'}

@[expose] def LargeEvenChevParentIDImage (P H : Subgroup (LargeEvenChevGL A K)) :
    Set (MulAut (LargeEvenCenterQuot H)) :=
  (Subgroup.closure (LargeEvenChevIDImage A K H ∪ LargeEvenParentConjImage P H) :
    Set (MulAut (LargeEvenCenterQuot H)))

@[expose] def LargeEvenChevFieldImage (H : Subgroup (LargeEvenChevGL A K)) :
    Set (MulAut (LargeEvenCenterQuot H)) :=
  {φ | ∃ σ : K ≃+* K, LargeEvenGraphAut (LargeEvenCenterMk H)
    (fun h h' => ((h' : LargeEvenChevGL A K) : Module.End K _) =
      LargeEvenEntrywise A K σ (map_zero σ) ((h : LargeEvenChevGL A K) : Module.End K _)) φ}

@[expose] def LargeEvenChevH (derived : Bool) : Subgroup (LargeEvenChevGL A K) :=
  if derived then ⁅LargeEvenChevGroup A K, LargeEvenChevGroup A K⁆ else LargeEvenChevGroup A K

@[expose] def LargeEvenTwistedH (ρ : Equiv.Perm (Fin r)) (n : ℕ) : Subgroup (LargeEvenChevGL A K) :=
  let F : Subgroup (LargeEvenChevGL A K) := Subgroup.closure {g | g ∈ LargeEvenChevGroup A K ∧
    LargeEvenDiagramMap A K ρ *
        LargeEvenEntrywise A K (fun c => c ^ 2 ^ n) (zero_pow (pow_ne_zero n two_ne_zero))
          (g : Module.End K (LargeEvenChevModule A K)) =
      (g : Module.End K (LargeEvenChevModule A K)) * LargeEvenDiagramMap A K ρ}
  ⁅F, F⁆

end Chevalley

@[expose] def LargeEvenTwF4Exp (a : ℕ) (i : Fin 4) : ℕ :=
  if i.val < 2 then 2 ^ a else 2 ^ (a + 1)

@[expose] def LargeEvenTwF4Parent (a : ℕ) (K : Type) [Field K] : Subgroup (LargeEvenChevGL LargeEvenCartanF4 K) :=
  let R₀ : Subgroup (LargeEvenChevGL LargeEvenCartanF4 K × LargeEvenChevGL LargeEvenCartanF4 K) :=
    Subgroup.closure {gh | ∃ (i : Fin 4) (c : K),
      ((gh.1 : Module.End K _) = LargeEvenXOp LargeEvenCartanF4 K i c ∧
          (gh.2 : Module.End K _) =
            LargeEvenXOp LargeEvenCartanF4 K (LargeEvenRhoF4 i) (c ^ LargeEvenTwF4Exp a i)) ∨
        ((gh.1 : Module.End K _) = LargeEvenYOp LargeEvenCartanF4 K i c ∧
          (gh.2 : Module.End K _) =
            LargeEvenYOp LargeEvenCartanF4 K (LargeEvenRhoF4 i) (c ^ LargeEvenTwF4Exp a i))}
  LargeEvenChevGroup LargeEvenCartanF4 K ⊓ R₀.comap ((MonoidHom.id _).prod (MonoidHom.id _))

@[expose] def LargeEvenTwF4H (a : ℕ) (K : Type) [Field K] :
    Subgroup (LargeEvenChevGL LargeEvenCartanF4 K) :=
  ⁅LargeEvenTwF4Parent a K, LargeEvenTwF4Parent a K⁆

@[expose] def LargeEvenSzGens (a : ℕ) (K : Type) [Field K] : Set (Matrix (Fin 4) (Fin 4) K) :=
  {M | (∃ u v : K, M = !![1, 0, 0, 0; u, 1, 0, 0; v, u ^ 2 ^ (a + 1), 1, 0;
        u ^ (2 ^ (a + 1) + 2) + u * v + v ^ 2 ^ (a + 1), u ^ (2 ^ (a + 1) + 1) + v, u, 1]) ∨
    (∃ l : Kˣ, M = Matrix.diagonal ![(l : K) ^ (1 + 2 ^ a), (l : K) ^ 2 ^ a,
        ((l⁻¹ : Kˣ) : K) ^ 2 ^ a, ((l⁻¹ : Kˣ) : K) ^ (1 + 2 ^ a)]) ∨
    M = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]}

@[expose] def LargeEvenSzGroup (a : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin 4) K) :=
  Subgroup.closure {g | (g : Matrix (Fin 4) (Fin 4) K) ∈ LargeEvenSzGens a K}

@[expose] def LargeEvenRecipeChevalley {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (q : ℕ) (derived : Bool)
    (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Q (LargeEvenCenterQuot (LargeEvenChevH A K derived)) (LargeEvenChevIDImage A K _)
      (LargeEvenChevFieldImage A K _)

@[expose] def LargeEvenRecipeTwisted {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r)) (m n : ℕ)
    (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n) ^ m ∧
    Q (LargeEvenCenterQuot (LargeEvenTwistedH A K ρ n)) (LargeEvenChevIDImage A K _)
      (LargeEvenChevFieldImage A K _)

@[expose] def LargeEvenRecipeSuzuki (a : ℕ) (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
    Q (LargeEvenCenterQuot (LargeEvenSzGroup a K)) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenCenterMk _))

@[expose] def LargeEvenRecipeTwF4 (a : ℕ) (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
    Q (LargeEvenCenterQuot (LargeEvenTwF4H a K)) (LargeEvenChevIDImage LargeEvenCartanF4 K _)
      (LargeEvenChevFieldImage LargeEvenCartanF4 K _)

@[expose] def LargeEvenRawDatumLegacy (lab : LargeEvenLabel) (Q : LargeEvenRawCont) : Prop :=
  match lab.tag with
  | .A => LargeEvenRecipeLinear (lab.rank + 1) (2 ^ lab.n) Q
  | .twA => LargeEvenRecipeUnitary (lab.rank + 1) (2 ^ lab.n) Q
  | .B | .C => LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false Q
  | .B2der => LargeEvenRecipeSymplectic 2 2 true Q
  | .D =>
    if lab.rank = 3 then LargeEvenRecipeLinear 4 (2 ^ lab.n) Q
    else LargeEvenRecipeOmegaPlus lab.rank (2 ^ lab.n) Q
  | .twD =>
    if lab.rank = 2 then LargeEvenRecipeLinear 2 ((2 ^ lab.n) ^ 2) Q
    else if lab.rank = 3 then LargeEvenRecipeUnitary 4 (2 ^ lab.n) Q
    else LargeEvenRecipeOmegaMinus (lab.rank - 1) (2 ^ lab.n) Q
  | .G2 => LargeEvenRecipeChevalley LargeEvenCartanG2 (2 ^ lab.n) false Q
  | .G2der => LargeEvenRecipeChevalley LargeEvenCartanG2 2 true Q
  | .F4 => LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ lab.n) false Q
  | .E6 => LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ lab.n) false Q
  | .E7 => LargeEvenRecipeChevalley (LargeEvenCartanE 7) (2 ^ lab.n) false Q
  | .E8 => LargeEvenRecipeChevalley (LargeEvenCartanE 8) (2 ^ lab.n) false Q
  | .twE6 => LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 lab.n Q
  | .triD4 => LargeEvenRecipeTwisted LargeEvenCartanD4 LargeEvenRhoD4 3 lab.n Q
  | .twB2 => LargeEvenRecipeSuzuki ((lab.n - 1) / 2) Q
  | .twF4 | .twF4der => LargeEvenRecipeTwF4 ((lab.n - 1) / 2) Q

@[expose] def LargeEvenRecipeG2Derived (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
    Q (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))
      (LargeEvenChevParentIDImage LargeEvenCartanG2 K
        (LargeEvenChevGroup LargeEvenCartanG2 K) (LargeEvenChevH LargeEvenCartanG2 K true))
      (LargeEvenChevFieldImage LargeEvenCartanG2 K _)

@[expose] def LargeEvenRecipeTwF4Inherited (a : ℕ) (Q : LargeEvenRawCont) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
    Q (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (if a = 0 then LargeEvenChevParentIDImage LargeEvenCartanF4 K
        (LargeEvenTwF4Parent a K) (LargeEvenTwF4H a K)
       else LargeEvenChevIDImage LargeEvenCartanF4 K _)
      (LargeEvenChevFieldImage LargeEvenCartanF4 K _)

@[expose] def LargeEvenRawDatum (lab : LargeEvenLabel) (Q : LargeEvenRawCont) : Prop :=
  match lab.tag with
  | .A => LargeEvenRecipeLinear (lab.rank + 1) (2 ^ lab.n) Q
  | .twA => LargeEvenRecipeUnitary (lab.rank + 1) (2 ^ lab.n) Q
  | .B | .C => LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false Q
  | .B2der => LargeEvenRecipeSymplectic 2 2 true Q
  | .D =>
    if lab.rank = 3 then LargeEvenRecipeLinear 4 (2 ^ lab.n) Q
    else LargeEvenRecipeOmegaPlus lab.rank (2 ^ lab.n) Q
  | .twD =>
    if lab.rank = 2 then LargeEvenRecipeLinear 2 ((2 ^ lab.n) ^ 2) Q
    else if lab.rank = 3 then LargeEvenRecipeUnitary 4 (2 ^ lab.n) Q
    else LargeEvenRecipeOmegaMinus (lab.rank - 1) (2 ^ lab.n) Q
  | .G2 => LargeEvenRecipeChevalley LargeEvenCartanG2 (2 ^ lab.n) false Q
  | .G2der => LargeEvenRecipeG2Derived Q
  | .F4 => LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ lab.n) false Q
  | .E6 => LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ lab.n) false Q
  | .E7 => LargeEvenRecipeChevalley (LargeEvenCartanE 7) (2 ^ lab.n) false Q
  | .E8 => LargeEvenRecipeChevalley (LargeEvenCartanE 8) (2 ^ lab.n) false Q
  | .twE6 => LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 lab.n Q
  | .triD4 => LargeEvenRecipeTwisted LargeEvenCartanD4 LargeEvenRhoD4 3 lab.n Q
  | .twB2 => LargeEvenRecipeSuzuki ((lab.n - 1) / 2) Q
  | .twF4 | .twF4der => LargeEvenRecipeTwF4Inherited ((lab.n - 1) / 2) Q

abbrev LargeEvenMarkProp (L : Type*) [Group L] : Type _ :=
  LargeEvenLabel → (R : Type) → [Group R] → Set (MulAut R) → Set (MulAut R) →
    (L ⧸ Subgroup.center L ≃* R) → Prop

@[expose] def LargeEvenMarking (L : Type*) [Group L] (P : LargeEvenMarkProp L) : Prop :=
  commutator L = ⊤ ∧ ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
    LargeEvenRawDatum lab fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* R, P lab R I F θ

theorem largeEvenRawDatumLegacy_to_canonical_carrier {lab : LargeEvenLabel}
    {T : (R : Type) → [Group R] → Prop}
    (h : LargeEvenRawDatumLegacy lab (fun R _ _ _ => T R)) :
    LargeEvenRawDatum lab (fun R _ _ _ => T R) := by
  obtain ⟨tag, rank, exponent⟩ := lab
  cases tag
  all_goals dsimp only [LargeEvenRawDatumLegacy, LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, fieldInst, finiteInst, hK, b, c, hbc, hT⟩ := h
       exact ⟨K, fieldInst, finiteInst, hK, b, c, hbc, hT⟩)
    | (obtain ⟨K, fieldInst, finiteInst, hK, hT⟩ := h
       exact ⟨K, fieldInst, finiteInst, hK, hT⟩)

@[expose] def LargeEvenMarkingLegacy (L : Type*) [Group L] (P : LargeEvenMarkProp L) : Prop :=
  commutator L = ⊤ ∧ ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
    LargeEvenRawDatumLegacy lab fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* R, P lab R I F θ

theorem largeEvenMarkingLegacy_to_canonical_carrier {L : Type*} [Group L]
    {P : LargeEvenLabel → (R : Type) → [Group R] →
      (L ⧸ Subgroup.center L ≃* R) → Prop}
    (h : LargeEvenMarkingLegacy L (fun lab R _ _ _ θ => P lab R θ)) :
    LargeEvenMarking L (fun lab R _ _ _ θ => P lab R θ) := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  exact ⟨hL, lab, hlab, largeEvenRawDatumLegacy_to_canonical_carrier hraw⟩

@[expose] def LargeEvenInduces {L : Type*} [Group L] {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (rel : L → L → Prop) (φ : MulAut R) : Prop :=
  ∀ l l' : L, rel l l' → φ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')

@[expose] def LargeEvenPrimeField (p : ℕ) (lab : LargeEvenLabel) {R : Type} [Group R] (I F : Set (MulAut R))
    (isα : MulAut R → Prop) : Prop :=
  (lab.tag ≠ .triD4 ∨ p ≠ 3) ∧ ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ isα (u * f * u⁻¹)

@[expose] def LargeEvenIsU42 (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
    Nonempty (X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K 2))

end Lie

section Local

variable {G : Type*} [Group G]

@[expose] def LargeEvenSymplecticType (T : Subgroup G) : Prop :=
  IsPGroup 2 T ∧ ∀ A : Subgroup T, A.Characteristic → IsMulCommutative A → IsCyclic A

@[expose] def LargeEvenSmall (K : Subgroup G) : Prop :=
  LargeEvenIsU42 K ∨ Nonempty (K ≃* alternatingGroup (Fin 6))

end Local

section StandardType

variable {G : Type*} [Group G]

@[expose] def LargeEvenStandardTypeOf (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G)
    (isNeighborOf : G → Subgroup G → Prop) (stdSub : Subgroup G → Subgroup G → Prop)
    (sHat : G → Subgroup G → Prop) (neighbor : G → Subgroup G → Subgroup G → Subgroup G → Prop)
    (pPrimeCoreOf : Subgroup G → Subgroup G) : Prop :=
  LargeEvenMarking L (fun lab _ _ I _ θ => LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
    (∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) ∧
    (∀ (y : G) (J : Subgroup G), isNeighborOf y J →
      B ≤ Subgroup.normalizer (J : Set G) ∧
        LargeEvenMarking J (fun lab _ _ I F θ =>
          LargeEvenHalfSplit p lab (Subgroup.center J = ⊥) ∨
            LargeEvenPrimeField p lab I F
              (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x))) ∧
    ∀ D K : Subgroup G, stdSub D K →
      (∃ (y : G) (J : Subgroup G), sHat y J ∧ neighbor y J D K) ∧
        ∀ d ∈ D, d ≠ 1 →
          Odd (Nat.card (⁅K, pPrimeCoreOf (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G))

@[expose] def LargeEvenStandardTypeOfLegacy (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G)
    (isNeighborOf : G → Subgroup G → Prop) (stdSub : Subgroup G → Subgroup G → Prop)
    (sHat : G → Subgroup G → Prop) (neighbor : G → Subgroup G → Subgroup G → Subgroup G → Prop)
    (pPrimeCoreOf : Subgroup G → Subgroup G) : Prop :=
  LargeEvenMarkingLegacy L (fun lab _ _ I _ θ => LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
    (∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) ∧
    (∀ (y : G) (J : Subgroup G), isNeighborOf y J →
      B ≤ Subgroup.normalizer (J : Set G) ∧
        LargeEvenMarkingLegacy J (fun lab _ _ I F θ =>
          LargeEvenHalfSplit p lab (Subgroup.center J = ⊥) ∨
            LargeEvenPrimeField p lab I F
              (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x))) ∧
    ∀ D K : Subgroup G, stdSub D K →
      (∃ (y : G) (J : Subgroup G), sHat y J ∧ neighbor y J D K) ∧
        ∀ d ∈ D, d ≠ 1 →
          Odd (Nat.card (⁅K, pPrimeCoreOf (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G))

theorem largeEvenStandardTypeOf_congr {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    {N N' : G → Subgroup G → Prop} {S S' : Subgroup G → Subgroup G → Prop}
    {H H' : G → Subgroup G → Prop} {R R' : G → Subgroup G → Subgroup G → Subgroup G → Prop}
    {O O' : Subgroup G → Subgroup G} (hN : ∀ y J, N y J ↔ N' y J) (hS : ∀ D K, S D K ↔ S' D K)
    (hH : ∀ y J, H y J ↔ H' y J) (hR : ∀ y J D K, R y J D K ↔ R' y J D K) (hO : O = O') :
    LargeEvenStandardTypeOf p B x L N S H R O ↔ LargeEvenStandardTypeOf p B x L N' S' H' R' O' := by
  obtain rfl : N = N' := funext₂ fun y J => propext (hN y J)
  obtain rfl : S = S' := funext₂ fun D K => propext (hS D K)
  obtain rfl : H = H' := funext₂ fun y J => propext (hH y J)
  obtain rfl : R = R' := funext fun y => funext fun J => funext₂ fun D K => propext (hR y J D K)
  subst hO
  rfl

end StandardType

end

end CFSG.Assembly
