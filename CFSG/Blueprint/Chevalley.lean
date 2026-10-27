module

public import Mathlib

public noncomputable section

namespace CFSG.Blueprint.Chevalley

inductive Tag
  | G2 | F4 | D4 | E6 | E7 | E8
  deriving DecidableEq, Repr

namespace Tag

@[expose] def rank : Tag → ℕ
  | G2 => 2
  | F4 => 4
  | D4 => 4
  | E6 => 6
  | E7 => 7
  | E8 => 8

@[expose] def cartanE (r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j =>
    if i = j then 2
    else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨ (i.val = 1 ∧ j.val = 3) ∨
        (i.val = 3 ∧ j.val = 1) ∨ (2 ≤ i.val ∧ j.val = i.val + 1) ∨
        (2 ≤ j.val ∧ i.val = j.val + 1) then -1
    else 0

@[expose] def cartan : (τ : Tag) → Matrix (Fin τ.rank) (Fin τ.rank) ℤ
  | G2 => !![2, -1; -3, 2]
  | F4 => !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]
  | D4 => !![2, 0, -1, 0; 0, 2, -1, 0; -1, -1, 2, -1; 0, 0, -1, 2]
  | E6 => cartanE 6
  | E7 => cartanE 7
  | E8 => cartanE 8

@[expose] def symmetrizer : (τ : Tag) → Matrix (Fin τ.rank) (Fin τ.rank) ℤ
  | G2 => Matrix.diagonal ![3, 1]
  | F4 => Matrix.diagonal ![2, 2, 1, 1]
  | D4 => 1
  | E6 => 1
  | E7 => 1
  | E8 => 1

@[expose] def symmetrizedCartan (τ : Tag) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  τ.symmetrizer * τ.cartan

end Tag

@[expose] def reflect (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  v - (∑ j, τ.cartan i j * v j) • Pi.single i 1

inductive IsRoot (τ : Tag) : (Fin τ.rank → ℤ) → Prop
  | basis (j : Fin τ.rank) : IsRoot τ (Pi.single j 1)
  | reflect (i : Fin τ.rank) {v : Fin τ.rank → ℤ} : IsRoot τ v → IsRoot τ (reflect τ i v)

@[expose] def height {τ : Tag} (v : Fin τ.rank → ℤ) : ℤ :=
  ∑ j, v j

abbrev Label (τ : Tag) : Type :=
  Fin τ.rank ⊕ {v : Fin τ.rank → ℤ // IsRoot τ v}

abbrev RootModule (τ : Tag) (R : Type*) [CommRing R] : Type _ :=
  Label τ →₀ R

@[expose] def Label.weight {τ : Tag} : Label τ → ℤ
  | .inl _ => 0
  | .inr α => height α.1

@[expose] def Label.Precedes {τ : Tag} (a b : Label τ) : Prop :=
  b.weight < a.weight ∨
    (a.weight = b.weight ∧
      match a, b with
      | .inl i, .inl j => i < j
      | .inr α, .inr β => toLex α.1 < toLex β.1
      | _, _ => False)

variable (τ : Tag) (R : Type*) [CommRing R]

@[expose] def hVec (i : Fin τ.rank) : RootModule τ R :=
  Finsupp.single (Sum.inl i) 1

open Classical in
@[expose] def rootVec (β : Fin τ.rank → ℤ) : RootModule τ R :=
  if h : IsRoot τ β then Finsupp.single (Sum.inr ⟨β, h⟩) 1 else 0

@[expose] def stringUp (i : Fin τ.rank) (α : Fin τ.rank → ℤ) : ℕ :=
  sSup {k : ℕ | IsRoot τ (α + (k : ℤ) • Pi.single i 1)}

@[expose] def stringDown (i : Fin τ.rank) (α : Fin τ.rank → ℤ) : ℕ :=
  sSup {k : ℕ | IsRoot τ (α - (k : ℤ) • Pi.single i 1)}

open Classical in
@[expose] def xOp (i : Fin τ.rank) (c : R) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1)
    | .inr α =>
      if α.1 = Pi.single i 1 then Finsupp.single (Sum.inr α) 1
      else if α.1 = -Pi.single i 1 then
        Finsupp.single (Sum.inr α) 1 + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringUp τ i α.1 + 1),
          (((stringDown τ i α.1 + k).choose k : R) * c ^ k) •
            rootVec τ R (α.1 + (k : ℤ) • Pi.single i 1)

open Classical in
@[expose] def yOp (i : Fin τ.rank) (c : R) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1)
    | .inr α =>
      if α.1 = -Pi.single i 1 then Finsupp.single (Sum.inr α) 1
      else if α.1 = Pi.single i 1 then
        Finsupp.single (Sum.inr α) 1 + c • hVec τ R i + c ^ 2 • rootVec τ R (-Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringDown τ i α.1 + 1),
          (((stringUp τ i α.1 + k).choose k : R) * c ^ k) •
            rootVec τ R (α.1 - (k : ℤ) • Pi.single i 1)

abbrev ModGL (K : Type*) [Field K] : Type _ :=
  LinearMap.GeneralLinearGroup K (RootModule τ K)

@[expose] def adjointGroup (K : Type*) [Field K] : Subgroup (ModGL τ K) :=
  Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : K),
    (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
      (g : Module.End K (RootModule τ K)) = yOp τ K i c}

inductive TwistTag
  | E6 | D4
  deriving DecidableEq, Repr

namespace TwistTag

@[expose] def tag : TwistTag → Tag
  | E6 => .E6
  | D4 => .D4

@[expose] def perm : (t : TwistTag) → Equiv.Perm (Fin t.tag.rank)
  | E6 => (Equiv.swap 0 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))
  | D4 => (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4))

@[expose] def order : TwistTag → ℕ
  | E6 => 2
  | D4 => 3

end TwistTag

@[expose] def permLattice {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    Fin τ.rank → ℤ :=
  v ∘ π.symm

theorem permLattice_single {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (i : Fin τ.rank) :
    permLattice π (Pi.single i 1) = Pi.single (π i) 1 := by
  ext j
  simp only [permLattice, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem permLattice_reflect {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    permLattice π (reflect τ i v) = reflect τ (π i) (permLattice π v) := by
  have hsum : ∑ j, τ.cartan (π i) j * (v ∘ π.symm) j = ∑ j, τ.cartan i j * v j := by
    rw [← Equiv.sum_comp π]
    simp [hπ]
  simp only [reflect, permLattice, hsum]
  ext j
  simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Equiv.symm_apply_eq]

theorem IsRoot.permLattice {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) :
    IsRoot τ (Chevalley.permLattice π v) := by
  induction hv with
  | basis j => rw [permLattice_single]; exact .basis _
  | reflect i _ ih => rw [permLattice_reflect hπ]; exact .reflect _ ih

theorem cartan_perm_symm {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (i j : Fin τ.rank) :
    τ.cartan (π.symm i) (π.symm j) = τ.cartan i j := by
  simpa using (hπ (π.symm i) (π.symm j)).symm

theorem TwistTag.cartan_submatrix (t : TwistTag) :
    t.tag.cartan.submatrix t.perm t.perm = t.tag.cartan := by
  cases t <;> decide

theorem TwistTag.cartan_perm (t : TwistTag) (i j : Fin t.tag.rank) :
    t.tag.cartan (t.perm i) (t.perm j) = t.tag.cartan i j :=
  congrFun (congrFun t.cartan_submatrix i) j

@[expose] def labelPerm {τ : Tag} (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) : Label τ ≃ Label τ where
  toFun
    | .inl i => .inl (π i)
    | .inr α => .inr ⟨permLattice π α.1, α.2.permLattice hπ⟩
  invFun
    | .inl i => .inl (π.symm i)
    | .inr α => .inr ⟨permLattice π.symm α.1, α.2.permLattice (cartan_perm_symm hπ)⟩
  left_inv := by
    rintro (i | ⟨α, hα⟩)
    · simp
    · simp only [Sum.inr.injEq, Subtype.mk.injEq]
      ext j; simp [permLattice]
  right_inv := by
    rintro (i | ⟨α, hα⟩)
    · simp
    · simp only [Sum.inr.injEq, Subtype.mk.injEq]
      ext j; simp [permLattice]

@[expose] def diagramMap (t : TwistTag) (K : Type*) [Field K] : ModGL t.tag K :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (Finsupp.domLCongr (labelPerm t.perm t.cartan_perm))

theorem diagramMap_hVec (t : TwistTag) (K : Type*) [Field K] (i : Fin t.tag.rank) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) (hVec t.tag K i) =
      hVec t.tag K (t.perm i) := by
  simp [diagramMap, hVec, labelPerm]

theorem diagramMap_rootVec (t : TwistTag) (K : Type*) [Field K] (α : Fin t.tag.rank → ℤ)
    (hα : IsRoot t.tag α) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) (rootVec t.tag K α) =
      rootVec t.tag K (permLattice t.perm α) := by
  simp [diagramMap, rootVec, hα, hα.permLattice t.cartan_perm, labelPerm]

variable {τ R}

@[expose] def entrywise (σ : R →+* R) (A : Module.End R (RootModule τ R)) :
    Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b => Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1))

theorem entrywise_single (σ : R →+* R) (A : Module.End R (RootModule τ R)) (b : Label τ) :
    entrywise σ A (Finsupp.single b 1) =
      Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1)) := by
  simp [entrywise]

theorem entrywise_apply_mapRange (σ : R →+* R) (A : Module.End R (RootModule τ R))
    (x : RootModule τ R) :
    entrywise σ A (Finsupp.mapRange σ σ.map_zero x) =
      Finsupp.mapRange σ σ.map_zero (A x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (map_add σ), map_add, hx, hy, map_add,
      Finsupp.mapRange_add (map_add σ)]
  | single b r =>
    have h1 : Finsupp.mapRange σ σ.map_zero (Finsupp.single b r) =
        σ r • Finsupp.single b (1 : R) := by
      simp
    have h2 : Finsupp.single b r = r • Finsupp.single b (1 : R) := by simp
    rw [h1, map_smul, entrywise_single, h2, map_smul]
    ext l
    simp

theorem entrywise_one (σ : R →+* R) :
    entrywise σ (1 : Module.End R (RootModule τ R)) = 1 := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp [entrywise]

theorem entrywise_mul (σ : R →+* R) (A B : Module.End R (RootModule τ R)) :
    entrywise σ (A * B) = entrywise σ A * entrywise σ B := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rw [entrywise_single, entrywise_single, entrywise_apply_mapRange, Module.End.mul_apply]

@[expose] def entrywiseHom (σ : R →+* R) :
    Module.End R (RootModule τ R) →* Module.End R (RootModule τ R) where
  toFun := entrywise σ
  map_one' := entrywise_one σ
  map_mul' := entrywise_mul σ

@[expose] def twistHom (t : TwistTag) (K : Type*) [Field K] (σ : K →+* K) :
    ModGL t.tag K →* ModGL t.tag K :=
  (MulAut.conj (diagramMap t K)).toMonoidHom.comp (Units.map (entrywiseHom σ))

theorem coe_twistHom (t : TwistTag) (K : Type*) [Field K] (σ : K →+* K) (g : ModGL t.tag K) :
    ((twistHom t K σ g : ModGL t.tag K) : Module.End K (RootModule t.tag K)) =
      (diagramMap t K : Module.End K (RootModule t.tag K)) *
        entrywise σ (g : Module.End K (RootModule t.tag K)) *
          ((diagramMap t K)⁻¹ : ModGL t.tag K) := by
  simp [twistHom, MulAut.conj_apply, entrywiseHom]

end CFSG.Blueprint.Chevalley
