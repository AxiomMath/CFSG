module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacCheck

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

section Defs

variable {τ : Tag}

@[expose] def eV (θ : Fin τ.rank → ℤ) : Option (Fin τ.rank) → Fin τ.rank → ℤ
  | none => -θ
  | some j => Pi.single j 1

@[expose] def zT (θ μ : Fin τ.rank → ℤ) : Option (Fin τ.rank) → Prop
  | none => θ ⬝ᵥ μ = ((3 : ℕ) : ℤ)
  | some j => μ j = 0

instance (θ μ : Fin τ.rank → ℤ) (x : Option (Fin τ.rank)) : Decidable (zT θ μ x) :=
  match x with
  | none => inferInstanceAs (Decidable (θ ⬝ᵥ μ = ((3 : ℕ) : ℤ)))
  | some j => inferInstanceAs (Decidable (μ j = 0))

@[expose] def adjL (E : List (Option (Fin τ.rank) × Option (Fin τ.rank)))
    (x y : Option (Fin τ.rank)) : Prop :=
  (x, y) ∈ E ∨ (y, x) ∈ E

instance (E : List (Option (Fin τ.rank) × Option (Fin τ.rank))) (x y : Option (Fin τ.rank)) :
    Decidable (adjL E x y) :=
  inferInstanceAs (Decidable ((x, y) ∈ E ∨ (y, x) ∈ E))

@[expose] def nT (θ μ : Fin τ.rank → ℤ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank)))
    (x y : Option (Fin τ.rank)) : Prop :=
  zT θ μ x ∧ zT θ μ y ∧ adjL E x y

instance (θ μ : Fin τ.rank → ℤ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank)))
    (x y : Option (Fin τ.rank)) : Decidable (nT θ μ E x y) :=
  inferInstanceAs (Decidable (zT θ μ x ∧ zT θ μ y ∧ adjL E x y))

@[expose] def Iso (θ μ : Fin τ.rank → ℤ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank)))
    (x : Option (Fin τ.rank)) : Prop :=
  ∀ y, ¬ nT θ μ E x y

instance (θ μ : Fin τ.rank → ℤ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank)))
    (x : Option (Fin τ.rank)) : Decidable (Iso θ μ E x) :=
  inferInstanceAs (Decidable (∀ y, ¬ nT θ μ E x y))

@[expose] def Q1 (θ μ : Fin τ.rank → ℤ) (E G : List (Option (Fin τ.rank) × Option (Fin τ.rank))) :
    Prop :=
  ∀ x, zT θ μ x → Iso θ μ E x ∨ (∃ y, nT θ μ E x y ∧ (x, y) ∈ G) ∨
    (∃ y, nT θ μ E x y ∧ ∃ z, nT θ μ E y z ∧ (y, z) ∈ G)

instance (θ μ : Fin τ.rank → ℤ) (E G : List (Option (Fin τ.rank) × Option (Fin τ.rank))) :
    Decidable (Q1 θ μ E G) :=
  inferInstanceAs (Decidable (∀ x, zT θ μ x → Iso θ μ E x ∨ (∃ y, nT θ μ E x y ∧ (x, y) ∈ G) ∨
    (∃ y, nT θ μ E x y ∧ ∃ z, nT θ μ E y z ∧ (y, z) ∈ G)))

@[expose] def Q2 (θ μ : Fin τ.rank → ℤ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank))) :
    Prop :=
  ∀ x, zT θ μ x → ¬ Iso θ μ E x

instance (θ μ : Fin τ.rank → ℤ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank))) :
    Decidable (Q2 θ μ E) :=
  inferInstanceAs (Decidable (∀ x, zT θ μ x → ¬ Iso θ μ E x))

@[expose] def Q3 (θ μ : Fin τ.rank → ℤ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank))) :
    Prop :=
  ∀ x x', zT θ μ x → zT θ μ x' → Iso θ μ E x → Iso θ μ E x' → x = x'

instance (θ μ : Fin τ.rank → ℤ) (E : List (Option (Fin τ.rank) × Option (Fin τ.rank))) :
    Decidable (Q3 θ μ E) :=
  inferInstanceAs (Decidable (∀ x x', zT θ μ x → zT θ μ x' → Iso θ μ E x → Iso θ μ E x' → x = x'))

@[expose] def BoxAll (θ : Fin τ.rank → ℤ) (bnd : Fin τ.rank → ℕ)
    (P : (Fin τ.rank → ℤ) → Prop) : Prop :=
  ∀ m : (j : Fin τ.rank) → Fin (bnd j + 1), θ ⬝ᵥ (fun j => ((m j : ℕ) : ℤ)) ≤ ((3 : ℕ) : ℤ) →
    P (fun j => ((m j : ℕ) : ℤ))

instance (θ : Fin τ.rank → ℤ) (bnd : Fin τ.rank → ℕ) (P : (Fin τ.rank → ℤ) → Prop)
    [DecidablePred P] : Decidable (BoxAll θ bnd P) :=
  inferInstanceAs (Decidable (∀ m : (j : Fin τ.rank) → Fin (bnd j + 1),
    θ ⬝ᵥ (fun j => ((m j : ℕ) : ℤ)) ≤ ((3 : ℕ) : ℤ) → P (fun j => ((m j : ℕ) : ℤ))))

end Defs

@[expose] def A2T (τ : Tag) (a b : Fin τ.rank → ℤ) : Prop :=
  List.ofFn (a + b) ∈ τ.artifactRoots ∧ List.ofFn (a - b) ∉ τ.artifactRoots ∧
    List.ofFn ((2 : ℤ) • a + b) ∉ τ.artifactRoots ∧
    List.ofFn (a + (2 : ℤ) • b) ∉ τ.artifactRoots

instance (τ : Tag) (a b : Fin τ.rank → ℤ) : Decidable (A2T τ a b) :=
  inferInstanceAs (Decidable (List.ofFn (a + b) ∈ τ.artifactRoots ∧
    List.ofFn (a - b) ∉ τ.artifactRoots ∧ List.ofFn ((2 : ℤ) • a + b) ∉ τ.artifactRoots ∧
    List.ofFn (a + (2 : ℤ) • b) ∉ τ.artifactRoots))

@[expose] def f4θ : Fin Tag.F4.rank → ℤ := ![2, 3, 4, 2]

@[expose] def f4bnd : Fin Tag.F4.rank → ℕ := ![1, 1, 0, 1]

@[expose] def f4ERaw : List (Option (Fin 4) × Option (Fin 4)) :=
  [(none, some 0), (some 0, some 1), (some 1, some 2), (some 2, some 3)]

@[expose] def f4E : List (Option (Fin Tag.F4.rank) × Option (Fin Tag.F4.rank)) := f4ERaw

@[expose] def f4GRaw : List (Option (Fin 4) × Option (Fin 4)) :=
  [(none, some 0), (some 0, none), (some 0, some 1), (some 1, some 0), (some 2, some 3),
    (some 3, some 2)]

@[expose] def f4G : List (Option (Fin Tag.F4.rank) × Option (Fin Tag.F4.rank)) := f4GRaw

theorem f4_hbnd : ∀ j : Fin Tag.F4.rank, 3 < f4θ j * (((f4bnd j : ℕ) : ℤ) + 1) := by
  decide +kernel

theorem f4_hadj : ∀ x y : Option (Fin Tag.F4.rank),
    (x ≠ y ∧ iform (τ := Tag.F4) (eV f4θ x) (eV f4θ y) ≠ 0) ↔ adjL f4E x y := by
  decide +kernel

theorem f4_hdist : ∀ x y : Option (Fin Tag.F4.rank), x ≠ y →
    eV f4θ x ≠ eV f4θ y ∧ eV f4θ x ≠ -eV f4θ y := by
  decide +kernel

theorem f4_hG : ∀ x y : Option (Fin Tag.F4.rank), (x, y) ∈ f4G →
    A2T Tag.F4 (eV f4θ x) (eV f4θ y) := by
  decide +kernel

theorem f4_Q1 : BoxAll f4θ f4bnd fun μ => Q1 f4θ μ f4E f4G := by
  decide +kernel

theorem f4_Q2 : BoxAll f4θ f4bnd fun μ => Q2 f4θ μ f4E := by
  decide +kernel

@[expose] def e6θ : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def e6bnd : Fin Tag.E6.rank → ℕ := ![3, 1, 1, 1, 1, 3]

@[expose] def e6ERaw : List (Option (Fin 6) × Option (Fin 6)) :=
  [(none, some 1), (some 0, some 2), (some 1, some 3), (some 2, some 3), (some 3, some 4),
    (some 4, some 5)]

@[expose] def e6E : List (Option (Fin Tag.E6.rank) × Option (Fin Tag.E6.rank)) := e6ERaw

@[expose] def e6G : List (Option (Fin Tag.E6.rank) × Option (Fin Tag.E6.rank)) :=
  e6E ++ e6E.map Prod.swap

theorem e6_hbnd : ∀ j : Fin Tag.E6.rank, 3 < e6θ j * (((e6bnd j : ℕ) : ℤ) + 1) := by
  decide +kernel

theorem e6_hadj : ∀ x y : Option (Fin Tag.E6.rank),
    (x ≠ y ∧ iform (τ := Tag.E6) (eV e6θ x) (eV e6θ y) ≠ 0) ↔ adjL e6E x y := by
  decide +kernel

theorem e6_hdist : ∀ x y : Option (Fin Tag.E6.rank), x ≠ y →
    eV e6θ x ≠ eV e6θ y ∧ eV e6θ x ≠ -eV e6θ y := by
  decide +kernel

theorem e6_hG : ∀ x y : Option (Fin Tag.E6.rank), (x, y) ∈ e6G →
    A2T Tag.E6 (eV e6θ x) (eV e6θ y) := by
  decide +kernel

theorem e6_Q1 : BoxAll e6θ e6bnd fun μ => Q1 e6θ μ e6E e6G := by
  decide +kernel

theorem e6_Q3 : BoxAll e6θ e6bnd fun μ => Q3 e6θ μ e6E := by
  decide +kernel

@[expose] def e7θ : Fin Tag.E7.rank → ℤ := ![2, 2, 3, 4, 3, 2, 1]

@[expose] def e7bnd : Fin Tag.E7.rank → ℕ := ![1, 1, 1, 0, 1, 1, 3]

@[expose] def e7ERaw : List (Option (Fin 7) × Option (Fin 7)) :=
  [(none, some 0), (some 0, some 2), (some 1, some 3), (some 2, some 3), (some 3, some 4),
    (some 4, some 5), (some 5, some 6)]

@[expose] def e7E : List (Option (Fin Tag.E7.rank) × Option (Fin Tag.E7.rank)) := e7ERaw

@[expose] def e7G : List (Option (Fin Tag.E7.rank) × Option (Fin Tag.E7.rank)) :=
  e7E ++ e7E.map Prod.swap

theorem e7_hbnd : ∀ j : Fin Tag.E7.rank, 3 < e7θ j * (((e7bnd j : ℕ) : ℤ) + 1) := by
  decide +kernel

theorem e7_hadj : ∀ x y : Option (Fin Tag.E7.rank),
    (x ≠ y ∧ iform (τ := Tag.E7) (eV e7θ x) (eV e7θ y) ≠ 0) ↔ adjL e7E x y := by
  decide +kernel

theorem e7_hdist : ∀ x y : Option (Fin Tag.E7.rank), x ≠ y →
    eV e7θ x ≠ eV e7θ y ∧ eV e7θ x ≠ -eV e7θ y := by
  decide +kernel

theorem e7_hG : ∀ x y : Option (Fin Tag.E7.rank), (x, y) ∈ e7G →
    A2T Tag.E7 (eV e7θ x) (eV e7θ y) := by
  decide +kernel

theorem e7_Q1 : BoxAll e7θ e7bnd fun μ => Q1 e7θ μ e7E e7G := by
  decide +kernel

theorem e7_Q3 : BoxAll e7θ e7bnd fun μ => Q3 e7θ μ e7E := by
  decide +kernel

@[expose] def e8θ : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def e8bnd : Fin Tag.E8.rank → ℕ := ![1, 1, 0, 0, 0, 0, 1, 1]

@[expose] def e8ERaw : List (Option (Fin 8) × Option (Fin 8)) :=
  [(none, some 7), (some 0, some 2), (some 1, some 3), (some 2, some 3), (some 3, some 4),
    (some 4, some 5), (some 5, some 6), (some 6, some 7)]

@[expose] def e8E : List (Option (Fin Tag.E8.rank) × Option (Fin Tag.E8.rank)) := e8ERaw

@[expose] def e8G : List (Option (Fin Tag.E8.rank) × Option (Fin Tag.E8.rank)) :=
  e8E ++ e8E.map Prod.swap

theorem e8_hbnd : ∀ j : Fin Tag.E8.rank, 3 < e8θ j * (((e8bnd j : ℕ) : ℤ) + 1) := by
  decide +kernel

theorem e8_hadj : ∀ x y : Option (Fin Tag.E8.rank),
    (x ≠ y ∧ iform (τ := Tag.E8) (eV e8θ x) (eV e8θ y) ≠ 0) ↔ adjL e8E x y := by
  decide +kernel

theorem e8_hdist : ∀ x y : Option (Fin Tag.E8.rank), x ≠ y →
    eV e8θ x ≠ eV e8θ y ∧ eV e8θ x ≠ -eV e8θ y := by
  decide +kernel

theorem e8_hG : ∀ x y : Option (Fin Tag.E8.rank), (x, y) ∈ e8G →
    A2T Tag.E8 (eV e8θ x) (eV e8θ y) := by
  decide +kernel

theorem e8_Q1 : BoxAll e8θ e8bnd fun μ => Q1 e8θ μ e8E e8G := by
  decide +kernel

theorem e8_Q2 : BoxAll e8θ e8bnd fun μ => Q2 e8θ μ e8E := by
  decide +kernel

end CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacCheck
