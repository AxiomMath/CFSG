module

public import CFSG.Open.FusionDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank

section Conjugation

variable {G : Type*} [Group G]

@[expose] def conjSubgroup (g : G) (T : Subgroup G) : Subgroup G :=
  T.map (MulAut.conj g).toMonoidHom

theorem mem_conjSubgroup {g : G} {T : Subgroup G} {x : G} :
    x ∈ conjSubgroup g T ↔ g⁻¹ * x * g ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

@[expose] def WeaklyClosedIn (T H : Subgroup G) : Prop :=
  T ≤ H ∧ ∀ g : G, conjSubgroup g T ≤ H → conjSubgroup g T = T

@[expose] def IsWC (T : Subgroup G) : Prop :=
  IsElemAbelian 2 T ∧
    ∀ t ∈ T, t ≠ 1 → WeaklyClosedIn T (Subgroup.centralizer ({t} : Set G))

@[expose] def IsTI (T : Subgroup G) : Prop :=
  ∀ g : G, T ⊓ conjSubgroup g T = ⊥ ∨ T ⊓ conjSubgroup g T = T

@[expose] def CorBHyp (T : Subgroup G) : Prop :=
  IsElemAbelian 2 T ∧ IsTI T ∧
    ∀ g : G, (∀ x ∈ T, ∀ y ∈ conjSubgroup g T, Commute x y) ↔ conjSubgroup g T = T

end Conjugation

section Targets

@[expose] def ZStarCase (H : Type*) [Group H] : Prop :=
  fusionZStar H = ⊤

@[expose] def ListGroup (X : Type) [Group X] : Prop :=
  (∃ m s : ℕ, 2 ≤ m ∧ 1 ≤ s ∧ StatedClassicalModel X .PSL m 2 s) ∨
  (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel X .PSU 3 2 s) ∨
  (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel X .twistedB2 0 2 s) ∨
  (∃ k : ℕ, 6 ≤ k ∧ k ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin k))) ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic X .M22 ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic X .M23 ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic X .M24

@[expose] def IsCoveringOfList (H : Type) [Group H] : Prop :=
  commutator H = ⊤ ∧ ∃ Z : Subgroup H, Z ≤ Subgroup.center H ∧
    ∃ _ : Z.Normal, ListGroup (H ⧸ Z)

end Targets

end CFSG.CGT.Timmesfeld75
