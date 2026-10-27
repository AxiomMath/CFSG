module

public import CFSG.LieType.Chevalley.Covering
public import CFSG.LieType.Chevalley.WeylRoots
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable (τ : Tag)

abbrev Root : Type := {v : Fin τ.rank → ℤ // IsRoot τ v}

@[expose] def simpleRoot (i : Fin τ.rank) : Root τ := ⟨Pi.single i 1, isRoot_single τ i⟩

@[expose] noncomputable def rootCombinatorics :
    RootCombinatorics (WeylGroup τ) (Root τ) (Fin τ.rank) where
  neg α := -α
  pos α := 0 < height α.1
  simple := simpleRoot τ
  refl := simple τ
  pos_or_pos_neg α := by
    rcases IsRoot.height_pos_or_neg α.2 with h | h
    · exact .inl h
    · right
      change 0 < height (-α.1)
      rw [height_neg]
      omega
  not_pos_and_pos_neg α := by
    rintro ⟨h1, h2⟩
    change 0 < height (-α.1) at h2
    rw [height_neg] at h2
    omega
  smul_neg w α := smul_neg_root w α
  pos_simple i := by
    change 0 < height (Pi.single i 1 : Fin τ.rank → ℤ)
    rw [height_single]
    exact one_pos
  refl_mul_self i := (coxeterSystem τ).simple_mul_simple_self i
  refl_simple i := by
    apply Subtype.ext
    change simple τ i • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1
    rw [simple_smul, reflect_single_self]
  pos_refl i α hα hne := by
    change 0 < height (simple τ i • α.1)
    rw [simple_smul]
    exact height_reflect_pos α.2 hα fun h => hne (Subtype.ext h)

variable {τ}

@[simp] theorem rootCombinatorics_pos (α : Root τ) :
    (rootCombinatorics τ).pos α ↔ 0 < height α.1 :=
  Iff.rfl

@[simp] theorem rootCombinatorics_neg (α : Root τ) : (rootCombinatorics τ).neg α = -α :=
  rfl

@[simp] theorem rootCombinatorics_simple (i : Fin τ.rank) :
    (rootCombinatorics τ).simple i = simpleRoot τ i :=
  rfl

@[simp] theorem rootCombinatorics_refl (i : Fin τ.rank) :
    (rootCombinatorics τ).refl i = simple τ i :=
  rfl

theorem rootCombinatorics_eq_one {w : WeylGroup τ}
    (h : ∀ i, (rootCombinatorics τ).pos (w • (rootCombinatorics τ).simple i)) : w = 1 :=
  eq_one_of_forall_height_pos fun i => h i

theorem closure_range_simple : Subgroup.closure (Set.range (simple τ)) = ⊤ :=
  (coxeterSystem τ).subgroup_closure_range_simple

end CFSG.LieType.Chevalley
