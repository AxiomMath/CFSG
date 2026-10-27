module

public import CFSG.LieType.Chevalley.RelativeWeylTwist

public noncomputable section

namespace CFSG.Blueprint.Chevalley.TwistTag

open CFSG.LieType.Chevalley

@[expose] def foldedTag : TwistTag → Tag
  | E6 => .F4
  | D4 => .G2

@[expose] def orbit : (t : TwistTag) → Fin t.foldedTag.rank → Finset (Fin t.tag.rank)
  | E6 => (![{0, 5}, {2, 4}, {3}, {1}] : Fin 4 → Finset (Fin 6))
  | D4 => (![{0, 1, 3}, {2}] : Fin 2 → Finset (Fin 4))

@[expose] def orbitIndex : (t : TwistTag) → Fin t.tag.rank → Fin t.foldedTag.rank
  | E6 => (![0, 3, 1, 2, 1, 0] : Fin 6 → Fin 4)
  | D4 => (![0, 0, 1, 0] : Fin 4 → Fin 2)

@[expose] def orbitWord (t : TwistTag) (a : Fin t.foldedTag.rank) : List (Fin t.tag.rank) :=
  (List.finRange t.tag.rank).filter (· ∈ t.orbit a)

@[expose] def orbitSum (t : TwistTag) (a : Fin t.foldedTag.rank) : Fin t.tag.rank → ℤ :=
  ∑ i ∈ t.orbit a, Pi.single i 1

@[expose] def foldMap (t : TwistTag) : (Fin t.foldedTag.rank → ℤ) →ₗ[ℤ] Fin t.tag.rank → ℤ :=
  Fintype.linearCombination ℤ t.orbitSum

@[expose] def orbitReflection
    (t : TwistTag) (a : Fin t.foldedTag.rank) : WeylGroup t.tag :=
  (coxeterSystem t.tag).wordProd (t.orbitWord a)

@[expose] def fixedLattice
    (t : TwistTag) : Submodule ℤ (Fin t.tag.rank → ℤ) where
  carrier := {v | permLattice t.perm v = v}
  add_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    rw [permLattice_add, hu, hv]
  zero_mem' := rfl
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [permLattice_zsmul, hv]

variable (t : TwistTag)

theorem mem_orbit_iff {i : Fin t.tag.rank} {a : Fin t.foldedTag.rank} :
    i ∈ t.orbit a ↔ t.orbitIndex i = a := by
  revert i a
  cases t <;> decide

theorem mem_orbit_orbitIndex (i : Fin t.tag.rank) : i ∈ t.orbit (t.orbitIndex i) :=
  (t.mem_orbit_iff).2 rfl

theorem perm_pow_order : t.perm ^ t.order = 1 := by
  cases t <;> decide

theorem orbit_orbitIndex (i : Fin t.tag.rank) :
    t.orbit (t.orbitIndex i) = (Finset.range t.order).image fun k => (t.perm ^ k) i := by
  revert i
  cases t <;> decide

theorem mem_orbitWord {i : Fin t.tag.rank} {a : Fin t.foldedTag.rank} :
    i ∈ t.orbitWord a ↔ i ∈ t.orbit a := by
  simp [orbitWord]

theorem nodup_orbitWord (a : Fin t.foldedTag.rank) : (t.orbitWord a).Nodup :=
  (List.nodup_finRange _).filter _

theorem length_orbitWord (a : Fin t.foldedTag.rank) :
    (t.orbitWord a).length = (t.orbit a).card := by
  revert a
  cases t <;> decide

theorem orbitWord_eq_sort (a : Fin t.foldedTag.rank) :
    t.orbitWord a = (t.orbit a).sort (· ≤ ·) := by
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) ?_ (Finset.pairwise_sort _ _) ?_
  · exact ((List.pairwise_lt_finRange _).filter _).imp le_of_lt
  · refine (List.perm_ext_iff_of_nodup (t.nodup_orbitWord a) (Finset.sort_nodup _ _)).2
      fun i => ?_
    rw [mem_orbitWord, Finset.mem_sort]

theorem mem_fixedLattice
    {v : Fin t.tag.rank → ℤ} :
    v ∈ t.fixedLattice ↔ permLattice t.perm v = v :=
  Iff.rfl

theorem mem_fixedLattice_iff_forall
    {v : Fin t.tag.rank → ℤ} :
    v ∈ t.fixedLattice ↔ ∀ i, v (t.perm i) = v i := by
  rw [mem_fixedLattice, permLattice]
  constructor
  · intro h i
    have := congrFun h (t.perm i)
    simpa using this.symm
  · intro h
    ext j
    simpa using (h (t.perm.symm j)).symm

theorem orbitSum_apply (a : Fin t.foldedTag.rank) (i : Fin t.tag.rank) :
    t.orbitSum a i = if i ∈ t.orbit a then 1 else 0 := by
  simp only [orbitSum, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]

theorem orbitSum_eq (a : Fin t.foldedTag.rank) :
    t.orbitSum a = fun i => if t.orbitIndex i = a then 1 else 0 := by
  ext i
  simp only [orbitSum_apply, t.mem_orbit_iff]

theorem foldMap_apply (u : Fin t.foldedTag.rank → ℤ) :
    t.foldMap u = ∑ a, u a • t.orbitSum a :=
  Fintype.linearCombination_apply ℤ _ u

theorem foldMap_single (a : Fin t.foldedTag.rank) : t.foldMap (Pi.single a 1) = t.orbitSum a := by
  rw [foldMap, Fintype.linearCombination_apply_single, one_smul]

theorem foldMap_apply_apply (u : Fin t.foldedTag.rank → ℤ) (i : Fin t.tag.rank) :
    t.foldMap u i = u (t.orbitIndex i) := by
  rw [foldMap_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, orbitSum_eq, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

end CFSG.Blueprint.Chevalley.TwistTag

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem weylTwist_smul
    (t : TwistTag) (w : WeylGroup t.tag) (v : Fin t.tag.rank → ℤ) :
    weylTwist t w • v = permLattice t.perm (w • permLattice t.perm.symm v) := by
  rw [← weylTwist_smul_permLattice, permLattice_permLattice_symm]

theorem mem_relWeylTwist_iff_smul
    (t : TwistTag) {w : WeylGroup t.tag} :
    w ∈ relWeylTwist t ↔ ∀ v, w • permLattice t.perm v = permLattice t.perm (w • v) := by
  refine ⟨fun hw v => ?_, fun h => ?_⟩
  · conv_lhs => rw [← (mem_relWeylTwist t).1 hw]
    exact weylTwist_smul_permLattice t w v
  · refine (mem_relWeylTwist t).2
      (FaithfulSMul.eq_of_smul_eq_smul (α := Fin t.tag.rank → ℤ) fun v => ?_)
    rw [weylTwist_smul, ← h, permLattice_permLattice_symm]

end CFSG.LieType.Chevalley
