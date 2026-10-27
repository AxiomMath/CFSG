module

public import CFSG.Blueprint.ChevalleyWeyl

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type*} [CommRing R]

theorem rootVec_single_eq (i : Fin τ.rank) :
    rootVec τ R (Pi.single i 1) = Finsupp.single (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩) 1 :=
  dite_eq_left (isRoot_single τ i)

theorem rootVec_neg_single_eq (i : Fin τ.rank) :
    rootVec τ R (-Pi.single i 1) =
      Finsupp.single (Sum.inr ⟨-Pi.single i 1, isRoot_neg_single τ i⟩) 1 :=
  dite_eq_left (isRoot_neg_single τ i)

theorem pi_single_ne_neg_pi_single (i : Fin τ.rank) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := fun h => by
  simpa using congrFun h i

theorem xOp_apply_hVec_self (i : Fin τ.rank) (c : R) :
    xOp τ R i c (hVec τ R i) = hVec τ R i + (2 * c) • rootVec τ R (Pi.single i 1) := by
  have h : xOp τ R i c (hVec τ R i) =
      hVec τ R i + (((τ.cartan i i).natAbs : R) * c) • rootVec τ R (Pi.single i 1) := by
    change xOp τ R i c (Finsupp.single (Sum.inl i) 1) = _
    rw [xOp, Finsupp.linearCombination_single, one_smul]
  rw [h, τ.cartan_self]
  norm_num

theorem xOp_apply_rootVec_single (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (Pi.single i 1)) = rootVec τ R (Pi.single i 1) := by
  rw [rootVec_single_eq, xOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

theorem xOp_apply_rootVec_neg_single (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (-Pi.single i 1)) =
      rootVec τ R (-Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1) := by
  rw [rootVec_neg_single_eq, xOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (pi_single_ne_neg_pi_single i).symm).trans (ite_eq_left rfl)

theorem yOp_apply_rootVec_single (i : Fin τ.rank) (d : R) :
    yOp τ R i d (rootVec τ R (Pi.single i 1)) =
      rootVec τ R (Pi.single i 1) + d • hVec τ R i + d ^ 2 • rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_single_eq, yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (pi_single_ne_neg_pi_single i)).trans (ite_eq_left rfl)

theorem xOp_mul_yOp_sub_apply_rootVec_single (i : Fin τ.rank) (c d : R) :
    (xOp τ R i c * yOp τ R i d - yOp τ R i d * xOp τ R i c) (rootVec τ R (Pi.single i 1)) =
      (2 * c * d + c ^ 2 * d ^ 2) • rootVec τ R (Pi.single i 1) + (c * d ^ 2) • hVec τ R i := by
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    xOp_apply_rootVec_single, yOp_apply_rootVec_single, map_add, map_add, map_smul, map_smul,
    xOp_apply_rootVec_single, xOp_apply_hVec_self, xOp_apply_rootVec_neg_single]
  simp only [smul_add, smul_smul, add_smul]
  module

theorem smul_rootVec_single_add_smul_hVec_apply (i : Fin τ.rank) (a b : R) :
    (a • rootVec τ R (Pi.single i 1) + b • hVec τ R i) (Sum.inl i) = b := by
  simp [rootVec_single_eq, hVec]

theorem opposite_simple_root_noncommutativity
    (τ : Tag) (K : Type*) [Field K] :
    (∀ (i : Fin τ.rank) (c d : K),
      (xOp τ K i c * yOp τ K i d - yOp τ K i d * xOp τ K i c) (rootVec τ K (Pi.single i 1)) =
        (2 * c * d + c ^ 2 * d ^ 2) • rootVec τ K (Pi.single i 1) + (c * d ^ 2) • hVec τ K i) ∧
    (∀ (i : Fin τ.rank) (c d : K), c ≠ 0 → d ≠ 0 →
      (2 * c * d + c ^ 2 * d ^ 2) • rootVec τ K (Pi.single i 1) + (c * d ^ 2) • hVec τ K i ≠ 0) ∧
    (∃ g h : adjointGroup τ K, g * h ≠ h * g) ∧
    Nontrivial (adjointGroup τ K ⧸ Subgroup.center (adjointGroup τ K)) := by
  have hne : ∀ (i : Fin τ.rank) (c d : K), c ≠ 0 → d ≠ 0 →
      (2 * c * d + c ^ 2 * d ^ 2) • rootVec τ K (Pi.single i 1) + (c * d ^ 2) • hVec τ K i ≠ 0 :=
    fun i c d hc hd h => by
      have := congrArg (fun v : RootModule τ K => v (Sum.inl i)) h
      simp only [smul_rootVec_single_add_smul_hVec_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      exact mul_ne_zero hc (pow_ne_zero 2 hd) this
  have hnc : ∃ g h : adjointGroup τ K, g * h ≠ h * g := by
    let i : Fin τ.rank := ⟨0, by cases τ <;> decide⟩
    refine ⟨⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩,
      ⟨yUnit τ K i 1, yUnit_mem_adjointGroup i 1⟩, fun h => ?_⟩
    have h' : xOp τ K i 1 * yOp τ K i 1 = yOp τ K i 1 * xOp τ K i 1 :=
      congrArg (fun g : adjointGroup τ K => ((g : ModGL τ K) : Module.End K (RootModule τ K))) h
    refine hne i 1 1 one_ne_zero one_ne_zero ?_
    rw [← xOp_mul_yOp_sub_apply_rootVec_single, h']
    simp
  refine ⟨xOp_mul_yOp_sub_apply_rootVec_single, hne, hnc, ?_⟩
  obtain ⟨g, h, hgh⟩ := hnc
  refine ⟨⟨(g : adjointGroup τ K ⧸ Subgroup.center (adjointGroup τ K)), 1, fun h1 => hgh ?_⟩⟩
  have hg : g ∈ Subgroup.center (adjointGroup τ K) := (QuotientGroup.eq_one_iff g).1 h1
  exact (Subgroup.mem_center_iff.1 hg h).symm

end CFSG.LieType.Chevalley
