module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem RootSpace

variable {τ : Tag}

variable (τ) in
@[expose] def weylStabilizer
    (v : RootSpace τ) : Subgroup (WeylGroup τ) where
  carrier := {w | weylAct τ w v = v}
  one_mem' := by
    change weylAct τ 1 v = v
    rw [map_one, LinearIsometryEquiv.coe_one, id]
  mul_mem' {a b} ha hb := by
    change weylAct τ (a * b) v = v
    rw [weylAct_mul_apply, show weylAct τ b v = v from hb, show weylAct τ a v = v from ha]
  inv_mem' {a} ha := by
    change weylAct τ a⁻¹ v = v
    have ha' : weylAct τ a v = v := ha
    conv_lhs => rw [← ha']
    rw [← weylAct_mul_apply, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]

theorem mem_weylStabilizer
    {v : RootSpace τ} {w : WeylGroup τ} :
    w ∈ weylStabilizer τ v ↔ weylAct τ w v = v :=
  Iff.rfl

theorem inner_weylAct_left
    (w : WeylGroup τ) (x y : RootSpace τ) :
    inner ℝ (weylAct τ w x) y = inner ℝ x (weylAct τ w⁻¹ y) := by
  conv_lhs => rw [← show weylAct τ w (weylAct τ w⁻¹ y) = y by
    rw [← weylAct_mul_apply, mul_inv_cancel, map_one, LinearIsometryEquiv.coe_one, id]]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem weylAct_rootReflection
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (x : RootSpace τ) :
    weylAct τ (rootReflection α) x =
      x - (2 * inner ℝ (ofLattice α) x / inner ℝ (ofLattice α) (ofLattice α)) • ofLattice α := by
  obtain ⟨u, j, hu⟩ := isRoot_iff_exists_smul_single.1 hα
  have h1 : inner ℝ (ofLattice (Pi.single j 1 : Fin τ.rank → ℤ)) (weylAct τ u⁻¹ x) =
      inner ℝ (ofLattice α) x := by
    rw [← hu, ← weylAct_ofLattice, inner_weylAct_left]
  have h2 : inner ℝ (ofLattice (Pi.single j 1 : Fin τ.rank → ℤ))
      (ofLattice (Pi.single j 1 : Fin τ.rank → ℤ)) = inner ℝ (ofLattice α) (ofLattice α) := by
    rw [← hu, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map]
  rw [rootReflection_eq_conj hu, weylAct_mul_apply, weylAct_mul_apply, weylAct_simple_eq, h1, h2,
    map_sub, map_smul, ← weylAct_mul_apply, mul_inv_cancel, map_one, LinearIsometryEquiv.coe_one,
    id, weylAct_ofLattice, hu]

theorem IsRoot.inner_nonpos_of_mem_dominantCone
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hneg : height α < 0) {v : RootSpace τ} (hv : v ∈ dominantCone τ) :
    inner ℝ (ofLattice α) v ≤ 0 := by
  have h := IsRoot.inner_nonneg_of_mem_dominantCone (IsRoot.neg hα)
    (by rw [height_neg]; omega) hv
  rw [ofLattice_neg, inner_neg_left] at h
  linarith

theorem weylStabilizer_eq_closure_simple
    {v : RootSpace τ} (hv : v ∈ dominantCone τ) :
    weylStabilizer τ v = Subgroup.closure
      {s | ∃ i, s = simple τ i ∧ inner ℝ (ofLattice (Pi.single i 1)) v = 0} := by
  set S := {s | ∃ i, s = simple τ i ∧ inner ℝ (ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)) v = 0}
  have hS : ∀ i, inner ℝ (ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)) v = 0 →
      weylAct τ (simple τ i) v = v := by
    intro i hi
    rw [weylAct_simple_eq, hi, mul_zero, zero_div, zero_smul, sub_zero]
  refine le_antisymm ?_ ?_
  · intro w hw
    induction h : (coxeterSystem τ).length w using Nat.strong_induction_on generalizing w with
    | _ n ih =>
      by_cases hw1 : w = 1
      · rw [hw1]
        exact one_mem _
      obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one hw1
      have hroot := IsRoot.smul (isRoot_single τ i) w
      have hdesc : (coxeterSystem τ).IsRightDescent w i :=
        (smul_single_mem_negRoots_iff w i).1 ⟨hroot, hi⟩
      have hlen := (isRightDescent_iff_length w i).1 hdesc
      have hwv : weylAct τ w v = v := hw
      have hzero : inner ℝ (ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)) v = 0 := by
        have e : inner ℝ (ofLattice (w • (Pi.single i 1 : Fin τ.rank → ℤ))) v =
            inner ℝ (ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)) v := by
          conv_lhs => rw [← hwv]
          rw [← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map]
        have h1 := IsRoot.inner_nonpos_of_mem_dominantCone hroot hi hv
        have h2 := hv i
        rw [e] at h1
        linarith
      have hws : w * simple τ i ∈ weylStabilizer τ v := by
        change weylAct τ (w * simple τ i) v = v
        rw [weylAct_mul_apply, hS i hzero, hwv]
      have hmem := ih _ (by omega) hws rfl
      have hsi : simple τ i ∈ Subgroup.closure S := Subgroup.subset_closure ⟨i, rfl, hzero⟩
      have := mul_mem hmem hsi
      rwa [mul_assoc, simple_mul_simple_self, mul_one] at this
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl, hi⟩
    exact hS i hi

theorem exceptional_Lang_Weyl_chamber_point_stabilizers
    (τ : Tag) :
    (∃ c : ℝ, 0 < c ∧ ∀ x y : RootSpace τ,
      inner ℝ x y = c * ∑ i, ∑ j, x i * (τ.symmetrizedCartan i j : ℝ) * y j) ∧
    Finite (WeylGroup τ) ∧
    (∀ v : RootSpace τ, ∃ w : WeylGroup τ, weylAct τ w v ∈ dominantCone τ) ∧
    (∀ v ∈ dominantCone τ, weylStabilizer τ v = Subgroup.closure
      {s | ∃ i, s = simple τ i ∧ inner ℝ (ofLattice (Pi.single i 1)) v = 0}) ∧
    (∀ (α : Fin τ.rank → ℤ), IsRoot τ α → ∀ x : RootSpace τ, weylAct τ (rootReflection α) x =
      x - (2 * inner ℝ (ofLattice α) x / inner ℝ (ofLattice α) (ofLattice α)) • ofLattice α) ∧
    ∀ v : RootSpace τ, weylStabilizer τ v = Subgroup.closure
      {s | ∃ α, IsRoot τ α ∧ inner ℝ (ofLattice α) v = 0 ∧ s = rootReflection α} := by
  have htrans : ∀ v : RootSpace τ, ∃ w : WeylGroup τ, weylAct τ w v ∈ dominantCone τ := by
    intro v
    obtain ⟨w, y, hy, rfl⟩ := exists_weylAct_mem_dominantCone v
    refine ⟨w⁻¹, ?_⟩
    rw [← weylAct_mul_apply, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]
    exact hy
  refine ⟨exists_inner_eq_smul τ, inferInstance, htrans,
    fun v hv => weylStabilizer_eq_closure_simple hv, fun α hα x => weylAct_rootReflection hα x,
    fun v => ?_⟩
  set R := {s | ∃ α, IsRoot τ α ∧ inner ℝ (ofLattice α) v = 0 ∧ s = rootReflection α}
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hu⟩ := htrans v
    set v' := weylAct τ u v with hv'
    intro w hw
    have hw' : u * w * u⁻¹ ∈ weylStabilizer τ v' := by
      change weylAct τ (u * w * u⁻¹) v' = v'
      rw [hv', ← weylAct_mul_apply, inv_mul_cancel_right, weylAct_mul_apply,
        show weylAct τ w v = v from hw]
    rw [weylStabilizer_eq_closure_simple hu] at hw'
    have hle : Subgroup.closure
        {s | ∃ i, s = simple τ i ∧ inner ℝ (ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)) v' = 0} ≤
        (Subgroup.closure R).comap (MulAut.conj u⁻¹).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl, hi⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv]
      refine Subgroup.subset_closure ⟨u⁻¹ • Pi.single i 1, IsRoot.smul (isRoot_single τ i) u⁻¹,
        ?_, ?_⟩
      · rw [← weylAct_ofLattice, inner_weylAct_left, inv_inv]
        exact hi
      · have hsi : rootReflection (Pi.single i 1 : Fin τ.rank → ℤ) = simple τ i := by
          rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]
        rw [rootReflection_smul_root u⁻¹ (isRoot_single τ i), inv_inv, hsi]
    have h := hle hw'
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
    simpa [mul_assoc] using h
  · rw [Subgroup.closure_le]
    rintro _ ⟨α, hα, hαv, rfl⟩
    change weylAct τ (rootReflection α) v = v
    rw [weylAct_rootReflection hα, hαv, mul_zero, zero_div, zero_smul, sub_zero]

end CFSG.LieType.Chevalley
