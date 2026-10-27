module

public import CFSG.LieType.Steinberg.Minuscule.Form
public import CFSG.LieType.Steinberg.Minuscule.RootOps

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (R : Type*) [CommRing R]

@[expose] def cartanOp (D : MinData τ) (j : Fin τ.rank) : Module.End R (Fin D.d →₀ R) :=
  Finsupp.linearCombination R fun a => ((D.wt a j : ℤ) : R) • Finsupp.single a 1

theorem cartanOp_single (j : Fin τ.rank) (a : Fin D.d) :
    cartanOp R D j (Finsupp.single a 1) = ((D.wt a j : ℤ) : R) • Finsupp.single a 1 := by
  simp [cartanOp]

include hV in
theorem rootOp_single_comm_neg_single
    (i : Fin τ.rank) :
    D.rootOp R (Pi.single i 1) * D.rootOp R (-Pi.single i 1) -
      D.rootOp R (-Pi.single i 1) * D.rootOp R (Pi.single i 1) = cartanOp R D i := by
  refine ext_single fun a => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    hV.rootOp_neg_single_apply, hV.rootOp_single_apply, cartanOp_single]
  have hs := hV.wt_sRefl_self i a
  have hss := hV.sRefl_sRefl i a
  rcases hV.wt_mem a i with h | h | h
  · simp [h, hV.rootOp_neg_single_apply, hs, hss]
  · simp [h]
  · simp [h, hV.rootOp_single_apply, hs, hss]

include hV in
theorem cartanOp_comm_rootOp
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : Fin τ.rank) :
    cartanOp R D j * D.rootOp R γ - D.rootOp R γ * cartanOp R D j =
      ((toWeight γ j : ℤ) : R) • D.rootOp R γ := by
  refine ext_single fun a => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, cartanOp_single, map_smul,
    LinearMap.smul_apply]
  rcases hV.isSignedMap_rootOp (R := R) hγ a with h0 | ⟨b, hb, hs⟩
  · rw [h0]
    simp
  · have hw : D.wt b j = D.wt a j + toWeight γ j := by rw [hb, Pi.add_apply]
    rcases hs with hs | hs <;> rw [hs] <;> simp [cartanOp_single, hw, add_smul]

include hV in
theorem rootOp_single_mul_mul_single
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (i : Fin τ.rank)
    (hne : Pi.single i 1 + γ ≠ 0) :
    D.rootOp R (Pi.single i 1) * D.rootOp R γ * D.rootOp R (Pi.single i 1) = 0 := by
  obtain ⟨hroot, hcomm⟩ := hV.pairRel (R := R) (IsRoot.basis i) hγ hne
  by_cases hr : IsRoot τ (Pi.single i 1 + γ)
  · exact (hroot hr).2.1
  · rw [hcomm hr, mul_assoc, hV.rootOp_mul_self, mul_zero]

include hV in
theorem rootOp_neg_single_mul_mul_neg_single
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (i : Fin τ.rank) (hne : -Pi.single i 1 + γ ≠ 0) :
    D.rootOp R (-Pi.single i 1) * D.rootOp R γ * D.rootOp R (-Pi.single i 1) = 0 := by
  have hi : IsRoot τ (-Pi.single i 1) := by
    rw [← reflect_single_self]
    exact (IsRoot.basis i).reflect i
  obtain ⟨hroot, hcomm⟩ := hV.pairRel (R := R) hi hγ hne
  by_cases hr : IsRoot τ (-Pi.single i 1 + γ)
  · exact (hroot hr).2.1
  · rw [hcomm hr, mul_assoc, hV.rootOp_mul_self, mul_zero]

include hV in
theorem rootOp_single_mul_neg_single_mul_single
    (i : Fin τ.rank) :
    D.rootOp R (Pi.single i 1) * D.rootOp R (-Pi.single i 1) * D.rootOp R (Pi.single i 1) =
      D.rootOp R (Pi.single i 1) := by
  refine ext_single fun a => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hV.rootOp_single_apply]
  have hs := hV.wt_sRefl_self i a
  have hss := hV.sRefl_sRefl i a
  split_ifs with h
  · rw [hV.rootOp_neg_single_apply, hs, h, ite_eq_left (by norm_num), hss, hV.rootOp_single_apply,
      ite_eq_left h]
  · rw [map_zero, map_zero]

include hV in
theorem rootOp_neg_single_mul_single_mul_neg_single
    (i : Fin τ.rank) :
    D.rootOp R (-Pi.single i 1) * D.rootOp R (Pi.single i 1) * D.rootOp R (-Pi.single i 1) =
      D.rootOp R (-Pi.single i 1) := by
  refine ext_single fun a => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hV.rootOp_neg_single_apply]
  have hs := hV.wt_sRefl_self i a
  have hss := hV.sRefl_sRefl i a
  split_ifs with h
  · rw [hV.rootOp_single_apply, hs, h, ite_eq_left (by norm_num), hss, hV.rootOp_neg_single_apply,
      ite_eq_left h]
  · rw [map_zero, map_zero]

variable (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
include hpd

theorem string_of_add
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {i : Fin τ.rank}
    (hr : IsRoot τ (α + Pi.single i 1)) :
    toWeight α i = -1 ∧ ¬ IsRoot τ (α - Pi.single i 1) ∧ ¬ IsRoot τ (α + 2 • Pi.single i 1) := by
  have hne : α + Pi.single i 1 ≠ 0 := hr.ne_zero
  have hdot : toWeight α ⬝ᵥ Pi.single i 1 = toWeight α i := by simp
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · have e := form_add_self hpd α (Pi.single i 1)
    rw [form_self_root hpd hr, form_self_root hpd hα, form_self_root hpd (IsRoot.basis i),
      hdot] at e
    omega
  · have hγ : α - Pi.single i 1 + Pi.single i 1 ≠ 0 := by rw [sub_add_cancel]; exact hα.ne_zero
    have := eq_one_of_isRoot_nsmul_add_nsmul hpd h (IsRoot.basis i) hγ (i := 1) (j := 2)
      one_pos two_pos (by
        rw [one_smul, two_smul, ← add_assoc, sub_add_cancel]
        exact hr)
    omega
  · have := eq_one_of_isRoot_nsmul_add_nsmul hpd hα (IsRoot.basis i) hne (i := 1) (j := 2)
      one_pos two_pos (by rwa [one_smul])
    omega

end CFSG.TauCetiBridge.Minuscule
