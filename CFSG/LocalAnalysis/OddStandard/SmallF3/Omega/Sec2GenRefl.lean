module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def reflOf (Q : QuadraticForm (ZMod 3) V) (u : V) (hu : Q u ≠ 0) :
    OGroup Q :=
  letI : Invertible (Q u) := invertibleOfNonzero hu
  TauCeti.QuadraticMap.reflectionOrthogonal Q u

theorem reflOf_eq (u : V) (hu : Q u ≠ 0) [Invertible (Q u)] :
    reflOf Q u hu = TauCeti.QuadraticMap.reflectionOrthogonal Q u := by
  unfold reflOf
  congr 1
  exact Subsingleton.elim _ _

theorem reflOf_mul_self (u : V) (hu : Q u ≠ 0) : reflOf Q u hu * reflOf Q u hu = 1 := by
  letI : Invertible (Q u) := invertibleOfNonzero hu
  rw [reflOf_eq u hu]
  exact TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q u

theorem reflOf_inv (u : V) (hu : Q u ≠ 0) : (reflOf Q u hu)⁻¹ = reflOf Q u hu :=
  inv_eq_of_mul_eq_one_left (reflOf_mul_self u hu)

theorem map_ogroup_apply (g : OGroup Q) (u : V) : Q ((g : V ≃ₗ[ZMod 3] V) u) = Q u :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2 u

theorem mul_reflOf_mul_inv (g : OGroup Q) (u : V) (hu : Q u ≠ 0) :
    g * reflOf Q u hu * g⁻¹ =
      reflOf Q ((g : V ≃ₗ[ZMod 3] V) u) (by rw [map_ogroup_apply]; exact hu) := by
  letI : Invertible (Q u) := invertibleOfNonzero hu
  letI : Invertible (Q ((g : V ≃ₗ[ZMod 3] V) u)) :=
    invertibleOfNonzero (by rw [map_ogroup_apply]; exact hu)
  rw [reflOf_eq u hu, reflOf_eq _ (by rw [map_ogroup_apply]; exact hu)]
  exact TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv Q g u

@[expose] def reflPairs (Q : QuadraticForm (ZMod 3) V) : Set (OGroup Q) :=
  {g | ∃ (u v : V) (hu : Q u ≠ 0) (hv : Q v ≠ 0), Q u = Q v ∧ g = reflOf Q u hu * reflOf Q v hv}

theorem reflOf_mul_reflOf_mem (u v : V) (hu : Q u ≠ 0) (hv : Q v ≠ 0) (huv : Q u = Q v) :
    reflOf Q u hu * reflOf Q v hv ∈ reflPairs Q :=
  ⟨u, v, hu, hv, huv, rfl⟩

theorem normal_closure_reflPairs : (Subgroup.closure (reflPairs Q)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, hu, hv, huv, rfl⟩ := hx
    have hgu : Q ((g : V ≃ₗ[ZMod 3] V) u) ≠ 0 := by rw [map_ogroup_apply]; exact hu
    have hgv : Q ((g : V ≃ₗ[ZMod 3] V) v) ≠ 0 := by rw [map_ogroup_apply]; exact hv
    apply Subgroup.subset_closure
    refine ⟨(g : V ≃ₗ[ZMod 3] V) u, (g : V ≃ₗ[ZMod 3] V) v, hgu, hgv, ?_, ?_⟩
    · rw [map_ogroup_apply, map_ogroup_apply]
      exact huv
    · rw [show g * (reflOf Q u hu * reflOf Q v hv) * g⁻¹ =
          (g * reflOf Q u hu * g⁻¹) * (g * reflOf Q v hv * g⁻¹) by group,
        mul_reflOf_mul_inv, mul_reflOf_mul_inv]
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem omegaGroup_le_of_reflection_pairs (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (H : Subgroup (OGroup Q))
    (hH : ∀ (u v : V) (hu : Q u ≠ 0) (hv : Q v ≠ 0), Q u = Q v →
      reflOf Q u hu * reflOf Q v hv ∈ H) : omegaGroup hQ ≤ H := by
  set H₀ : Subgroup (OGroup Q) := Subgroup.closure (reflPairs Q) with hH₀def
  haveI hN : H₀.Normal := normal_closure_reflPairs
  have hH₀ : H₀ ≤ H := by
    refine (Subgroup.closure_le H).mpr ?_
    rintro g ⟨u, v, hu, hv, huv, rfl⟩
    exact hH u v hu hv huv
  let π : OGroup Q →* OGroup Q ⧸ H₀ := QuotientGroup.mk' H₀
  have hrefl : ∀ (u v : V) (hu : Q u ≠ 0) (hv : Q v ≠ 0),
      π (reflOf Q u hu) * π (reflOf Q v hv) = π (reflOf Q v hv) * π (reflOf Q u hu) := by
    intro u v hu hv
    have hmem : (reflOf Q u hu * reflOf Q v hv * (reflOf Q u hu)⁻¹) * (reflOf Q v hv)⁻¹ ∈ H₀ := by
      rw [mul_reflOf_mul_inv, reflOf_inv]
      apply Subgroup.subset_closure
      refine ⟨_, v, _, hv, ?_, rfl⟩
      rw [map_ogroup_apply]
    have h1 : π ((reflOf Q u hu * reflOf Q v hv * (reflOf Q u hu)⁻¹) * (reflOf Q v hv)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have hall : ∀ g h : OGroup Q, π g * π h = π h * π g := by
    have step1 : ∀ (u : V) (hu : Q u ≠ 0) (g : OGroup Q),
        π (reflOf Q u hu) * π g = π g * π (reflOf Q u hu) := by
      intro u hu
      have htop := TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ
        ((Subgroup.centralizer {π (reflOf Q u hu)}).comap π) (fun v hv => by
          have hv0 : Q v ≠ 0 := (isUnit_of_invertible (Q v)).ne_zero
          rw [← reflOf_eq v hv0, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
          exact hrefl v u hv0 hu)
      intro g
      have hg : g ∈ (Subgroup.centralizer {π (reflOf Q u hu)}).comap π := by
        rw [htop]; trivial
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hg
      exact hg.symm
    intro g h
    have htop := TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ
      ((Subgroup.centralizer {π g}).comap π) (fun v hv => by
        have hv0 : Q v ≠ 0 := (isUnit_of_invertible (Q v)).ne_zero
        rw [← reflOf_eq v hv0, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
        exact step1 v hv0 g)
    have hh : h ∈ (Subgroup.centralizer {π g}).comap π := by
      rw [htop]; trivial
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hh
    exact hh.symm
  have hcomm : commutator (OGroup Q) ≤ H₀ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [commutatorElement_def]
    have h1 : π (g * h * g⁻¹ * h⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hall g h]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  calc omegaGroup hQ = commutator (OGroup Q) := omegaGroup_eq_commutator hQ h2
    _ ≤ H₀ := hcomm
    _ ≤ H := hH₀

end CFSG.OddStandard.SmallF3.Omega
