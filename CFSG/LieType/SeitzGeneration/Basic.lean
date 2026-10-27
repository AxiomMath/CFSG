module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.LieType.SeitzGeneration

variable {K : Type*} [Group K]

@[expose] def planeClosure (E : Subgroup (MulAut K)) : Subgroup K :=
  Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k = k}

@[expose] def PlaneGen (E : Subgroup (MulAut K)) : Prop :=
  planeClosure E = ⊤

theorem mem_planeClosure_of_fixed {E : Subgroup (MulAut K)} {e : MulAut K} (he : e ∈ E)
    (he1 : e ≠ 1) {k : K} (hk : e k = k) : k ∈ planeClosure E :=
  Subgroup.subset_closure ⟨e, he, he1, hk⟩

theorem mem_planeClosure_of_commute {E₀ : Subgroup K} {g : K} (hg : g ∈ E₀)
    (hg1 : (MulAut.conj g : MulAut K) ≠ 1) {k : K} (hk : k * g = g * k) :
    k ∈ planeClosure (E₀.map (MulAut.conj : K →* MulAut K)) := by
  refine mem_planeClosure_of_fixed (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩) hg1 ?_
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact hk.symm

theorem planeClosure_mono {E F : Subgroup (MulAut K)} (h : E ≤ F) :
    planeClosure E ≤ planeClosure F :=
  Subgroup.closure_mono fun _ ⟨e, he, he1, hk⟩ => ⟨e, h he, he1, hk⟩

theorem PlaneGen.mono {E F : Subgroup (MulAut K)} (h : E ≤ F) (hE : PlaneGen E) : PlaneGen F :=
  top_le_iff.mp (hE ▸ planeClosure_mono h)

theorem planeClosure_map_congr {L : Type*} [Group L] (e : K ≃* L) (E : Subgroup (MulAut K)) :
    planeClosure (E.map (MulAut.congr e).toMonoidHom) = (planeClosure E).map e.toMonoidHom := by
  unfold planeClosure
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    rintro l ⟨_, ⟨ε, hε, rfl⟩, hε1, hεl⟩
    refine ⟨e.symm l, ⟨ε, hε, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hε1 (map_one _)
    · have := congrArg e.symm hεl
      simpa [MulAut.congr_apply] using this
  · refine Subgroup.closure_mono ?_
    rintro _ ⟨k, ⟨ε, hε, hε1, hεk⟩, rfl⟩
    refine ⟨(MulAut.congr e).toMonoidHom ε, ⟨ε, hε, rfl⟩, ?_, ?_⟩
    · intro h
      exact hε1 ((MulAut.congr e).map_eq_one_iff.mp h)
    · simp [MulAut.congr_apply, hεk]

theorem planeGen_map_congr {L : Type*} [Group L] (e : K ≃* L) (E : Subgroup (MulAut K)) :
    PlaneGen (E.map (MulAut.congr e).toMonoidHom) ↔ PlaneGen E := by
  unfold PlaneGen
  rw [planeClosure_map_congr]
  constructor
  · intro h
    have := congrArg (Subgroup.comap e.toMonoidHom) h
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this
  · intro h
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]

end CFSG.LieType.SeitzGeneration
