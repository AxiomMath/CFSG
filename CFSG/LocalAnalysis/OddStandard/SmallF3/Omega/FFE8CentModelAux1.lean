module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}

@[expose] noncomputable def ffOutFFE8CentModel_grp (fr : PFrame Q ι c) : Subgroup (OGroup Q) where
  carrier := {g | ∃ K : Finset ι, g = fr.signChange K}
  one_mem' := ⟨∅, fr.signChange_empty.symm⟩
  mul_mem' := by
    rintro _ _ ⟨J, rfl⟩ ⟨K, rfl⟩
    exact ⟨symmDiff J K, fr.signChange_mul J K⟩
  inv_mem' := by
    rintro _ ⟨J, rfl⟩
    exact ⟨J, inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)⟩

theorem ffOutFFE8CentModel_piOrth_mem (fr : PFrame Q ι c) :
    piOrth Q ∈ ffOutFFE8CentModel_grp fr :=
  ⟨Finset.univ, fr.piOrth_eq_signChange_univ⟩

theorem ffOutFFE8CentModel_grp_comm (fr : PFrame Q ι c) {a b : OGroup Q}
    (ha : a ∈ ffOutFFE8CentModel_grp fr) (hb : b ∈ ffOutFFE8CentModel_grp fr) : a * b = b * a := by
  obtain ⟨J, rfl⟩ := ha
  obtain ⟨K, rfl⟩ := hb
  exact fr.signChange_comm J K

theorem ffOutFFE8CentModel_grp_mul_self (fr : PFrame Q ι c) {a : OGroup Q}
    (ha : a ∈ ffOutFFE8CentModel_grp fr) : a * a = 1 := by
  obtain ⟨J, rfl⟩ := ha
  exact fr.signChange_mul_self J

private theorem sum_ite_neg_one (K : Finset ι) :
    ∑ i, (if i ∈ K then (-1 : ZMod 3) else 1) = (Fintype.card ι : ZMod 3) - 2 * K.card := by
  have h : ∀ i, (if i ∈ K then (-1 : ZMod 3) else 1) = 1 - 2 * (if i ∈ K then 1 else 0) := by
    intro i
    by_cases hi : i ∈ K <;> simp only [hi, if_true, if_false] <;> decide
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem ffOutFFE8CentModel_trace_signChange (fr : PFrame Q ι c) (K : Finset ι) :
    LinearMap.trace (ZMod 3) V ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V).toLinearMap =
      (Fintype.card ι : ZMod 3) - 2 * K.card := by
  rw [LinearMap.trace_eq_matrix_trace (ZMod 3) fr.b, ← sum_ite_neg_one K]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe,
    fr.signChange_basis]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ K <;> simp [hi]

theorem ffOutFFE8CentModel_trace_neg (fr : PFrame Q ι c) (K : Finset ι) {γ : V ≃ₗ[ZMod 3] V}
    (h : ∀ v, ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) (γ v) =
      -γ (((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) v)) :
    (Fintype.card ι : ZMod 3) - 2 * K.card = 0 := by
  have hconj : γ.conj ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V).toLinearMap =
      -((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V).toLinearMap := by
    ext w
    have h1 := h (γ.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.neg_apply]
    rw [h1, neg_neg]
  have h2 := LinearMap.trace_conj' ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V).toLinearMap γ
  rw [hconj, map_neg, ffOutFFE8CentModel_trace_signChange] at h2
  revert h2
  generalize (Fintype.card ι : ZMod 3) - 2 * K.card = x
  revert x
  decide

theorem ffOutFFE8CentModel_commute_cases (t : OGroup Q) (γ : simGroup Q)
    (h : ffSim Q t * (QuotientGroup.mk γ : ProjSim Q) = QuotientGroup.mk γ * ffSim Q t) :
    (∀ v, (t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v) =
        (γ : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) v)) ∨
      (∀ v, (t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v) =
        -(γ : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) v)) := by
  have h1 : (QuotientGroup.mk (orthToSim Q t * γ) : ProjSim Q) =
      QuotientGroup.mk (γ * orthToSim Q t) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact h
  have h2 := QuotientGroup.eq.mp h1
  rcases mem_piSim_iff.mp h2 with h3 | h3
  · left
    have h4 : orthToSim Q t * γ = γ * orthToSim Q t := inv_mul_eq_one.mp h3
    intro v
    exact congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V) v) h4
  · right
    have h4 : γ * orthToSim Q t = orthToSim Q t * γ * orthToSim Q (piOrth Q) :=
      inv_mul_eq_iff_eq_mul.mp h3
    intro v
    have h5 := congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V) v) h4
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_orthToSim, coe_piOrth_apply,
      map_neg] at h5
    rw [h5, neg_neg]

theorem ffOutFFE8CentModel_repr_comm (fr : PFrame Q ι c) (K : Finset ι) {γ : V ≃ₗ[ZMod 3] V}
    (h : ∀ v, ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) (γ v) =
      γ (((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) v))
    (i j : ι) :
    ((if i ∈ K then (-1 : ZMod 3) else 1) - (if j ∈ K then -1 else 1)) *
      fr.b.repr (γ (fr.b j)) i = 0 := by
  have h1 := congrArg (fun v => fr.b.repr v i) (h (fr.b j))
  simp only [fr.repr_signChange, fr.signChange_basis] at h1
  by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;> simp [hi, hj] at h1 ⊢ <;>
    (revert h1; generalize (fr.b.repr (γ (fr.b j))) i = x; revert x; decide)

end CFSG.OddStandard.SmallF3.Omega
