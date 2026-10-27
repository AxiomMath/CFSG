module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutI
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4

namespace X10Sp4

variable {K : Type} [Field K]

theorem exists_ne_pm (h2 : (2 : K) ≠ 0) {σ : K ≃+* K} (hσ : σ ≠ 1) :
    ∃ t : K, σ t ≠ t ∧ σ t ≠ -t := by
  by_contra hcon
  push Not at hcon
  apply hσ
  refine RingEquiv.ext fun t => ?_
  change σ t = t
  by_contra ht
  have h1 := hcon t ht
  have ht0 : t ≠ 0 := fun h => ht (by rw [h, map_zero])
  have h4 : σ (t + 1) ≠ t + 1 := by
    rw [map_add, map_one, h1]
    intro h
    apply ht0
    have h' : (2 : K) * t = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2
  have h5 := hcon (t + 1) h4
  rw [map_add, map_one, h1] at h5
  apply h2
  linear_combination h5

theorem trace_conj (A : GL (Fin 2 ⊕ Fin 2) K) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    trace ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * M *
      ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = trace M := by
  rw [trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem trace_fixed (A : gsp 2 K) (σ : K ≃+* K) {g : StatedSp 2 K}
    (h : (conjAut 2 K A * fieldAut 2 K σ) (proj 2 K g) = proj 2 K g) :
    σ (trace ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) =
        trace ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∨
      σ (trace ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) =
        -trace ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h
  have htr : trace (((conjSp 2 K A (fieldSp 2 K σ g) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        σ (trace ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
    rw [coe_conjSp, Units.val_mul, Units.val_mul, trace_conj, coe_fieldSp]
    exact (AddMonoidHom.map_trace σ _).symm
  rcases eq_or_eq_neg_of_proj_eq h with h1 | h1
  · left
    rw [← htr, ← h1]
  · right
    rw [← htr, h1, trace_neg, neg_neg]

@[expose] def AllTraces (M : Subgroup (StatedProj (StatedSp 2 K))) : Prop :=
  ∀ t : K, ∃ g : StatedSp 2 K, proj 2 K g ∈ M ∧
    trace ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 2 * t

theorem false_of_allTraces (h2 : (2 : K) ≠ 0) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hM : AllTraces M) (A : gsp 2 K) {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hfix : ∀ x ∈ M, (conjAut 2 K A * fieldAut 2 K σ) x = x) : False := by
  obtain ⟨t, ht1, ht2⟩ := exists_ne_pm h2 hσ
  obtain ⟨g, hgM, htr⟩ := hM t
  have h22 : σ 2 = 2 := map_ofNat σ 2
  rcases trace_fixed A σ (hfix _ hgM) with h | h <;> rw [htr, map_mul, h22] at h
  · exact ht1 (mul_left_cancel₀ h2 h)
  · exact ht2 (mul_left_cancel₀ h2 (by rw [h]; ring))

theorem trace_kron_one (k : Matrix (Fin 2) (Fin 2) K) : trace (kron k 1) = 2 * trace k := by
  simp [kron, trace, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

@[expose] def slOfTrace (t : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨(!![t, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K), by simp [Matrix.det_fin_two]⟩

theorem trace_slOfTrace (t : K) :
    trace ((slOfTrace t : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = t := by
  simp [slOfTrace, trace, Fin.sum_univ_two]

theorem allTraces_Lsub : AllTraces (Lsub K) := fun t =>
  ⟨diagSL K (slOfTrace t), ⟨_, ⟨slOfTrace t, rfl⟩, rfl⟩, by
    rw [coe_diagSL, trace_kron_one, trace_slOfTrace]⟩

theorem allTraces_JI {a : K} (ha : a ≠ 0) : AllTraces (JI ha) := fun t =>
  ⟨gI ha (slOfTrace t), ⟨_, ⟨slOfTrace t, rfl⟩, rfl⟩, by
    rw [coe_gI, trace_mul_cycle, bAinv_mul_bA ha, Matrix.one_mul, trace_kron_one,
      trace_slOfTrace]⟩

theorem allTraces_map [Finite K] (hodd : ringChar K ≠ 2) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hM : AllTraces M) (φ : MulAut (StatedProj (StatedSp 2 K))) :
    AllTraces (M.map φ.toMonoidHom) := by
  obtain ⟨X, ρ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hodd le_rfl φ
  intro s
  obtain ⟨g, hgM, htr⟩ := hM (ρ.symm s)
  refine ⟨conjSp 2 K X (fieldSp 2 K ρ g), ⟨_, hgM, ?_⟩, ?_⟩
  · change (conjAut 2 K X * fieldAut 2 K ρ) (proj 2 K g) = _
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  · rw [coe_conjSp, Units.val_mul, Units.val_mul, trace_conj, coe_fieldSp,
      ← AddMonoidHom.map_trace ρ, htr]
    change ρ (2 * ρ.symm s) = 2 * s
    rw [map_mul, map_ofNat, RingEquiv.apply_symm_apply]

end X10Sp4

end CFSG.ComponentClassification.GSThmB
