module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Setup
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44SevenCommute
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44SevenTrace

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open Matrix

variable {K : Type*} [Field K]

private lemma pow_seven_eq_one {g : SpecialLinearGroup (Fin 4) K}
    (hg7 : (g : Matrix (Fin 4) (Fin 4) K) ^ 7 = 1) : g ^ 7 = 1 :=
  Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_pow] using hg7)

private lemma coe_inv_eq_pow_six {g : SpecialLinearGroup (Fin 4) K}
    (hg7 : (g : Matrix (Fin 4) (Fin 4) K) ^ 7 = 1) :
    ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) K) ^ 6 := by
  have h7 : g ^ 7 = 1 := pow_seven_eq_one hg7
  have h : g * g ^ 6 = 1 := by
    rw [← pow_succ']
    simpa using h7
  calc ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      = ((g ^ 6 : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
        congrArg (fun x : SpecialLinearGroup (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K))
          (inv_eq_of_mul_eq_one_right h)
    _ = (g : Matrix (Fin 4) (Fin 4) K) ^ 6 := Matrix.SpecialLinearGroup.coe_pow g 6

private lemma trace_coe_map (σ : K ≃+* K) (X : SpecialLinearGroup (Fin 4) K) :
    trace (((Matrix.SpecialLinearGroup.map σ.toRingHom X : SpecialLinearGroup (Fin 4) K)) :
      Matrix (Fin 4) (Fin 4) K) = σ (trace (X : Matrix (Fin 4) (Fin 4) K)) := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  exact (AddMonoidHom.map_trace σ.toRingHom (X : Matrix (Fin 4) (Fin 4) K)).symm

private lemma trace_coe_transpose (X : SpecialLinearGroup (Fin 4) K) :
    trace (((X.transpose : SpecialLinearGroup (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
      trace (X : Matrix (Fin 4) (Fin 4) K) := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.trace_transpose]

private lemma fieldAut_fixes_trace (σ : K ≃+* K) {g : Matrix (Fin 4) (Fin 4) K}
    (h : trace g = 0 ∨ trace g = 1) : σ (trace g) = trace g := by
  rcases h with h | h <;> simp [h]

private lemma fieldAut_add_one_fixes_trace (σ : K ≃+* K) {g : Matrix (Fin 4) (Fin 4) K}
    (h : trace g = 0 ∨ trace g = 1) : σ (trace g + 1) = trace g + 1 := by
  have hσ : σ (trace g) = trace g := fieldAut_fixes_trace σ h
  rw [map_add, hσ, map_one]

private lemma trace_eq_add_one_ne_self {g : Matrix (Fin 4) (Fin 4) K}
    (h : trace g = trace g + 1) : False := by
  have h01 : (0 : K) = 1 :=
    add_left_cancel (show trace g + 0 = trace g + 1 by rw [add_zero]; exact h)
  exact one_ne_zero h01.symm

theorem mem_semilinearAutGroup_of_apply_eq (hK : Nat.card K = 4)
    {θ : MulAut (projectiveSL 4 K)} {y : projectiveSL 4 K} (hy : orderOf y = 7) (h : θ y = y) :
    θ ∈ semilinearAutGroup 4 K := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  by_contra hθ
  obtain ⟨A, σ, ε, hε, hθeq⟩ :=
    (automorphism_generation (K := K) (n := 4) (by norm_num)).2 θ
  obtain ⟨g, hyg, hg7, hg1⟩ := exists_lift_of_orderOf_seven hK hy
  have hτ := (trace_of_pow_seven hK hg7 hg1).1
  have htr6 := (trace_of_pow_seven hK hg7 hg1).2
  rcases Nat.eq_zero_or_pos ε with hε0 | hεpos
  · rw [hε0, pow_zero, mul_one] at hθeq
    apply hθ
    rw [hθeq]
    exact mem_semilinearAutGroup_iff.mpr ⟨A, σ, rfl⟩
  · have hε1 : ε = 1 := by omega
    rw [hε1, pow_one] at hθeq
    have hθy : θ y = proj 4 K
        (slConjugation 4 K A (Matrix.SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose))) := by
      rw [hθeq, ← hyg]
      simp only [MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]
    have hproj : proj 4 K
        (slConjugation 4 K A (Matrix.SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose))) =
          proj 4 K g := by
      rw [← hθy, h, hyg]
    have hmat : ((slConjugation 4 K A
        (Matrix.SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose)) :
          SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (g : Matrix (Fin 4) (Fin 4) K) :=
      congrArg (fun x : SpecialLinearGroup (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K))
        (proj_four_injective hK hproj)
    set M : Matrix (Fin 4) (Fin 4) K :=
      (((Matrix.SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose) :
        SpecialLinearGroup (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) with hM
    have hmat' : (A : Matrix (Fin 4) (Fin 4) K) * M *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (g : Matrix (Fin 4) (Fin 4) K) := by
      rw [hM, ← coe_slConjugation]
      exact hmat
    have htraceA : trace ((A : Matrix (Fin 4) (Fin 4) K) * M *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = trace M := by
      simpa using trace_units_conj A M
    have htrace_g : trace M = trace (g : Matrix (Fin 4) (Fin 4) K) := by
      rw [← htraceA]
      exact congrArg trace hmat'
    have htraceM : trace M = trace (g : Matrix (Fin 4) (Fin 4) K) + 1 := by
      rw [hM, trace_coe_map, trace_coe_transpose, coe_inv_eq_pow_six hg7, htr6]
      exact fieldAut_add_one_fixes_trace σ hτ
    exact trace_eq_add_one_ne_self (htrace_g.symm.trans htraceM)

theorem not_mem_semilinearAutGroup_of_apply_eq_inv (hK : Nat.card K = 4)
    {θ : MulAut (projectiveSL 4 K)} {y : projectiveSL 4 K} (hy : orderOf y = 7)
    (h : θ y = y⁻¹) : θ ∉ semilinearAutGroup 4 K := by
  classical
  intro hθ
  obtain ⟨A, σ, hθeq⟩ := mem_semilinearAutGroup_iff.mp hθ
  obtain ⟨g, hyg, hg7, hg1⟩ := exists_lift_of_orderOf_seven hK hy
  have hτ := (trace_of_pow_seven hK hg7 hg1).1
  have htr6 := (trace_of_pow_seven hK hg7 hg1).2
  have hθy : θ y = proj 4 K
      (slConjugation 4 K A (Matrix.SpecialLinearGroup.map σ.toRingHom g)) := by
    rw [hθeq, ← hyg]
    simp only [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  have hproj : proj 4 K
      (slConjugation 4 K A (Matrix.SpecialLinearGroup.map σ.toRingHom g)) = proj 4 K g⁻¹ := by
    rw [← hθy, h, ← hyg, map_inv]
  have hmat : ((slConjugation 4 K A
      (Matrix.SpecialLinearGroup.map σ.toRingHom g) : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = ((g⁻¹ : SpecialLinearGroup (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) :=
    congrArg (fun x : SpecialLinearGroup (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K))
      (proj_four_injective hK hproj)
  set M : Matrix (Fin 4) (Fin 4) K :=
    (((Matrix.SpecialLinearGroup.map σ.toRingHom g : SpecialLinearGroup (Fin 4) K)) :
      Matrix (Fin 4) (Fin 4) K) with hM
  have hmat' : (A : Matrix (Fin 4) (Fin 4) K) * M *
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hM, ← coe_slConjugation]
    exact hmat
  have htraceA : trace ((A : Matrix (Fin 4) (Fin 4) K) * M *
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = trace M := by
    simpa using trace_units_conj A M
  have htraceL : trace M = σ (trace (g : Matrix (Fin 4) (Fin 4) K)) := by
    rw [hM, trace_coe_map]
  have htraceR : trace ((g⁻¹ : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = trace (g : Matrix (Fin 4) (Fin 4) K) + 1 := by
    rw [coe_inv_eq_pow_six hg7, htr6]
  have hσ : σ (trace (g : Matrix (Fin 4) (Fin 4) K)) =
      trace (g : Matrix (Fin 4) (Fin 4) K) + 1 := by
    rw [← htraceL, ← htraceR]
    exact htraceA.symm.trans (congrArg trace hmat')
  have hcon : trace (g : Matrix (Fin 4) (Fin 4) K) =
      trace (g : Matrix (Fin 4) (Fin 4) K) + 1 :=
    (fieldAut_fixes_trace σ hτ).symm.trans hσ
  exact trace_eq_add_one_ne_self hcon

theorem eq_one_of_commute_of_orderOf_seven (hK : Nat.card K = 4) {y u : projectiveSL 4 K}
    (hy : orderOf y = 7) (hu : u * u = 1) (hyu : y * u = u * y) : u = 1 := by
  classical
  obtain ⟨g, hyg, hg7, hg1⟩ := exists_lift_of_orderOf_seven hK hy
  obtain ⟨h, hh⟩ := proj_surjective 4 K u
  have hh2 : h * h = 1 := by
    have h1 : proj 4 K (h * h) = 1 := by rw [map_mul, hh, hu]
    rw [proj_eq_one_iff] at h1
    rwa [scalars_four_eq_bot hK, Subgroup.mem_bot] at h1
  have hgh : g * h = h * g := by
    apply proj_four_injective hK
    rw [map_mul, map_mul, hyg, hh, hyu]
  have hmat : (h : Matrix (Fin 4) (Fin 4) K) * (h : Matrix (Fin 4) (Fin 4) K) = 1 := by
    have h' := congrArg (fun x : SpecialLinearGroup (Fin 4) K =>
      (x : Matrix (Fin 4) (Fin 4) K)) hh2
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h'
  have hcomm : (g : Matrix (Fin 4) (Fin 4) K) * (h : Matrix (Fin 4) (Fin 4) K) =
      (h : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) := by
    have h' := congrArg (fun x : SpecialLinearGroup (Fin 4) K =>
      (x : Matrix (Fin 4) (Fin 4) K)) hgh
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h'
  have hh1 : (h : Matrix (Fin 4) (Fin 4) K) = 1 :=
    eq_one_of_commute_of_pow_seven hK hg7 hg1 hmat hcomm
  rw [← hh, show h = 1 from Subtype.ext hh1, map_one]

end CFSG.OddStandard.AltStdSec.SwapPartner
