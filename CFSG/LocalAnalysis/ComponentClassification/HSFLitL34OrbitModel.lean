module

public import Certificates.Certificate22805
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Model
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.UnbalancedLayer Subgroup

theorem exists_conj_eq_mul_center_T0
    {y : Equiv.Perm (Fin 42)} (hy : y ∈ TR) (hy2 : y * y = 1)
    (hyZ : ¬ (y ∈ T0 ∧ ∀ t ∈ T0, y * t = t * y))
    (hyc : ∀ t ∈ T0, y * (t * y * t⁻¹) = t * y * t⁻¹ * y) {z : Equiv.Perm (Fin 42)}
    (hz : z ∈ T0) (hzc : ∀ t ∈ T0, z * t = t * z) : ∃ τ ∈ T0, τ * y * τ⁻¹ = y * z := by
  have h := Certificates.certificate22805
  rw [cosetClassOK, List.all_eq_true] at h
  have h1 := h _ ((mem_TR_iff_code y).1 hy)
  have hsq : isId (psq (code y)) = true := (sq_iff y).2 hy2
  have hZ : inZB t0L (code y) = false := by
    cases hb : inZB t0L (code y)
    · rfl
    · exact absurd ((inZB_iff y).1 hb) hyZ
  have hcomm : (t0L.map fun t => pcomp (pcomp t (code y)) (pcube t)).all (commC (code y)) =
      true := by
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨tc, htc, rfl⟩ := List.mem_map.1 hc
    obtain ⟨t, ht, rfl⟩ := exists_of_mem_t0L htc
    rw [conj_code ht, commC_iff]
    exact hyc t ht
  simp only [hsq, hZ, hcomm, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 (code z) (List.mem_filter.2 ⟨(mem_T0_iff z).1 hz, (inZB_iff z).2 ⟨hz, hzc⟩⟩)
  rw [memB_iff, List.mem_map] at h2
  obtain ⟨tc, htc, he⟩ := h2
  obtain ⟨t, ht, rfl⟩ := exists_of_mem_t0L htc
  rw [conj_code ht, ← code_mul, code_inj] at he
  exact ⟨t, ht, he⟩

theorem conj_mem_center_T0 {n z : Equiv.Perm (Fin 42)}
    (hn : n ∈ TR) (hz : z ∈ T0)
    (hzc : ∀ t ∈ T0, z * t = t * z) :
    n * z * n⁻¹ ∈ T0 ∧ ∀ t ∈ T0, n * z * n⁻¹ * t = t * (n * z * n⁻¹) := by
  have hN := TR_le_normalizer hn
  refine ⟨(mem_normalizer_iff.mp hN z).mp hz, fun t ht => ?_⟩
  have ht' : n⁻¹ * t * n⁻¹⁻¹ ∈ T0 := (mem_normalizer_iff.mp (inv_mem hN) t).mp ht
  rw [inv_inv] at ht'
  have h1 := hzc _ ht'
  calc n * z * n⁻¹ * t = n * (z * (n⁻¹ * t * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * t * n) * z) * n⁻¹ := by rw [h1]
    _ = t * (n * z * n⁻¹) := by group

end CFSG.ComponentClassification.HSFLit.AutL34
