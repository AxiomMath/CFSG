module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroExhaustion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroKernel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonal

variable {K : Type*} [Field K]

@[expose] def traceZeroSpecialImage (K : Type*) [Field K] :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) :=
  (traceZeroOrthogonalAction.comp
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K)).range

theorem traceZeroOrthogonalAction_mem_specialImage {A : GL (Fin 2) K}
    (hA : GeneralLinearGroup.det A = 1) :
    traceZeroOrthogonalAction A ∈ traceZeroSpecialImage K := by
  have hA' : A ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range :=
    by rw [SpecialLinearGroup.range_toGL_eq_ker_det]; exact hA
  obtain ⟨S, rfl⟩ := hA'
  exact ⟨S, rfl⟩

theorem traceZeroOrthogonalAction_mem_specialImage_of_det_eq_sq {A : GL (Fin 2) K} {c : Kˣ}
    (hA : GeneralLinearGroup.det A = c ^ 2) :
    traceZeroOrthogonalAction A ∈ traceZeroSpecialImage K := by
  have h := traceZeroOrthogonalAction_mem_specialImage
    (A := GeneralLinearGroup.scalar (Fin 2) c⁻¹ * A) (by
      rw [map_mul, GeneralLinearGroup.det_scalar, hA, Fintype.card_fin, inv_pow,
        inv_mul_cancel])
  rwa [map_mul, traceZeroOrthogonalAction_scalar, one_mul] at h

theorem traceZero_sq_mem_specialImage (h2 : (2 : K) ≠ 0)
    (g : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) :
    g ^ 2 ∈ traceZeroSpecialImage K := by
  obtain ⟨⟨A, ε⟩, rfl⟩ := traceZeroFullAction_surjective h2 g
  have hε : ε ^ 2 = 1 := Subtype.ext ((mem_rootsOfUnity 2 ε.val).mp ε.property)
  change (traceZeroOrthogonalAction A * traceZeroScalarAction ε) ^ 2 ∈ _
  rw [(traceZeroScalarAction_commute ε A).symm.mul_pow, ← map_pow, ← map_pow, hε, map_one,
    mul_one]
  exact traceZeroOrthogonalAction_mem_specialImage_of_det_eq_sq
    (c := GeneralLinearGroup.det A) (map_pow _ _ _)

theorem traceZeroSpecialImage_normal (h2 : (2 : K) ≠ 0) : (traceZeroSpecialImage K).Normal := by
  constructor
  rintro _ ⟨S, rfl⟩ g
  obtain ⟨⟨A, ε⟩, rfl⟩ := traceZeroFullAction_surjective h2 g
  change traceZeroOrthogonalAction A * traceZeroScalarAction ε *
    traceZeroOrthogonalAction (SpecialLinearGroup.toGL S) *
    (traceZeroOrthogonalAction A * traceZeroScalarAction ε)⁻¹ ∈ _
  have hc := (traceZeroScalarAction_commute ε (SpecialLinearGroup.toGL S)).eq
  have heq : traceZeroOrthogonalAction A * traceZeroScalarAction ε *
      traceZeroOrthogonalAction (SpecialLinearGroup.toGL S) *
      (traceZeroOrthogonalAction A * traceZeroScalarAction ε)⁻¹ =
      traceZeroOrthogonalAction (A * SpecialLinearGroup.toGL S * A⁻¹) := by
    rw [map_mul, map_mul, map_inv, _root_.mul_inv_rev,
      mul_assoc (traceZeroOrthogonalAction A), hc]
    group
  rw [heq]
  apply traceZeroOrthogonalAction_mem_specialImage
  rw [map_mul, map_mul, map_inv, SpecialLinearGroup.coeToGL_det, mul_one, mul_inv_cancel]

variable [Finite K]

theorem traceZeroSpecialImage_quasisimple (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    CFSG.IsQuasisimple (traceZeroSpecialImage K) := by
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  let f := traceZeroOrthogonalAction.comp
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K)
  rcases quasisimple_homomorphic_images hSL f with h | h
  · exfalso
    let S : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hmem : f S ∈ f.range := ⟨S, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    obtain ⟨c, hc⟩ := (traceZeroOrthogonalAction_eq_one_iff _).mp hmem
    have h01 := congrArg (fun B : GL (Fin 2) K => B.val 0 1) hc
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
    change Matrix.diagonal (fun _ => (c : K)) 0 1 = 1 at h01
    rw [Matrix.diagonal_apply_ne _ (by decide)] at h01
    exact zero_ne_one h01
  · exact h

theorem traceZero_commutator_eq (hodd : Odd (Nat.card K)) (hK3 : Nat.card K ≠ 3) :
    commutator (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) =
      traceZeroSpecialImage K := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have := traceZeroSpecialImage_normal h2
  have hK2 : Nat.card K ≠ 2 := by
    rintro h
    rw [h] at hodd
    exact absurd hodd (by decide)
  exact commutator_eq_of_isPerfect_of_forall_sq_mem
    (traceZeroSpecialImage_quasisimple hK2 hK3).1 (traceZero_sq_mem_specialImage h2)

theorem traceZero_prime_dvd_card (hK : Nat.card K = 3) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K))) :
    p = 2 ∨ p = 3 := by
  have h2 : (2 : K) ≠ 0 :=
    CatalogueBOddQuadratic.two_ne_zero_of_odd_card (by rw [hK]; decide)
  have hrange : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) ∣
      Nat.card (GL (Fin 2) K × rootsOfUnity 2 K) := by
    have h := Subgroup.card_range_dvd (traceZeroFullAction (K := K))
    rwa [MonoidHom.range_eq_top.mpr (traceZeroFullAction_surjective h2),
      Subgroup.card_top] at h
  rw [Nat.card_prod] at hrange
  rcases (Nat.Prime.dvd_mul hp).mp (hdvd.trans hrange) with h | h
  · exact prime_dvd_forty_eight hp (h.trans (card_GL_two_dvd_forty_eight hK.le))
  · left
    have hle : p ≤ 2 := (Nat.le_of_dvd Nat.card_pos h).trans (card_rootsOfUnity K 2)
    have := hp.two_le
    omega

end CFSG.LocalAnalysis.ComponentInitial
