module

import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LrResLift
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLComplex
import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSL4Comp
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc.Res

open CFSG.ClassicalInvolution.Q3 CFSG.CGT.PushingUpLit.SolKNA
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)
open scoped MatrixGroups commutatorElement

section Std

variable {F : Type} [Field F] [Finite F] [Fact (¬ IsSquare (-1 : F))]

theorem theta_mul_comm (hF : Nat.card F = 3) {g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F}
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)))
    (S : SL(2, GaussField F)) :
    gaussTheta hF (le_refl 2) S * g = g * gaussTheta hF (le_refl 2) S := by
  have hscal : ∀ A : Matrix (Fin 2) (Fin 2) (GaussField F),
      A * Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F) =
        Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F) * A := fun A =>
    (Matrix.scalar_commute _ (fun r => Commute.all _ r) A).eq.symm
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, coe_gaussTheta,
    ← map_mul, ← map_mul, hscal]

theorem commutator_mem_range_theta (hF : Nat.card F = 3)
    {g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F}
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)))
    {x y : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F} (hx : x * g = g * x) (hy : y * g = g * y) :
    ⁅x, y⁆ ∈ (gaussTheta hF (le_refl 2)).range := by
  have hcomm : ∀ z : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F, z * g = g * z →
      (z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) *
        gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)) * z := by
    intro z hz
    have h' := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F =>
      (y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F)) hz
    simpa only [Matrix.SpecialLinearGroup.coe_mul, hg] using h'
  have hinv : ∀ z : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F, z * g = g * z →
      ∃ A A' : Matrix (Fin 2) (Fin 2) (GaussField F),
        gaussIota 2 A = (z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) ∧
        gaussIota 2 A' = ((z⁻¹ : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) :
          Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) ∧ A * A' = 1 := by
    intro z hz
    obtain ⟨A, hA⟩ := exists_gaussIota_of_commute 2 (hcomm z hz)
    obtain ⟨A', hA'⟩ := exists_gaussIota_of_commute 2 (hcomm z⁻¹ (Commute.inv_left hz).eq)
    refine ⟨A, A', hA, hA', ?_⟩
    apply gaussIota_injective 2
    rw [map_mul, hA, hA', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, map_one]
  obtain ⟨A, A', hA, hA', hAA⟩ := hinv x hx
  obtain ⟨B, B', hB, hB', hBB⟩ := hinv y hy
  have h1 : A.det * A'.det = 1 := by rw [← Matrix.det_mul, hAA, Matrix.det_one]
  have h2 : B.det * B'.det = 1 := by rw [← Matrix.det_mul, hBB, Matrix.det_one]
  have hdet : (A * B * A' * B').det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    calc A.det * B.det * A'.det * B'.det = (A.det * A'.det) * (B.det * B'.det) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  refine ⟨⟨A * B * A' * B', hdet⟩, ?_⟩
  apply Subtype.ext
  show gaussIota 2 (A * B * A' * B') = ((⁅x, y⁆ : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F)
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, map_mul, map_mul, map_mul, hA, hA', hB, hB']

theorem le_range_theta_of_perfect (hF : Nat.card F = 3)
    {g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F}
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)))
    {T : Subgroup (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F)} (hT : Group.IsPerfect T)
    (hTc : ∀ x ∈ T, x * g = g * x) : T ≤ (gaussTheta hF (le_refl 2)).range := by
  calc T = ⁅T, T⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ _ := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact commutator_mem_range_theta hF hg (hTc x hx) (hTc y hy)

theorem omega_mul_omega_gauss : (QuadraticAlgebra.omega : GaussField F) * QuadraticAlgebra.omega =
    -1 := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem coe_mul_self_of_gauss {g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F}
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F))) :
    ((g * g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) :
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) = -1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, hg, ← map_mul, ← map_mul, omega_mul_omega_gauss,
    map_neg, map_one, map_neg, map_one]

theorem ker_comp_theta_eq_center (hF : Nat.card F = 3) {L : Type*} [Group L]
    (φ : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F →* L)
    (hφk : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F))
    {g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F}
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)))
    (hy : φ g * φ g = 1) :
    (φ.comp (gaussTheta hF (le_refl 2))).ker = Subgroup.center SL(2, GaussField F) := by
  ext s
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hs
    have h1 : gaussTheta hF (le_refl 2) s ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) :=
      hφk (MonoidHom.mem_ker.mpr hs)
    obtain ⟨r, -, hrΘ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
    have h2 : gaussIota 2 (s : Matrix (Fin 2) (Fin 2) (GaussField F)) =
        gaussIota 2 (Matrix.scalar (Fin 2) (algebraMap F (GaussField F) r)) := by
      rw [gaussIota_scalar_algebraMap, hrΘ, coe_gaussTheta]
    have h3 : (s : Matrix (Fin 2) (Fin 2) (GaussField F)) =
        Matrix.scalar (Fin 2) (algebraMap F (GaussField F) r) := gaussIota_injective 2 h2
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨algebraMap F (GaussField F) r, ?_,
      h3.symm⟩
    have hdet := s.2
    rw [h3, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa using hdet
  · intro hs
    obtain ⟨c, hc2, hcs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs
    rw [Fintype.card_fin] at hc2
    rcases sq_eq_one_iff.mp hc2 with hc | hc
    · have : s = 1 := by
        apply Subtype.ext
        rw [← hcs, hc, map_one, Matrix.SpecialLinearGroup.coe_one]
      rw [this, map_one, map_one]
    · have : gaussTheta hF (le_refl 2) s = g * g := by
        apply Subtype.ext
        rw [coe_gaussTheta, coe_mul_self_of_gauss hg, ← hcs, hc, map_neg, map_one, map_neg,
          map_one]
      rw [this, map_mul, hy]

theorem part_B_std {L : Type*} [Group L] [Finite L] (hF : Nat.card F = 3)
    (φ : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F →* L)
    (hφk : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F))
    {g : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F}
    (hg : (g : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F) =
      gaussIota 2 (Matrix.scalar (Fin 2) (QuadraticAlgebra.omega : GaussField F)))
    (hy : φ g * φ g = 1) :
    ∃ A : Subgroup L, (∀ x ∈ A, x * φ g = φ g * x) ∧ Nonempty (↥A ≃* alternatingGroup (Fin 6)) ∧
      ∀ Q : Subgroup L, (∀ x ∈ Q, x * φ g = φ g * x) → Group.IsPerfect ↥Q → Q ≤ φ.range →
        Q ≤ A := by
  classical
  have : Finite (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) F) := inferInstance
  set Θ := gaussTheta hF (le_refl 2) with hΘ
  set ψ := φ.comp Θ with hψ
  refine ⟨ψ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    show φ (Θ s) * φ g = φ g * φ (Θ s)
    rw [← map_mul, ← map_mul, theta_mul_comm hF hg s]
  · have hker := ker_comp_theta_eq_center hF φ hφk hg hy
    haveI : Fintype (GaussField F) := Fintype.ofFinite _
    have hE9 : Fintype.card (GaussField F) = 9 := by
      rw [← Nat.card_eq_fintype_card, card_gaussField_eq_nine hF]
    obtain ⟨e3⟩ :=
      unique_field_nine_projective_linear_alternating_six_isomorphism (GaussField F) hE9
    exact ⟨(QuotientGroup.quotientKerEquivRange ψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (G := SL(2, GaussField F)) hker.symm).symm.trans e3)⟩
  · intro Q hQg hQ hQr
    obtain ⟨S, hS, hSg, hSQ⟩ := exists_perfect_lift φ hφk g hQ hQr hQg
    have hST : S ≤ Θ.range := le_range_theta_of_perfect hF hg hS hSg
    rw [← hSQ]
    calc S.map φ ≤ Θ.range.map φ := Subgroup.map_mono hST
      _ = ψ.range := (MonoidHom.range_comp φ Θ).symm

end Std

section Four

open scoped MatrixGroups

theorem part_B {L : Type*} [Group L] [Finite L] (φ : SL(4, ZMod 3) →* L)
    (hφk : φ.ker ≤ Subgroup.center SL(4, ZMod 3)) {g : SL(4, ZMod 3)}
    (hg2 : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = -1) (hy : φ g * φ g = 1) :
    ∃ A : Subgroup L, (∀ x ∈ A, x * φ g = φ g * x) ∧ Nonempty (↥A ≃* alternatingGroup (Fin 6)) ∧
      ∀ Q : Subgroup L, (∀ x ∈ Q, x * φ g = φ g * x) → Group.IsPerfect ↥Q → Q ≤ φ.range →
        Q ≤ A := by
  have hF : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  have := Fact.mk (not_isSquare_neg_one_of_card_eq_three hF)
  obtain ⟨m, c, hnm, hψg⟩ := exists_gaussBasis hF (n := 4) (by norm_num) g hg2
  obtain rfl : m = 2 := by omega
  let e := specialLinearBasisEquiv c
  let φ' : Matrix.SpecialLinearGroup (Fin 2 × Fin 2) (ZMod 3) →* L :=
    φ.comp e.symm.toMonoidHom
  have hφ'g : φ' (e g) = φ g := by simp [φ']
  have hk' : φ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2 × Fin 2) (ZMod 3)) := by
    intro x hx
    have h1 : e.symm x ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have h2 := Subgroup.mem_map_of_mem
      (↑e : SL(4, ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2 × Fin 2) (ZMod 3)) (hφk h1)
    rw [Subgroup.map_center_eq e] at h2
    simpa using h2
  obtain ⟨A, h1, h2, h3⟩ := part_B_std hF φ' hk' hψg (by rw [hφ'g]; exact hy)
  refine ⟨A, by rwa [hφ'g] at h1, h2, ?_⟩
  intro Q hQg hQ hQr
  refine h3 Q (by rwa [hφ'g]) hQ ?_
  intro x hx
  obtain ⟨k, rfl⟩ := hQr hx
  exact ⟨e k, by simp [φ']⟩

end Four

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc.Res
