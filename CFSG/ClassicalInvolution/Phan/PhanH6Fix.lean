module

public import CFSG.ClassicalInvolution.Phan.PhanH5Frames
public import CFSG.ClassicalInvolution.Asc77.AscB3C1

public section

namespace CFSG.ClassicalInvolution.PhanB3.H

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort Pel kron2 kronMat Pmat mat_Pel mat_kron2
  twShort_apply)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def vP (a b : F) : Fin 2 ⊕ Fin 2 ⊕ Unit → F :=
  Sum.elim ![a / 2, b] (Sum.elim ![2 * a, b] fun _ => 0)

theorem kappa_vP (h2 : (2 : F) ≠ 0) (a b : F) :
    kappa (vP a b) = mk7 0 a b 0 (-a) (-b) 0 := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [kappa_eq_mk7]
  simp [vP]
  field_simp

theorem Pmat_iota5_vP (h2 : (2 : F) ≠ 0) (a b : F) :
    Pmat F * iota5 (vP a b) * (Pmat F).transpose =
      Matrix.fromBlocks 0 !![b, a; a, -b] (-!![b, a; a, -b]) 0 := by
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Pmat, iota5_apply, vP, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.transpose_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem kron_fix_block (A : SL(2, F)) (s0 s1 s2 : F) :
    kronMat (A : Matrix (Fin 2) (Fin 2) F) *
      Matrix.fromBlocks 0 !![s0, s1; s1, s2] (-!![s0, s1; s1, s2]) 0 *
      (kronMat (A : Matrix (Fin 2) (Fin 2) F)).transpose =
      Matrix.fromBlocks 0 !![s0, s1; s1, s2] (-!![s0, s1; s1, s2]) 0 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    exact this
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [kronMat, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.transpose_apply] <;>
    first | ring1 | linear_combination s0 * hdet | linear_combination s1 * hdet |
      linear_combination s2 * hdet | linear_combination (-s0) * hdet |
      linear_combination (-s1) * hdet | linear_combination (-s2) * hdet

theorem twShort_fix_iota5 (h2 : (2 : F) ≠ 0) (A : SL(2, F)) (a b : F) :
    mat 2 F (twShort h2 A) * iota5 (vP a b) * (mat 2 F (twShort h2 A)).transpose =
      iota5 (vP a b) := by
  have hPi : mat 2 F ((Pel h2)⁻¹) * Pmat F = 1 := by
    rw [← mat_Pel h2, ← map_mul, inv_mul_cancel, map_one]
  have hmat : mat 2 F (twShort h2 A) =
      mat 2 F ((Pel h2)⁻¹) * kronMat (A : Matrix (Fin 2) (Fin 2) F) * Pmat F := by
    rw [twShort_apply, map_mul, map_mul, mat_kron2, mat_Pel]
  have key := kron_fix_block A b a (-b)
  rw [← Pmat_iota5_vP h2 a b] at key
  have h1 : (mat 2 F ((Pel h2)⁻¹) * kronMat (A : Matrix (Fin 2) (Fin 2) F) * Pmat F) *
      iota5 (vP a b) * (mat 2 F ((Pel h2)⁻¹) * kronMat (A : Matrix (Fin 2) (Fin 2) F) *
        Pmat F).transpose =
      mat 2 F ((Pel h2)⁻¹) * (kronMat (A : Matrix (Fin 2) (Fin 2) F) *
        (Pmat F * iota5 (vP a b) * (Pmat F).transpose) *
        (kronMat (A : Matrix (Fin 2) (Fin 2) F)).transpose) *
        (mat 2 F ((Pel h2)⁻¹)).transpose := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have h2' : (mat 2 F ((Pel h2)⁻¹) * Pmat F) * iota5 (vP a b) *
      (mat 2 F ((Pel h2)⁻¹) * Pmat F).transpose =
      mat 2 F ((Pel h2)⁻¹) * (Pmat F * iota5 (vP a b) * (Pmat F).transpose) *
        (mat 2 F ((Pel h2)⁻¹)).transpose := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hmat, h1, key, ← h2', hPi]
  simp

section Theta

variable {φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)} {θ : StatedSp 2 F →* spinGroup (quadOdd 3 F)}

theorem theta_twShort_Pp (hφ : IsLevi φ)
    (hnat : ∀ g v, spinAction (quadOdd 3 F) (θ g) (kappa v) =
      kappa (spinAction (quadOdd 2 F) (φ g) v))
    (h2 : (2 : F) ≠ 0) (A : SL(2, F)) (a b : F) :
    spinAction (quadOdd 3 F) (θ (twShort h2 A)) (mk7 0 a b 0 (-a) (-b) 0) =
      mk7 0 a b 0 (-a) (-b) 0 := by
  have := spinAction_theta_eq hφ hnat (twShort h2 A) (vP a b) (vP a b)
    (twShort_fix_iota5 h2 A a b).symm
  rwa [kappa_vP h2] at this

theorem theta_fix_P (hfix : ∀ g (p : Fin 3 ⊕ Fin 3 ⊕ Unit → F),
    (∀ v, polar (quadOdd 3 F) p (kappa v) = 0) → spinAction (quadOdd 3 F) (θ g) p = p)
    (g : StatedSp 2 F) (s z : F) :
    spinAction (quadOdd 3 F) (θ g) (mk7 s 0 0 s 0 0 z) = mk7 s 0 0 s 0 0 z := by
  refine hfix g _ fun v => ?_
  rw [kappa_eq_mk7, polar_mk7]
  ring

end Theta

theorem mem_span_fr0 (h2 : (2 : F) ≠ 0) {x : Fin 3 ⊕ Fin 3 ⊕ Unit → F}
    (hx : x ∈ (fr0 h2).span) : ∃ s a b z : F, x = mk7 s a b s (-a) (-b) z := by
  rw [Frame.mem_span_iff_inv _ h2, La0_neg_one] at hx
  have e1 := congrFun hx (.inl 0)
  have e2 := congrFun hx (.inl 1)
  have e3 := congrFun hx (.inl 2)
  simp at e1 e2 e3
  refine ⟨x (.inl 0), x (.inl 1), x (.inl 2), x (.inr (.inr ())), ?_⟩
  conv_lhs => rw [mk7_eta x]
  have e2' : x (.inr (.inl 1)) = -x (.inl 1) := by linear_combination e2
  have e3' : x (.inr (.inl 2)) = -x (.inl 2) := by linear_combination e3
  rw [e1, e2', e3']

theorem mk7_split (s a b z : F) :
    mk7 s a b s (-a) (-b) z = mk7 s 0 0 s 0 0 z + mk7 0 a b 0 (-a) (-b) 0 := by
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [mk7]
  · fin_cases i <;> simp [mk7]
  · simp [mk7]

section Theta2

variable {φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)} {θ : StatedSp 2 F →* spinGroup (quadOdd 3 F)}

theorem theta_twShort_fix_span (hφ : IsLevi φ)
    (hnat : ∀ g v, spinAction (quadOdd 3 F) (θ g) (kappa v) =
      kappa (spinAction (quadOdd 2 F) (φ g) v))
    (hfix : ∀ g (p : Fin 3 ⊕ Fin 3 ⊕ Unit → F),
      (∀ v, polar (quadOdd 3 F) p (kappa v) = 0) → spinAction (quadOdd 3 F) (θ g) p = p)
    (h2 : (2 : F) ≠ 0) (A : SL(2, F)) {x : Fin 3 ⊕ Fin 3 ⊕ Unit → F} (hx : x ∈ (fr0 h2).span) :
    spinAction (quadOdd 3 F) (θ (twShort h2 A)) x = x := by
  obtain ⟨s, a, b, z, rfl⟩ := mem_span_fr0 h2 hx
  rw [mk7_split, map_add, theta_fix_P hfix, theta_twShort_Pp hφ hnat h2]

end Theta2

section FixComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem La_comm_of_fix (fr : Frame Q) {g : V ≃ₗ[K] V} (hg : ∀ x, Q (g x) = Q x)
    (hfix : ∀ x ∈ fr.span, g x = x) (A : SL(2, K)) : g * fr.La A = fr.La A * g := by
  have hp : ∀ x y, polar Q (g x) (g y) = polar Q x y := fun x y => by
    simp only [QuadraticMap.polar, ← map_add, hg]
  have hmem : ∀ X, fr.incl X ∈ fr.span := fun X => LinearMap.mem_range_self _ _
  have hf1 : g fr.e₁ = fr.e₁ := by
    have := hfix _ (hmem !![1, 0; 0, 0])
    simpa [Frame.incl_apply] using this
  have hf2 : g fr.f₁ = fr.f₁ := by
    have := hfix _ (hmem !![0, 0; 0, 1])
    simpa [Frame.incl_apply] using this
  have he2 : g fr.e₂ = fr.e₂ := by
    have := hfix _ (hmem !![0, -1; 0, 0])
    simpa [Frame.incl_apply] using this
  have hf3 : g fr.f₂ = fr.f₂ := by
    have := hfix _ (hmem !![0, 0; 1, 0])
    simpa [Frame.incl_apply] using this
  have hpol : ∀ x y, g y = y → polar Q (g x) y = polar Q x y := fun x y hy => by
    conv_lhs => rw [← hy]
    exact hp x y
  have hc : ∀ x, fr.coords (g x) = fr.coords x := fun x => by
    simp only [Frame.coords_apply, hpol x _ hf1, hpol x _ hf2, hpol x _ he2, hpol x _ hf3]
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_apply, Frame.La_apply, map_add,
    hfix _ (hmem _), hc]

end FixComm

theorem commutes_of_lift (h2 : (2 : F) ≠ 0) {φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)}
    {θ : StatedSp 2 F →* spinGroup (quadOdd 3 F)} (hφ : IsLevi φ)
    (hnat : ∀ g v, spinAction (quadOdd 3 F) (θ g) (kappa v) =
      kappa (spinAction (quadOdd 2 F) (φ g) v))
    (hfix : ∀ g (p : Fin 3 ⊕ Fin 3 ⊕ Unit → F),
      (∀ v, polar (quadOdd 3 F) p (kappa v) = 0) → spinAction (quadOdd 3 F) (θ g) p = p)
    {R : Subgroup (spinGroup (quadOdd 3 F))} (hperf : ⁅R, R⁆ = R)
    (hR : R.map (spinAction (quadOdd 3 F)) = (fr0 h2).La.range) :
    Commutes R ((twShort h2).range.map θ) := by
  refine CFSG.ClassicalInvolution.RouteD.Gaps.commutes_of_map_commutes
    (ker_spinAction_le_center _) hperf ?_
  rw [hR]
  rintro _ ⟨A, rfl⟩ _ ⟨y, ⟨x, ⟨B, rfl⟩, rfl⟩, rfl⟩
  exact (La_comm_of_fix (fr0 h2) (g := spinAction (quadOdd 3 F) (θ (twShort h2 B)))
    (map_spinAction _ _) (fun x hx => theta_twShort_fix_span hφ hnat hfix h2 B hx) A).symm

end CFSG.ClassicalInvolution.PhanB3.H
