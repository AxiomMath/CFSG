module

public import CFSG.ClassicalInvolution.Asc77.AscT7OH
public import CFSG.ClassicalInvolution.Asc77.AscT7OA
public import CFSG.ClassicalInvolution.Asc77.AscT7OG

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.Dichotomy QuadraticMap
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Finite F] [FiniteDimensional F V] {X : Type} [Group X] [Finite X]

theorem alphaOf_klein_of_complex (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (fr : Frame Q) (hV : 7 ≤ Module.finrank F V)
    (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e) [e.range.Normal]
    {A : V ≃ₗ[F] V} (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hA2 : ∀ x, A (A x) = -x) (hAz : A * fr.La (-1) = fr.La (-1) * A)
    (hAK : ∀ B : SL(2, F), A * fr.swap.La B = fr.swap.La B * A) {y : X} (hy : ActsAs e y A)
    (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hzy1 : e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ * y ≠ 1)
    (hz1 : e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ ≠ 1)
    (hz : ∀ n ∈ involutionOddCore (e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩), n = 1) :
    alphaOf (Subgroup.closure ({e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩, y} :
      Set X)) = ⊥ := by
  classical
  set zE : ↥(elementaryGroup Q) := ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ with hzE
  set z : X := e zE with hzdef
  have hz2 : z * z = 1 := e_La_neg_one_sq e fr
  have hLO : fr.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Frame.La_mem_orthogonalGroup fr (-1)
  have hE := commutator_orth_le_of_frame hodd hQ fr hV
  have hzy : z * y = y * z := by
    have h := hy zE zE (by
      change fr.La (-1) = A * fr.La (-1) * A⁻¹
      symm
      rw [mul_inv_eq_iff_eq_mul]
      exact hAz)
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hS := cplxLayer hodd hQ hAO hA2 (by omega) hE
  have hzS : fr.La (-1) ∈ cplxS Q A := La_neg_one_mem_layer h5 fr hS hAK
  have hzP : z ∈ img e (cplxS Q A) := (mem_img_iff e).mpr ⟨zE, hzS, rfl⟩
  have d₁ : LayerData e.range (Subgroup.closure ({z, y} : Set X)) y (img e (cplxS Q A)) := by
    refine layerData_of_outer e hker hAO hy hS _ ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro g (hg | hg)
    · rw [hg]; exact Subgroup.mem_sup_right hzP
    · rw [hg]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  set A' : V ≃ₗ[F] V := fr.La (-1) * A with hA'def
  have hA'O : A' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hLO hAO
  have hA'2 : ∀ x, A' (A' x) = -x := by
    intro x
    have hc : ∀ u, fr.La (-1) (A u) = A (fr.La (-1) u) := fun u =>
      congrArg (fun m : V ≃ₗ[F] V => m u) hAz.symm
    have hLL : ∀ u, fr.La (-1) (fr.La (-1) u) = u := fun u =>
      congrArg (fun m : V ≃ₗ[F] V => m u) fr.La_neg_one_mul_self
    simp only [hA'def, LinearEquiv.mul_apply]
    rw [hc, hLL, hA2]
  have hA'z : A' * fr.La (-1) = fr.La (-1) * A' := by
    calc A' * fr.La (-1) = fr.La (-1) * (A * fr.La (-1)) := by rw [hA'def, mul_assoc]
      _ = fr.La (-1) * (fr.La (-1) * A) := by rw [hAz]
      _ = fr.La (-1) * A' := rfl
  have hA'K : ∀ B : SL(2, F), A' * fr.swap.La B = fr.swap.La B * A' := by
    intro B
    rw [hA'def, mul_assoc, hAK B, ← mul_assoc, ← mul_assoc, fr.La_swap_neg_one_comm B]
  have hA : ActsAs e (z * y) A' := by
    intro g h hgh
    have hmem : A * (g : V ≃ₗ[F] V) * A⁻¹ ∈ elementaryGroup Q :=
      conj_mem_elementaryGroup hAO g.2
    have h1 := hy g ⟨A * g * A⁻¹, hmem⟩ rfl
    have hh : (h : V ≃ₗ[F] V) = fr.La (-1) * (A * g * A⁻¹) * (fr.La (-1))⁻¹ := by
      rw [hgh, hA'def, mul_inv_rev]; group
    have h2 : e zE * e ⟨A * g * A⁻¹, hmem⟩ * (e zE)⁻¹ = e h := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hh.symm
    calc z * y * e g * (z * y)⁻¹ = z * (y * e g * y⁻¹) * z⁻¹ := by group
      _ = e h := by rw [h1, ← h2]
  have hS' := cplxLayer hodd hQ hA'O hA'2 (by omega) hE
  have hzS' : fr.La (-1) ∈ cplxS Q A' := La_neg_one_mem_layer h5 fr hS' hA'K
  have hzP' : z ∈ img e (cplxS Q A') := (mem_img_iff e).mpr ⟨zE, hzS', rfl⟩
  have d₂ : LayerData e.range (Subgroup.closure ({z, y} : Set X)) (z * y)
      (img e (cplxS Q A')) := by
    refine layerData_of_outer e hker hA'O hA hS' _ ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro g (hg | hg)
    · rw [hg]; exact Subgroup.mem_sup_right hzP'
    · have hy' : g = z * (z * y) := by rw [hg, ← mul_assoc, hz2, one_mul]
      rw [hy']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzP')
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  exact alphaOf_klein_outer_of_oddCore e.range hz2 hy2 hzy hz1 hy1 hzy1 d₁ d₂ hz

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
