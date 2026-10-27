module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
public import CFSG.ClassicalGroups.Orthogonal.Restrict
import CFSG.ClassicalInvolution.SmallOrth.Primitive
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthIso
import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ClassicalInvolution.Asc77.SCV

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalGroups.Orthogonal.Small CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

section Mat

variable {F : Type*} [Field F]

theorem mat_sq_cases (h : Matrix (Fin 2) (Fin 2) F) {s : F}
    (hs : h * h = s • (1 : Matrix (Fin 2) (Fin 2) F)) :
    (∃ c : F, h = c • (1 : Matrix (Fin 2) (Fin 2) F)) ∨ h.det = -s := by
  have e00 := congrFun (congrFun hs 0) 0
  have e01 := congrFun (congrFun hs 0) 1
  have e10 := congrFun (congrFun hs 1) 0
  have e11 := congrFun (congrFun hs 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases htr : h 0 0 + h 1 1 = 0
  · right
    rw [Matrix.det_fin_two]
    have h11 : h 1 1 = -h 0 0 := by linear_combination htr
    rw [h11]
    linear_combination -e00
  · left
    have hb : h 0 1 = 0 := by
      have : h 0 1 * (h 0 0 + h 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right htr
    have hc : h 1 0 = 0 := by
      have : h 1 0 * (h 0 0 + h 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right htr
    have hd : h 0 0 = h 1 1 := by
      have : (h 0 0 - h 1 1) * (h 0 0 + h 1 1) = 0 := by
        rw [hb, hc] at e00 e11
        linear_combination e00 - e11
      have := (mul_eq_zero.mp this).resolve_right htr
      linear_combination this
    refine ⟨h 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd]

end Mat

section Frame

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem comm_swap_of_scalar (fr : Frame Q) (a : V →ₗ[F] V) (c : F)
    (hc : ∀ Y, a (fr.incl Y) = c • fr.incl Y)
    (hperp : ∀ x, fr.coords x = 0 → fr.coords (a x) = 0) (B : SL(2, F)) (x : V) :
    a (fr.swap.La B x) = fr.swap.La B (a x) := by
  have hr : fr.coords (x - fr.incl (fr.coords x)) = 0 := by
    rw [map_sub, Frame.coords_incl, sub_self]
  have hax : a x = c • fr.incl (fr.coords x) + a (x - fr.incl (fr.coords x)) := by
    rw [← hc, ← map_add]
    congr 1
    abel
  have hcax : fr.coords (a x) = c • fr.coords x := by
    rw [hax, map_add, map_smul, Frame.coords_incl, hperp _ hr, add_zero]
  rw [Frame.La_swap_apply, Frame.La_swap_apply, Frame.embLin_apply, Frame.embLin_apply, map_add,
    hc, hcax]
  simp only [LinearMap.mulRight_apply, map_sub, map_smul, smul_sub]

end Frame

section Skew

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem false_of_skew [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) (hW1 : ∀ P P' : HypPair Q, ¬ P.Orth P')
    (h3 : 3 ≤ Module.finrank F V) (a : V →ₗ[F] V) {s : F} (hs : s ≠ 0)
    (ha2 : ∀ x, a (a x) = s • x) (haQ : ∀ x, Q (a x) = (-s) * Q x) : False := by
  have hpol : ∀ x y, polar Q (a x) (a y) = (-s) * polar Q x y := by
    intro x y
    have h1 := haQ (x + y)
    rw [map_add, QuadraticMap.map_add Q, QuadraticMap.map_add Q, haQ x, haQ y] at h1
    linear_combination h1
  have hw : ∀ w, polar Q w (a w) = 0 := by
    intro w
    have h1 := hpol w (a w)
    rw [ha2 w, polar_smul_right_eq, polar_comm Q (a w) w] at h1
    have h2' : (2 * s) * polar Q w (a w) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2').resolve_left (mul_ne_zero h2 hs)
  obtain ⟨e, he0, heQ⟩ := exists_isotropic_of_finrank_ge_three hodd Q hQ h3
  have haeQ : Q (a e) = 0 := by rw [haQ, heQ, mul_zero]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_polar_eq_zero_of_noOrth hQ hW1 heQ he0 haeQ (hw e)
  have hcs : c ^ 2 = s := by
    have h1 : s • e = (c ^ 2) • e := by
      rw [← ha2 e, hc, map_smul, hc, smul_smul, _root_.sq]
    have h2' : (s - c ^ 2) • e = 0 := by rw [sub_smul, h1, sub_self]
    have := (smul_eq_zero.mp h2').resolve_right he0
    linear_combination -this
  have hc0 : c ≠ 0 := by
    intro h0
    apply hs
    rw [← hcs, h0]
    ring
  set Up : Submodule F V := LinearMap.ker (a - c • LinearMap.id) with hUp
  set Um : Submodule F V := LinearMap.ker (a + c • LinearMap.id) with hUm
  have hUpmem : ∀ x, x ∈ Up ↔ a x = c • x := fun x => by
    rw [hUp, LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hUmmem : ∀ x, x ∈ Um ↔ a x = -(c • x) := fun x => by
    rw [hUm, LinearMap.mem_ker]
    simp [add_eq_zero_iff_eq_neg]
  have hQ0 : ∀ x, (a x = c • x ∨ a x = -(c • x)) → Q x = 0 := by
    intro x hx
    have h1 : Q (a x) = c ^ 2 * Q x := by
      rcases hx with hx | hx
      · rw [hx, map_smul_eq_sq]
      · rw [hx, QuadraticMap.map_neg, map_smul_eq_sq]
    rw [haQ, hcs] at h1
    have h2' : (2 * s) * Q x = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2').resolve_left (mul_ne_zero h2 hs)
  have hone : ∀ (W : Submodule F V), (∀ x ∈ W, Q x = 0) → Module.finrank F W ≤ 1 := by
    intro W hW
    by_cases hWz : ∀ x ∈ W, x = 0
    · have : Subsingleton W := ⟨fun x y => Subtype.ext (by rw [hWz x x.2, hWz y y.2])⟩
      have : Module.finrank F W = 0 := Module.finrank_zero_of_subsingleton
      omega
    · push Not at hWz
      obtain ⟨x, hxW, hx0⟩ := hWz
      refine finrank_le_one (⟨x, hxW⟩ : W) fun y => ?_
      have hy : Q (y : V) = 0 := hW y y.2
      have hxy : polar Q x (y : V) = 0 := by
        have h1 := hW (x + (y : V)) (W.add_mem hxW y.2)
        rw [QuadraticMap.map_add Q, hW x hxW, hy] at h1
        linear_combination h1
      obtain ⟨d, hd⟩ := exists_eq_smul_of_polar_eq_zero_of_noOrth hQ hW1 (hW x hxW) hx0 hy hxy
      exact ⟨d, Subtype.ext hd.symm⟩
  have hUp1 := hone Up (fun x hx => hQ0 x (Or.inl ((hUpmem x).mp hx)))
  have hUm1 := hone Um (fun x hx => hQ0 x (Or.inr ((hUmmem x).mp hx)))
  have htop : (⊤ : Submodule F V) ≤ Up ⊔ Um := by
    intro x _
    have hx : x = (2 : F)⁻¹ • (x + c⁻¹ • a x) + (2 : F)⁻¹ • (x - c⁻¹ • a x) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul F x, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hx]
    refine add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ ?_))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ ?_))
    · have h1 : c⁻¹ • (s • x) = c • x := by
        rw [smul_smul, ← hcs, _root_.sq, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      have h2'' : c • (c⁻¹ • a x) = a x := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      rw [hUpmem, map_add, map_smul, ha2, smul_add, h2'', h1, add_comm]
    · have h1 : c⁻¹ • (s • x) = c • x := by
        rw [smul_smul, ← hcs, _root_.sq, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      have h2'' : c • (c⁻¹ • a x) = a x := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      rw [hUmmem, map_sub, map_smul, ha2, smul_sub, h2'', h1, neg_sub]
  have h1 := Submodule.finrank_mono htop
  rw [finrank_top] at h1
  have h2' := Submodule.finrank_add_le_finrank_add_finrank Up Um
  omega

end Skew

section Frames

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_frame_le_of_orth {W : Submodule F V} {P P' : HypPair (Q.restrict W)}
    (h : P.Orth P') : ∃ F₂ : Frame Q, F₂.span ≤ W := by
  refine ⟨⟨⟨(P.e : V), (P.f : V), P.Q_e, P.Q_f, by simpa [polar_restrict] using P.polar_ef⟩,
    ⟨(P'.e : V), (P'.f : V), P'.Q_e, P'.Q_f, by simpa [polar_restrict] using P'.polar_ef⟩,
    ⟨by simpa [polar_restrict] using h.ee, by simpa [polar_restrict] using h.ef,
      by simpa [polar_restrict] using h.fe, by simpa [polar_restrict] using h.ff⟩⟩, ?_⟩
  rintro _ ⟨X, rfl⟩
  rw [Frame.incl_apply]
  exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ P.e.2) (W.smul_mem _ P.f.2))
    (W.smul_mem _ P'.e.2)) (W.smul_mem _ P'.f.2)

end Frames

end CFSG.ClassicalInvolution.Asc77.SCV
