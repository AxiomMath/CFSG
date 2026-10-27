module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutNormal
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.ModelFacts.OrthAut
  (exists_mulRight_of_commute_La exists_scalar_of_commute_La_swap polar_map_of_similitude)
open scoped Matrix MatrixGroups

section Matrices

variable {F : Type} [Field F]

theorem matrix_cayley_hamilton_two (h : Matrix (Fin 2) (Fin 2) F) :
    h * h - h.trace • h + h.det • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem scalar_or_trace_zero {h : Matrix (Fin 2) (Fin 2) F} {c : F}
    (hh : h * h = c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    (∃ s : F, h = s • (1 : Matrix (Fin 2) (Fin 2) F)) ∨ h.det = -c := by
  have hch := matrix_cayley_hamilton_two h
  rw [hh] at hch
  by_cases ht : h.trace = 0
  · right
    rw [ht, zero_smul, sub_zero, ← add_smul] at hch
    have h00 := congrFun (congrFun hch 0) 0
    simp at h00
    linear_combination h00
  · left
    refine ⟨(h.trace)⁻¹ * (c + h.det), ?_⟩
    have : h.trace • h = (c + h.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [add_smul]
      have := hch
      rw [sub_add_eq_add_sub, sub_eq_zero] at this
      exact this.symm
    calc h = (h.trace)⁻¹ • (h.trace • h) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = _ := by rw [this, smul_smul]

end Matrices

section Swap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem coords_eq_zero_polar {fr : Frame Q} {w : V} (hw : fr.coords w = 0) :
    polar Q w fr.f₁ = 0 ∧ polar Q w fr.f₂ = 0 ∧ polar Q w fr.e₂ = 0 ∧ polar Q w fr.e₁ = 0 := by
  have h00 := congrFun (congrFun hw 0) 0
  have h01 := congrFun (congrFun hw 0) 1
  have h10 := congrFun (congrFun hw 1) 0
  have h11 := congrFun (congrFun hw 1) 1
  simp [Frame.coords_apply] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem commutes_swap_of_commutes_La (g : V →ₗ[F] V) (hg : Function.Injective g) {μ : F}
    (hμ : ∀ x, Q (g x) = μ * Q x)
    (hG : ∀ ω ∈ elementaryGroup Q, ∀ z, g (g (ω z)) = ω (g (g z)))
    (fr : Frame Q) (hL : ∀ (A : SL(2, F)) z, g (fr.La A z) = fr.La A (g z))
    (hno : ∀ g' : V →ₗ[F] V, Function.Injective g' →
      (∀ x y, polar Q (g' x) y = -polar Q x (g' y)) →
      (∃ c : F, c ≠ 0 ∧ ∀ x, g' (g' x) = c • x) → False)
    (B : SL(2, F)) (z : V) : g (fr.swap.La B z) = fr.swap.La B (g z) := by
  obtain ⟨h, hh, hperp⟩ := exists_mulRight_of_commute_La fr g hL
  let G : V →ₗ[F] V := g ∘ₗ g
  have hGapp : ∀ x, G x = g (g x) := fun x => rfl
  have hGL : ∀ (A : SL(2, F)) x, G (fr.La A x) = fr.La A (G x) := fun A x =>
    hG _ (fr.La_mem_elementaryGroup A) x
  have hGL' : ∀ (B : SL(2, F)) x, G (fr.swap.La B x) = fr.swap.La B (G x) := fun B x =>
    hG _ (fr.swap.La_mem_elementaryGroup B) x
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_La_swap fr G hGL hGL'
  have hGperp : ∀ w, fr.coords w = 0 → G w = c • w := by
    intro w hw
    obtain ⟨hf1, -, -, he1⟩ := coords_eq_zero_polar hw
    have huw : polar Q fr.e₁ w = 0 := by rw [polar_comm]; exact he1
    have hE := hG (eichler Q fr.e₁ w) (eichler_mem_elementaryGroup Q _ _) fr.f₁
    have hf : fr.f₁ = fr.incl !![0, 0; 0, 1] := by simp [Frame.incl_apply]
    have he : fr.e₁ = fr.incl !![1, 0; 0, 0] := by simp [Frame.incl_apply]
    have hGf : G fr.f₁ = c • fr.f₁ := by
      conv_lhs => rw [hf]
      rw [hc, ← hf]
    have hGe : G fr.e₁ = c • fr.e₁ := by
      conv_lhs => rw [he]
      rw [hc, ← he]
    have hEf : eichler Q fr.e₁ w fr.f₁ = fr.f₁ + w - Q w • fr.e₁ := by
      rw [eichler_apply fr.Q_e₁ huw, fr.polar_f₁_e₁, polar_comm Q fr.f₁ w, hf1]
      simp
    rw [← hGapp, hEf] at hE
    rw [← hGapp, hGf, map_smul, hEf] at hE
    simp only [map_sub, map_add, map_smul, hGf, hGe] at hE
    calc G w = (c • (fr.f₁ + w - Q w • fr.e₁)) - c • fr.f₁ + Q w • c • fr.e₁ := by
          rw [← hE]; abel
      _ = c • w := by module
  have hrperp : ∀ x, fr.coords (x - fr.incl (fr.coords x)) = 0 := fun x => by
    rw [map_sub, Frame.coords_incl, sub_self]
  have hsplit : ∀ x, x = fr.incl (fr.coords x) + (x - fr.incl (fr.coords x)) := fun x => by abel
  have hGall : ∀ x, G x = c • x := by
    intro x
    conv_lhs => rw [hsplit x]
    rw [map_add, hc, hGperp _ (hrperp x), ← smul_add, ← hsplit x]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : ∀ x, g (g x) = 0 := fun x => by rw [← hGapp, hGall, h0, zero_smul]
    have hgx : ∀ x, g x = 0 := fun x => hg (by rw [h1 x, map_zero])
    exact fr.P.e_ne_zero (hg (by rw [hgx fr.e₁, map_zero]))
  have hhh : h * h = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 := hGall (fr.incl 1)
    rw [hGapp, hh, one_mul, hh] at h1
    rw [← map_smul] at h1
    exact fr.incl_injective h1
  have hdet : h.det = μ := by
    have h1 := hμ (fr.incl 1)
    rw [hh, one_mul, Frame.Q_incl, Frame.Q_incl, Matrix.det_one, mul_one] at h1
    exact h1
  rcases scalar_or_trace_zero hhh with ⟨s, rfl⟩ | hdc
  · have hcg : ∀ x, fr.coords (g x) = fr.coords x * (s • (1 : Matrix (Fin 2) (Fin 2) F)) := by
      intro x
      conv_lhs => rw [hsplit x]
      rw [map_add, hh, map_add, Frame.coords_incl, hperp _ (hrperp x), add_zero]
    rw [Frame.La_swap_apply, Frame.La_swap_apply, Frame.embLin_apply_eq, Frame.embLin_apply_eq,
      hcg, map_add, hh, map_sub, hh]
    simp only [LinearMap.mulRight_apply, Matrix.mul_smul, Matrix.mul_one, map_smul]
  · exfalso
    have hμc : μ = -c := hdet.symm.trans hdc
    refine hno g hg ?_ ⟨c, hc0, fun x => by rw [← hGapp, hGall]⟩
    intro x y
    have h1 : polar Q (g x) (g (g y)) = μ * polar Q x (g y) :=
      polar_map_of_similitude g hμ x (g y)
    have hy : g (g y) = c • y := by rw [← hGapp, hGall]
    rw [hy, polar_smul_right, smul_eq_mul, hμc] at h1
    have : c * (polar Q (g x) y + polar Q x (g y)) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc0
    · linear_combination h

end Swap

end CFSG.ClassicalInvolution.RouteD.Exotic
