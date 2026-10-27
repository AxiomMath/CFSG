module

public import CFSG.LieType.Universal.Spin.Forms
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module

theorem even_finrank_of_alternating {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (h2 : (2 : K) ≠ 0) (γ : LinearMap.BilinForm K W)
    (hγ : ∀ u, γ u u = 0) (hsep : ∀ u, (∀ v, γ u v = 0) → u = 0) : Even (finrank K W) := by
  classical
  have hskew : ∀ u v, γ v u = -γ u v := by
    intro u v
    have h := hγ (u + v)
    simp only [map_add, LinearMap.add_apply, hγ u, hγ v, zero_add, add_zero] at h
    linear_combination h
  have hnd : γ.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  set b := Module.finBasis K W
  set M := LinearMap.BilinForm.toMatrix b γ with hM
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd
  have hT : M.transpose = -M := by
    ext i j
    rw [Matrix.transpose_apply, Matrix.neg_apply, hM, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, hskew]
  have h1 : M.det = (-1) ^ finrank K W * M.det := by
    calc M.det = M.transpose.det := (Matrix.det_transpose M).symm
      _ = (-M).det := by rw [hT]
      _ = (-1) ^ finrank K W * M.det := by rw [Matrix.det_neg, Fintype.card_fin]
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow, neg_one_mul] at h1
  apply hdet
  have h2M : (2 : K) * M.det = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2M).resolve_left h2

theorem even_finrank_ker_sub_one_of_isometry {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hnd : (polarBilin Q).Nondegenerate) (hV : Even (finrank K V)) (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg3 : ∀ v, g (g (g v)) = v) :
    Even (finrank K (LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id))) := by
  have hpol : ∀ x y, polar Q (g x) (g y) = polar Q x y :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg
  set F := LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id) with hFdef
  set W := LinearMap.ker (LinearMap.id + (g : V →ₗ[K] V) + (g : V →ₗ[K] V) ∘ₗ (g : V →ₗ[K] V))
    with hWdef
  have hF : ∀ v, v ∈ F ↔ g v = v := fun v => by
    rw [hFdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hW : ∀ v, v ∈ W ↔ v + g v + g (g v) = 0 := fun v => by
    rw [hWdef, LinearMap.mem_ker]
    rfl
  have h3inv : (3 : K)⁻¹ * 3 = 1 := inv_mul_cancel₀ h3
  have hinf : F ⊓ W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvF, hvW⟩ := Submodule.mem_inf.1 hv
    rw [hF] at hvF
    rw [hW, hvF, hvF] at hvW
    have h : (3 : K) • v = 0 := by
      rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
      exact hvW
    exact (smul_eq_zero.1 h).resolve_left h3
  have hsup : F ⊔ W = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hv1 : (3 : K)⁻¹ • (v + g v + g (g v)) ∈ F := by
      rw [hF, map_smul, map_add, map_add, hg3]
      congr 1
      abel
    have hv2 : v - (3 : K)⁻¹ • (v + g v + g (g v)) ∈ W := by
      rw [hW]
      simp only [map_sub, map_smul, map_add, hg3]
      rw [show v - (3 : K)⁻¹ • (v + g v + g (g v)) + (g v - (3 : K)⁻¹ • (g v + g (g v) + v)) +
          (g (g v) - (3 : K)⁻¹ • (g (g v) + v + g v)) =
          ((1 : K) - (3 : K)⁻¹ * 3) • (v + g v + g (g v)) by module, h3inv, sub_self, zero_smul]
    have h := Submodule.add_mem_sup hv1 hv2
    rwa [add_sub_cancel] at h
  have hdim : finrank K F + finrank K W = finrank K V := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq F W
    rw [hsup, hinf, finrank_top, finrank_bot, add_zero] at h
    exact h.symm
  have hFW : ∀ x ∈ F, ∀ w ∈ W, polar Q x w = 0 := by
    intro x hx w hw
    rw [hF] at hx
    rw [hW] at hw
    have e1 : polar Q x (g w) = polar Q x w := by rw [← hpol x w, hx]
    have e2 : polar Q x (g (g w)) = polar Q x w := by
      calc polar Q x (g (g w)) = polar Q (g x) (g (g w)) := by rw [hx]
        _ = polar Q x (g w) := hpol x (g w)
        _ = polar Q x w := e1
    have e3 := congrArg (polar Q x) hw
    rw [polar_add_right, polar_add_right, e1, e2, polar_zero_right] at e3
    have h3' : (3 : K) * polar Q x w = 0 := by linear_combination e3
    exact (mul_eq_zero.1 h3').resolve_left h3
  have hWg : ∀ w ∈ W, g w ∈ W := fun w hw => by
    rw [hW] at hw ⊢
    rw [hg3]
    rw [← hw]
    abel
  let γ : LinearMap.BilinForm K W := (polarBilin Q).compl₁₂ W.subtype
    (((g : V →ₗ[K] V) - (g : V →ₗ[K] V) ∘ₗ (g : V →ₗ[K] V)) ∘ₗ W.subtype)
  have hγ : ∀ u v : W, γ u v = polar Q (u : V) (g v - g (g v)) := fun u v => rfl
  have halt : ∀ u, γ u u = 0 := by
    intro u
    rw [hγ, polar_sub_right]
    have e : polar Q (u : V) (g (g u)) = polar Q (u : V) (g u) := by
      rw [← hpol (u : V) (g (g u)), hg3, polar_comm]
    rw [e, sub_self]
  have hsep : ∀ u, (∀ v, γ u v = 0) → u = 0 := by
    intro u hu
    have hW0 : ∀ w ∈ W, polar Q (u : V) w = 0 := by
      intro w hw
      have hvW : (3 : K)⁻¹ • ((2 : K) • g (g w) + w) ∈ W :=
        W.smul_mem _ (W.add_mem (W.smul_mem _ (hWg _ (hWg _ hw))) hw)
      have hgv : g ((3 : K)⁻¹ • ((2 : K) • g (g w) + w)) -
          g (g ((3 : K)⁻¹ • ((2 : K) • g (g w) + w))) = w := by
        rw [hW] at hw
        simp only [map_smul, map_add, hg3]
        have hgw : g (g w) = -w - g w := by rw [← sub_eq_zero, ← hw]; abel
        rw [hgw]
        rw [show (3 : K)⁻¹ • ((2 : K) • w + g w) - (3 : K)⁻¹ • ((2 : K) • g w + (-w - g w)) =
            ((3 : K)⁻¹ * 3) • w by module, h3inv, one_smul]
      have h := hu ⟨_, hvW⟩
      rw [hγ] at h
      simp only at h
      rwa [hgv] at h
    apply Subtype.ext
    refine hnd.1 (u : V) fun y => ?_
    have hy : y ∈ F ⊔ W := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    change polar Q (u : V) (x + w) = 0
    rw [polar_add_right, hW0 w hw, polar_comm, hFW x hx (u : V) u.2, zero_add]
  have hWeven := even_finrank_of_alternating h2 γ halt hsep
  have h := (Nat.even_add.1 (hdim ▸ hV : Even (finrank K F + finrank K W))).2 hWeven
  exact h

theorem even_finrank_ker_sub_one {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 4 K))
    (hg3 : ∀ v, g (g (g v)) = v) :
    Even (Module.finrank K (LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) - LinearMap.id))) :=
  even_finrank_ker_sub_one_of_isometry
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 K) ⟨4, by simp⟩ h2 h3 hg hg3

end CFSG.HardMathSupport.Timmesfeld.DFour
