module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Pair
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Mod

public section

namespace CFSG.GH74.GLS.IVK

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E} {Y : Subgroup (sesqUnitaryGroup B)}

namespace PairedSL

variable (P : PairedSL h B Y)

theorem eigen_dichotomy (h2 : (2 : E) ≠ 0) (τ : V →ₛₗ[h.bar] V) (hτ : Function.Bijective τ)
    (d : E) (hTτ : ∀ v, unitaryOp P.T (τ v) = d • τ (unitaryOp P.T v)) :
    (∀ v ∈ P.Vp, τ v ∈ P.Vp) ∨ (∀ v ∈ P.Vp, τ v ∈ P.Vm) := by
  have hT : ∀ v ∈ P.Vp, unitaryOp P.T (τ v) = (d * h.bar P.l) • τ v := by
    intro v hv
    rw [hTτ, P.T_p v hv, map_smulₛₗ, smul_smul]
  obtain ⟨v₀, hv₀, hv₀0⟩ := P.exists_ne_zero
  have hx0 : τ v₀ ≠ 0 := fun h0 => hv₀0 (hτ.1 (h0.trans (map_zero τ).symm))
  have h3 : ((d * h.bar P.l) ^ 2 - P.l ^ 2) • τ v₀ = 0 := by
    rw [sub_smul, ← P.T_sq (τ v₀), hT v₀ hv₀, map_smul, hT v₀ hv₀, smul_smul, pow_two, sub_self]
  have h4 : (d * h.bar P.l - P.l) * (d * h.bar P.l + P.l) = 0 := by
    have := (smul_eq_zero.mp h3).resolve_right hx0
    linear_combination this
  rcases mul_eq_zero.mp h4 with h5 | h5
  · left
    intro v hv
    apply P.mem_Vp_of_eigen h2
    rw [hT v hv, sub_eq_zero.mp h5]
  · right
    intro v hv
    apply P.mem_Vm_of_eigen h2
    rw [hT v hv, eq_neg_of_add_eq_zero_left h5, neg_smul]


theorem not_keep (τ : V →ₛₗ[h.bar] V) (hτ : Function.Bijective τ)
    (hτY : ∀ y ∈ Y, ∀ v, unitaryOp y (τ v) = τ (unitaryOp y v))
    (hkeep : ∀ v ∈ P.Vp, τ v ∈ P.Vp) : False := by
  let T' : (Fin 2 → E) →+ (Fin 2 → E) :=
    AddMonoidHom.mk' (fun u => P.cp ⟨τ (P.vec u), hkeep _ (P.vec_mem u)⟩) (by
      intro u u'
      rw [← map_add]
      congr 1
      apply Subtype.ext
      simp only [vec_add, map_add, Submodule.coe_add])
  have hvecT' : ∀ u, P.vec (T' u) = τ (P.vec u) := by
    intro u
    exact P.vec_cp ⟨τ (P.vec u), hkeep _ (P.vec_mem u)⟩
  have hT : ∀ (a : E) (v : Fin 2 → E), T' (a • v) = barEquiv h a • T' v := by
    intro a v
    apply P.vec_injective
    rw [hvecT', vec_smul, map_smulₛₗ, vec_smul, hvecT']
    rfl
  have hc : ∀ g : SpecialLinearGroup (Fin 2) E, ∀ v : Fin 2 → E,
      T' ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) E) *ᵥ T' v := by
    intro g v
    obtain ⟨y, hy, hyv⟩ := P.surj_vec g
    apply P.vec_injective
    rw [hvecT', hyv, hyv, hvecT', hτY y hy]
  have h0 := sl2_semilinear_commutant_zero (barEquiv h) (barEquiv_ne_one h) T' hT hc
  obtain ⟨v₀, hv₀, hv₀0⟩ := P.exists_ne_zero
  obtain ⟨u₀, hu₀⟩ := P.exists_vec hv₀
  have h1 : T' u₀ = 0 := by rw [h0]; rfl
  have h2 : τ v₀ = 0 := by
    rw [← hu₀, ← hvecT', h1, P.vec_zero]
  exact hv₀0 (hτ.1 (h2.trans (map_zero τ).symm))

theorem swap_neg (hB : B.IsSymm) (τ : V →ₛₗ[h.bar] V) (hτ : Function.Bijective τ)
    (hτB : ∀ v w, B (τ v) (τ w) = h.bar (B v w)) (μ : E) (hμ : ∀ v, τ (τ v) = μ • v)
    (hτY : ∀ y ∈ Y, ∀ v, unitaryOp y (τ v) = τ (unitaryOp y v))
    (h2 : (2 : E) ≠ 0) (hswap : ∀ v ∈ P.Vp, τ v ∈ P.Vm) : μ = -1 := by
  let G : (Fin 2 → E) → (Fin 2 → E) → E := fun u w => B (P.vec u) (τ (P.vec w))
  have hG1 : ∀ a u w, G (a • u) w = h.bar a * G u w := by
    intro a u w
    simp only [G, vec_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  have hG2 : ∀ a u w, G u (a • w) = h.bar a * G u w := by
    intro a u w
    simp only [G, vec_smul, map_smulₛₗ, smul_eq_mul, RingHom.id_apply]
  have hGa1 : ∀ u u' w, G (u + u') w = G u w + G u' w := by
    intro u u' w
    simp only [G, vec_add, map_add, LinearMap.add_apply]
  have hGa2 : ∀ u w w', G u (w + w') = G u w + G u w' := by
    intro u w w'
    simp only [G, vec_add, map_add]
  let F : (Fin 2 → E) →ₗ[E] (Fin 2 → E) →ₗ[E] E :=
    LinearMap.mk₂ E (fun u w => h.bar (G u w))
      (fun u u' w => by rw [hGa1, map_add])
      (fun a u w => by rw [hG1, map_mul, h.bar_bar, smul_eq_mul])
      (fun u w w' => by rw [hGa2, map_add])
      (fun a u w => by rw [hG2, map_mul, h.bar_bar, smul_eq_mul])
  have hF : ∀ u w, F u w = h.bar (G u w) := fun u w => rfl
  have hinv : ∀ g : SpecialLinearGroup (Fin 2) E, ∀ u v : Fin 2 → E,
      F ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ u) ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ v) = F u v := by
    intro g u v
    obtain ⟨y, hy, hyv⟩ := P.surj_vec g
    rw [hF, hF]
    simp only [G, hyv]
    rw [← hτY y hy]
    exact congrArg h.bar (y.2 _ _)
  have hskew := sl2_invariant_bilinear_skew h2 F hinv
  have hGskew : ∀ u w, G u w = - G w u := by
    intro u w
    have := hskew u w
    rw [hF, hF, ← map_neg] at this
    have h3 := congrArg h.bar this
    rwa [h.bar_bar, h.bar_bar] at h3
  have hrel : ∀ u w, h.bar (G w u) = μ * h.bar (G u w) := by
    intro u w
    have h3 := hτB (P.vec w) (τ (P.vec u))
    rw [hμ, map_smul, smul_eq_mul, ← hB.eq (P.vec u) (τ (P.vec w))] at h3
    exact h3.symm
  obtain ⟨w₀, hw₀, hw₀0⟩ := P.exists_ne_zero
  obtain ⟨u₀, hu₀⟩ := P.exists_vec hw₀
  have hτw₀ : τ w₀ ≠ 0 := fun h0 => hw₀0 (hτ.1 (h0.trans (map_zero τ).symm))
  have hex : ∃ v ∈ P.Vp, B v (τ w₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hτw₀ (P.pair_m _ (hswap w₀ hw₀) hcon)
  obtain ⟨v₁, hv₁, hv₁0⟩ := hex
  obtain ⟨u₁, hu₁⟩ := P.exists_vec hv₁
  have hne : G u₁ u₀ ≠ 0 := by
    simp only [G, hu₁, hu₀]
    exact hv₁0
  have h5 := hrel u₁ u₀
  rw [hGskew u₀ u₁, map_neg] at h5
  have h6 : (μ + 1) * h.bar (G u₁ u₀) = 0 := by linear_combination -h5
  have h7 : h.bar (G u₁ u₀) ≠ 0 := fun h0 => hne (h.bar.injective (by rw [h0, map_zero]))
  have h8 := (mul_eq_zero.mp h6).resolve_right h7
  linear_combination h8

theorem antiunitary_neg (h2 : (2 : E) ≠ 0) (hB : B.IsSymm)
    (τ : V →ₛₗ[h.bar] V) (hτ : Function.Bijective τ)
    (hτB : ∀ v w, B (τ v) (τ w) = h.bar (B v w)) (μ : E) (hμ : ∀ v, τ (τ v) = μ • v)
    (hτY : ∀ y ∈ Y, ∀ v, unitaryOp y (τ v) = τ (unitaryOp y v))
    (d : E) (hTτ : ∀ v, unitaryOp P.T (τ v) = d • τ (unitaryOp P.T v)) : μ = -1 := by
  rcases P.eigen_dichotomy h2 τ hτ d hTτ with hkeep | hswap
  · exact (P.not_keep τ hτ hτY hkeep).elim
  · exact P.swap_neg hB τ hτ hτB μ hμ hτY h2 hswap

end PairedSL

end CFSG.GH74.GLS.IVK
