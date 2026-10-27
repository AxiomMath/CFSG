module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped Pointwise

theorem exists_mulEquiv_inf_centralizer {X : Type*} [Group X] {D₁ D₂ : Subgroup X} {a : X}
    (ha : a * a = 1) (hcomm : ⁅D₁, D₂⁆ = ⊥) (hinf : D₁ ⊓ D₂ = ⊥)
    (hconj : D₁.map (MulAut.conj a⁻¹).toMonoidHom = D₂) :
    ∃ φ : ↥D₁ ≃* ↥((D₁ ⊔ D₂) ⊓ centralizer ({a} : Set X)),
      ∀ d : ↥D₁, ((φ d : ↥((D₁ ⊔ D₂) ⊓ centralizer ({a} : Set X))) : X) =
        (d : X) * (a⁻¹ * (d : X) * a) := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have key : ∀ x : X, a⁻¹ * (a⁻¹ * x * a) * a = x := by
    intro x
    rw [hinv]
    calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha, one_mul, mul_one]
  have hcen : ∀ d ∈ D₁, ∀ e ∈ D₂, d * e = e * d := by
    intro d hd e he
    have hle : D₁ ≤ centralizer (D₂ : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact ((Subgroup.mem_centralizer_iff.mp (hle hd)) e he).symm
  have hu : ∀ d ∈ D₁, a⁻¹ * d * a ∈ D₂ := by
    intro d hd
    rw [← hconj]
    exact Subgroup.mem_map.mpr ⟨d, hd, by simp [MulAut.conj_apply]⟩
  have hv : ∀ e ∈ D₂, a⁻¹ * e * a ∈ D₁ := by
    intro e he
    rw [← hconj] at he
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp he
    have h1 : a⁻¹ * ((MulAut.conj a⁻¹).toMonoidHom d) * a = d := by
      simpa [MulAut.conj_apply] using key d
    rw [h1]
    exact hd
  have conj_fix : ∀ x : X, a⁻¹ * x * a = x → x * a = a * x := by
    intro x h
    rw [hinv] at h
    calc x * a = (a * a) * x * a := by rw [ha, one_mul]
      _ = a * (a * x * a) := by simp only [mul_assoc]
      _ = a * x := by rw [h]
  have hmem : ∀ d ∈ D₁, d * (a⁻¹ * d * a) ∈ (D₁ ⊔ D₂) ⊓ centralizer ({a} : Set X) := by
    intro d hd
    refine Subgroup.mem_inf.mpr ⟨mul_mem (Subgroup.mem_sup_left hd)
      (Subgroup.mem_sup_right (hu d hd)), ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr (conj_fix _ ?_)
    calc a⁻¹ * (d * (a⁻¹ * d * a)) * a
        = (a⁻¹ * d * a) * (a⁻¹ * (a⁻¹ * d * a) * a) := by group
      _ = (a⁻¹ * d * a) * d := by rw [key d]
      _ = d * (a⁻¹ * d * a) := (hcen d hd _ (hu d hd)).symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥D₁ →* ↥((D₁ ⊔ D₂) ⊓ centralizer ({a} : Set X)),
      ∀ d : ↥D₁, ((ψ d : ↥((D₁ ⊔ D₂) ⊓ centralizer ({a} : Set X))) : X) =
        (d : X) * (a⁻¹ * (d : X) * a) := by
    have hmulval : ∀ d d' : ↥D₁, ((d * d' : ↥D₁) : X) * (a⁻¹ * ((d * d' : ↥D₁) : X) * a) =
        ((d : X) * (a⁻¹ * (d : X) * a)) * ((d' : X) * (a⁻¹ * (d' : X) * a)) := by
      intro d d'
      rw [Subgroup.coe_mul]
      have hc : (d' : X) * (a⁻¹ * (d : X) * a) = (a⁻¹ * (d : X) * a) * (d' : X) :=
        hcen _ d'.2 _ (hu _ d.2)
      calc (d : X) * (d' : X) * (a⁻¹ * ((d : X) * (d' : X)) * a)
          = (d : X) * ((d' : X) * (a⁻¹ * (d : X) * a)) * (a⁻¹ * (d' : X) * a) := by group
        _ = (d : X) * ((a⁻¹ * (d : X) * a) * (d' : X)) * (a⁻¹ * (d' : X) * a) := by rw [hc]
        _ = ((d : X) * (a⁻¹ * (d : X) * a)) * ((d' : X) * (a⁻¹ * (d' : X) * a)) := by
          simp only [mul_assoc]
    exact ⟨{ toFun := fun d => ⟨(d : X) * (a⁻¹ * (d : X) * a), hmem (d : X) d.2⟩,
             map_one' := Subtype.ext (by simp),
             map_mul' := fun d d' => Subtype.ext (hmulval d d') }, fun d => rfl⟩
  have step : ∀ p q e₁ e₂ : X, p ∈ D₂ → q ∈ D₁ → e₁ ∈ D₁ → e₂ ∈ D₂ →
      q * p = e₁ * e₂ → e₁ = q ∧ e₂ = p := by
    intro p q e₁ e₂ hp hq he₁ he₂ h
    have h1 : q⁻¹ * e₁ = p * e₂⁻¹ := by
      calc q⁻¹ * e₁ = q⁻¹ * (e₁ * e₂) * e₂⁻¹ := by group
        _ = q⁻¹ * (q * p) * e₂⁻¹ := by rw [h]
        _ = p * e₂⁻¹ := by group
    have h2 : q⁻¹ * e₁ ∈ D₁ ⊓ D₂ := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hq) he₁, ?_⟩
      rw [h1]
      exact mul_mem hp (inv_mem he₂)
    rw [hinf, Subgroup.mem_bot] at h2
    have he1 : e₁ = q := (inv_mul_eq_one.mp h2).symm
    refine ⟨he1, ?_⟩
    rw [he1] at h
    exact (mul_left_cancel h).symm
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hval : (d : X) * (a⁻¹ * (d : X) * a) = 1 :=
      (hψ d).symm.trans (congrArg Subtype.val hd)
    have hdD₂ : (d : X) ∈ D₂ := by
      have h := inv_mem (hu _ d.2)
      rwa [← eq_inv_of_mul_eq_one_left hval] at h
    have hbot : (d : X) ∈ D₁ ⊓ D₂ := Subgroup.mem_inf.mpr ⟨d.2, hdD₂⟩
    rw [hinf, Subgroup.mem_bot] at hbot
    exact Subtype.ext hbot
  have hsurj : Function.Surjective ψ := by
    rintro ⟨x, hxC⟩
    obtain ⟨hxsup, hxcent⟩ := Subgroup.mem_inf.mp hxC
    have hLE : D₁ ≤ Subgroup.normalizer (D₂ : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right D₁ D₂ hLE
    have hxmul : x ∈ (D₁ : Set X) * (D₂ : Set X) := by
      rw [← hset]
      exact hxsup
    obtain ⟨d₁, hd₁, d₂, hd₂, hx_eq⟩ := Set.mem_mul.mp hxmul
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hxcent
    have hax : a⁻¹ * x * a = x := by
      rw [hinv]
      calc a * x * a = a * (x * a) := by simp only [mul_assoc]
        _ = a * (a * x) := by rw [hxa]
        _ = (a * a) * x := by simp only [mul_assoc]
        _ = x := by rw [ha, one_mul]
    have hpq : (a⁻¹ * d₁ * a) * (a⁻¹ * d₂ * a) = d₁ * d₂ := by
      calc (a⁻¹ * d₁ * a) * (a⁻¹ * d₂ * a) = a⁻¹ * (d₁ * d₂) * a := by group
        _ = a⁻¹ * x * a := by rw [hx_eq]
        _ = x := hax
        _ = d₁ * d₂ := hx_eq.symm
    have hqp : (a⁻¹ * d₂ * a) * (a⁻¹ * d₁ * a) = d₁ * d₂ :=
      (hcen _ (hv d₂ hd₂) _ (hu d₁ hd₁)).trans hpq
    obtain ⟨_, h2⟩ :=
      step (a⁻¹ * d₁ * a) (a⁻¹ * d₂ * a) d₁ d₂ (hu d₁ hd₁) (hv d₂ hd₂) hd₁ hd₂ hqp
    refine ⟨⟨d₁, hd₁⟩, Subtype.ext ?_⟩
    rw [hψ ⟨d₁, hd₁⟩]
    show d₁ * (a⁻¹ * d₁ * a) = x
    rw [← h2]
    exact hx_eq
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩, fun d => hψ d⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
