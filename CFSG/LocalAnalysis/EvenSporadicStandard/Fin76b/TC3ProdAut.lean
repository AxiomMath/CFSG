module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ProdAut
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.EvenSporadicStandard.M24Std

structure OrdFacts (A : Type*) [Group A] : Prop where
  simple : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤
  central : ∀ a : A, (∀ c, a * c = c * a) → a = 1
  nontrivial : ∃ s : A, s ≠ 1
  pow_eight : ∀ f : MulAut A, f ^ 16 = 1 → f ^ 8 = 1
  eq_pow : ∀ u : MulAut A, u ^ 8 = 1 → u ^ 4 ≠ 1 → ∀ v : MulAut A, v * u = u * v →
    ∃ k < 8, v = u ^ k

namespace OrdFacts

variable {A : Type*} [Group A]

theorem prod_cases (h : OrdFacts A) (α : MulAut (A × A)) :
    (∃ f₁ f₂ : MulAut A, ∀ a b, α (a, b) = (f₁ a, f₂ b)) ∨
      ∃ f₁ f₂ : MulAut A, ∀ a b, α (a, b) = (f₁ b, f₂ a) := by
  rcases ProdAut.mulAut_prod_cases h.simple h.central h.nontrivial α with
    ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩
  · exact Or.inl (ProdAut.exists_prod_preserve α hp1 hp2)
  · exact Or.inr (ProdAut.exists_prod_swap α hs1 hs2)

end OrdFacts

variable {A : Type*} [Group A]

theorem pow_apply_pres {α : MulAut (A × A)} {f₁ f₂ : MulAut A}
    (hf : ∀ a b, α (a, b) = (f₁ a, f₂ b)) (n : ℕ) (a b : A) :
    (α ^ n) (a, b) = ((f₁ ^ n) a, (f₂ ^ n) b) := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, hf]

theorem sq_apply_swap {α : MulAut (A × A)} {f₁ f₂ : MulAut A}
    (hf : ∀ a b, α (a, b) = (f₁ b, f₂ a)) (a b : A) :
    (α ^ 2) (a, b) = ((f₁ * f₂) a, (f₂ * f₁) b) := by
  simp [pow_two, hf]

theorem pow_two_mul_apply_swap {α : MulAut (A × A)} {f₁ f₂ : MulAut A}
    (hf : ∀ a b, α (a, b) = (f₁ b, f₂ a)) (n : ℕ) (a b : A) :
    (α ^ (2 * n)) (a, b) = (((f₁ * f₂) ^ n) a, ((f₂ * f₁) ^ n) b) := by
  rw [pow_mul]
  exact pow_apply_pres (fun a b => sq_apply_swap hf a b) n a b

theorem mulAut_prod_eq_one {β : MulAut (A × A)} (h : ∀ a b, β (a, b) = (a, b)) : β = 1 :=
  MulEquiv.ext fun p => by
    obtain ⟨a, b⟩ := p
    simpa using h a b

theorem OrdFacts.comm_of_orderOf_sixteen (h : OrdFacts A) {α : MulAut (A × A)}
    (hα : orderOf α = 16) {x y : MulAut (A × A)} (hx : x * α = α * x) (hy : y * α = α * y) :
    x * y = y * x := by
  have hα16 : α ^ 16 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have hα8 : α ^ 8 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hα]; norm_num)
  rcases h.prod_cases α with ⟨f₁, f₂, hf⟩ | ⟨f₁, f₂, hf⟩
  · exfalso
    apply hα8
    have h1 : f₁ ^ 16 = 1 := MulEquiv.ext fun a => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (a, 1)).1) hα16
      simpa [pow_apply_pres hf] using this
    have h2 : f₂ ^ 16 = 1 := MulEquiv.ext fun b => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (1, b)).2) hα16
      simpa [pow_apply_pres hf] using this
    have h1' := h.pow_eight f₁ h1
    have h2' := h.pow_eight f₂ h2
    exact mulAut_prod_eq_one fun a b => by simp [pow_apply_pres hf, h1', h2']
  · set u : MulAut A := f₁ * f₂ with hu
    set v : MulAut A := f₂ * f₁ with hv
    have hu8 : u ^ 8 = 1 := MulEquiv.ext fun a => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (a, 1)).1) hα16
      have e : (α ^ 16) (a, 1) = ((u ^ 8) a, (v ^ 8) 1) := pow_two_mul_apply_swap hf 8 a 1
      simpa [e] using this
    have hvu : v = f₂ * u * f₂⁻¹ := by simp [hu, hv, mul_assoc]
    have hu4 : u ^ 4 ≠ 1 := by
      intro h4
      apply hα8
      have hv4 : v ^ 4 = 1 := by rw [hvu, conj_pow, h4]; simp
      refine mulAut_prod_eq_one fun a b => ?_
      have e : (α ^ 8) (a, b) = ((u ^ 4) a, (v ^ 4) b) := pow_two_mul_apply_swap hf 4 a b
      simp [e, h4, hv4]
    have hcyc := h.eq_pow u hu8 hu4
    have hinv : ∀ a b, α⁻¹ (a, b) = (f₂⁻¹ b, f₁⁻¹ a) := fun a b => by
      apply α.injective
      rw [MulAut.apply_inv_self, hf]
      simp
    have key : ∀ z : MulAut (A × A), z * α = α * z → ∀ g₁ g₂ : MulAut A,
        (∀ a b, z (a, b) = (g₁ a, g₂ b)) → g₁ * u = u * g₁ ∧ g₂ = f₁⁻¹ * g₁ * f₁ := by
      intro z hz g₁ g₂ hg
      have e1 : ∀ b, g₁ (f₁ b) = f₁ (g₂ b) := fun b => by
        have := congrArg (fun γ : MulAut (A × A) => (γ (1, b)).1) hz
        simpa [hf, hg] using this
      have e2 : ∀ a, g₂ (f₂ a) = f₂ (g₁ a) := fun a => by
        have := congrArg (fun γ : MulAut (A × A) => (γ (a, 1)).2) hz
        simpa [hf, hg] using this
      have h1 : g₁ * f₁ = f₁ * g₂ := MulEquiv.ext e1
      have h2 : g₂ * f₂ = f₂ * g₁ := MulEquiv.ext e2
      refine ⟨?_, ?_⟩
      · calc g₁ * u = g₁ * f₁ * f₂ := by rw [hu, mul_assoc]
          _ = f₁ * (g₂ * f₂) := by rw [h1, mul_assoc]
          _ = f₁ * (f₂ * g₁) := by rw [h2]
          _ = u * g₁ := by rw [hu, mul_assoc]
      · calc g₂ = f₁⁻¹ * (f₁ * g₂) := by group
          _ = f₁⁻¹ * (g₁ * f₁) := by rw [h1]
          _ = f₁⁻¹ * g₁ * f₁ := by group
    have pp : ∀ z z' : MulAut (A × A), z * α = α * z → z' * α = α * z' →
        ∀ g₁ g₂ g₁' g₂' : MulAut A, (∀ a b, z (a, b) = (g₁ a, g₂ b)) →
          (∀ a b, z' (a, b) = (g₁' a, g₂' b)) → z * z' = z' * z := by
      intro z z' hz hz' g₁ g₂ g₁' g₂' hg hg'
      obtain ⟨hc, hg₂⟩ := key z hz g₁ g₂ hg
      obtain ⟨hc', hg₂'⟩ := key z' hz' g₁' g₂' hg'
      obtain ⟨k, -, hk⟩ := hcyc g₁ hc
      obtain ⟨k', -, hk'⟩ := hcyc g₁' hc'
      have hcomm : g₁ * g₁' = g₁' * g₁ := by
        rw [hk, hk']
        exact (Commute.pow_pow_self u k k').eq
      have hcomm2 : g₂ * g₂' = g₂' * g₂ := by
        calc g₂ * g₂' = f₁⁻¹ * (g₁ * g₁') * f₁ := by rw [hg₂, hg₂']; group
          _ = f₁⁻¹ * (g₁' * g₁) * f₁ := by rw [hcomm]
          _ = g₂' * g₂ := by rw [hg₂, hg₂']; group
      refine MulEquiv.ext fun p => ?_
      obtain ⟨a, b⟩ := p
      have e1 : g₁ (g₁' a) = g₁' (g₁ a) := congrArg (fun γ : MulAut A => γ a) hcomm
      have e2 : g₂ (g₂' b) = g₂' (g₂ b) := congrArg (fun γ : MulAut A => γ b) hcomm2
      simp [MulAut.mul_apply, hg, hg', e1, e2]
    have decomp : ∀ z : MulAut (A × A), z * α = α * z → ∃ p : MulAut (A × A), p * α = α * p ∧
        (∃ g₁ g₂ : MulAut A, ∀ a b, p (a, b) = (g₁ a, g₂ b)) ∧ (z = p ∨ z = p * α) := by
      intro z hz
      rcases h.prod_cases z with ⟨g₁, g₂, hg⟩ | ⟨g₁, g₂, hg⟩
      · exact ⟨z, hz, ⟨g₁, g₂, hg⟩, Or.inl rfl⟩
      · refine ⟨z * α⁻¹, ?_, ⟨g₁ * f₁⁻¹, g₂ * f₂⁻¹, fun a b => ?_⟩, Or.inr (by group)⟩
        · calc z * α⁻¹ * α = z := by group
            _ = α * (z * α⁻¹) := by rw [← mul_assoc, ← hz]; group
        · simp [MulAut.mul_apply, hinv, hg]
    obtain ⟨p, hpα, ⟨g₁, g₂, hg⟩, hxp⟩ := decomp x hx
    obtain ⟨q, hqα, ⟨g₁', g₂', hg'⟩, hyq⟩ := decomp y hy
    have cpq : Commute p q := pp p q hpα hqα g₁ g₂ g₁' g₂' hg hg'
    have cpa : Commute p α := hpα
    have cqa : Commute q α := hqα
    have hxy : Commute x y := by
      rcases hxp with hxp | hxp <;> rcases hyq with hyq | hyq <;> rw [hxp, hyq]
      · exact cpq
      · exact cpq.mul_right cpa
      · exact cpq.mul_left cqa.symm
      · exact (cpq.mul_right cpa).mul_left (cqa.symm.mul_right (Commute.refl α))
    exact hxy

end CFSG.EvenSporadicStandard.Fin76b
