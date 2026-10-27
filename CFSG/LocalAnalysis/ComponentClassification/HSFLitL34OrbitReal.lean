module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34OrbitModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Real2

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.UnbalancedLayer Subgroup

theorem false_of_five_center_T0 {P : Equiv.Perm (Fin 42) → Prop}
    (hcard : Nat.card {t // P t} = 4)
    {w₀ w₁ w₂ w₃ w₄ : Equiv.Perm (Fin 42)} (h₀ : P w₀) (h₁ : P w₁) (h₂ : P w₂) (h₃ : P w₃)
    (h₄ : P w₄) (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h03 : w₀ ≠ w₃) (h04 : w₀ ≠ w₄)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h14 : w₁ ≠ w₄) (h23 : w₂ ≠ w₃) (h24 : w₂ ≠ w₄)
    (h34 : w₃ ≠ w₄) : False := by
  let f : Fin 5 → {t // P t} := ![⟨w₀, h₀⟩, ⟨w₁, h₁⟩, ⟨w₂, h₂⟩, ⟨w₃, h₃⟩, ⟨w₄, h₄⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢ <;> simp_all
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin, hcard] at this
  omega

namespace Real

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} (ρ : Real K)

include ρ in
theorem exists_conj_mul_center
    {Sg : Subgroup G}
    (hS : IsSylowTwoIn Sg (normalizer (K : Set G))) {e a : G} (he : e ∈ Sg) (he2 : e * e = 1)
    (hec : ∀ g ∈ Sg, ∀ h ∈ Sg, g⁻¹ * e * g * (h⁻¹ * e * h) = h⁻¹ * e * h * (g⁻¹ * e * g))
    (ha : a ∈ Sg ⊓ K ⊓ centralizer ((Sg ⊓ K : Subgroup G) : Set G)) {g₂ g₃ g₄ : G}
    (hg₂ : g₂ ∈ Sg) (hg₃ : g₃ ∈ Sg) (hg₄ : g₄ ∈ Sg)
    (h₁ : e ∉ coreActionKernel K) (h₂ : g₂⁻¹ * e * g₂ ∉ coreActionKernel K)
    (h₃ : g₃⁻¹ * e * g₃ ∉ coreActionKernel K) (h₄ : g₄⁻¹ * e * g₄ ∉ coreActionKernel K)
    (h12 : e⁻¹ * (g₂⁻¹ * e * g₂) ∉ coreActionKernel K)
    (h13 : e⁻¹ * (g₃⁻¹ * e * g₃) ∉ coreActionKernel K)
    (h14 : e⁻¹ * (g₄⁻¹ * e * g₄) ∉ coreActionKernel K)
    (h23 : (g₂⁻¹ * e * g₂)⁻¹ * (g₃⁻¹ * e * g₃) ∉ coreActionKernel K)
    (h24 : (g₂⁻¹ * e * g₂)⁻¹ * (g₄⁻¹ * e * g₄) ∉ coreActionKernel K)
    (h34 : (g₃⁻¹ * e * g₃)⁻¹ * (g₄⁻¹ * e * g₄) ∉ coreActionKernel K) {g : G} (hg : g ∈ Sg) :
    ∃ g' ∈ Sg, (g'⁻¹ * (g⁻¹ * e * g) * g')⁻¹ * (g⁻¹ * e * g * a) ∈ coreActionKernel K := by
  have hSN := hS.1
  have hS2 := GrS4.isPGroup_of_isSylowTwoIn hS
  obtain ⟨heq, h64⟩ := ρ.img_inf_K_eq hS
  obtain ⟨c, -, hc, hiff, hsurj⟩ := exists_std (ρ.img_le_R Sg) (ρ.img_isPGroup hS2) h64
  set ψ : ↥(normalizer (K : Set G)) →* Equiv.Perm (Fin 42) :=
    (MulAut.conj c).toMonoidHom.comp ρ.φ with hψ
  have hψa : ∀ x, ψ x = c * ρ.φ x * c⁻¹ := fun x => rfl
  have hker : ∀ x y : ↥(normalizer (K : Set G)), ψ x = ψ y → (x : G)⁻¹ * y ∈ coreActionKernel K :=
    by
    intro x y hxy
    have h1 : ρ.φ x = ρ.φ y := by
      rw [hψa, hψa] at hxy
      simpa using hxy
    have h2 : ρ.φ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (ρ.ker_iff _).1 h2
  have hTR : ∀ x : ↥(normalizer (K : Set G)), (x : G) ∈ Sg → ψ x ∈ TR := fun x hx =>
    hc _ (ρ.phi_mem_img hx)
  have hlift : ∀ τ ∈ T0, ∃ g : ↥(normalizer (K : Set G)), (g : G) ∈ Sg ⊓ K ∧ ψ g = τ := by
    intro τ hτ
    obtain ⟨x, hx, rfl⟩ := hsurj τ hτ
    rw [← heq] at hx
    obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
    exact ⟨g, hg, rfl⟩
  set e' : ↥(normalizer (K : Set G)) := ⟨e, hSN he⟩
  set a' : ↥(normalizer (K : Set G)) := ⟨a, hSN (mem_inf.1 (mem_inf.1 ha).1).1⟩
  have hcj : ∀ g : G, (hg : g ∈ Sg) →
      ψ ⟨g⁻¹ * e * g, hSN (mul_mem (mul_mem (inv_mem hg) he) hg)⟩ =
        (ψ ⟨g, hSN hg⟩)⁻¹ * ψ e' * ψ ⟨g, hSN hg⟩ := by
    intro g hg
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hyTR : ψ e' ∈ TR := hTR e' he
  have hy2 : ψ e' * ψ e' = 1 := by
    rw [← map_mul]
    have : e' * e' = 1 := Subtype.ext he2
    rw [this, map_one]
  have ha' : ρ.φ a' ∈ ρ.img Sg ⊓ S := heq ▸ ρ.phi_mem_img (mem_inf.1 ha).1
  have hzT : ψ a' ∈ T0 := (hiff _ (mem_inf.1 ha').1).1 (mem_inf.1 ha').2
  have hzc : ∀ t ∈ T0, ψ a' * t = t * ψ a' := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := hlift t ht
    have h1 : (g : G) * a = a * g := mem_centralizer_iff.1 (mem_inf.1 ha).2 g hg
    have h2 : ψ (a' * g) = ψ (g * a') := congrArg ψ (Subtype.ext h1.symm)
    simpa only [map_mul] using h2
  by_cases hyZ : ψ e' ∈ T0 ∧ ∀ t ∈ T0, ψ e' * t = t * ψ e'
  ·
    exfalso
    have hZ : ∀ g : G, (hg : g ∈ Sg) →
        ψ ⟨g⁻¹ * e * g, hSN (mul_mem (mul_mem (inv_mem hg) he) hg)⟩ ∈ T0 ∧
          ∀ t ∈ T0, ψ ⟨g⁻¹ * e * g, hSN (mul_mem (mul_mem (inv_mem hg) he) hg)⟩ * t =
            t * ψ ⟨g⁻¹ * e * g, hSN (mul_mem (mul_mem (inv_mem hg) he) hg)⟩ := by
      intro g hg
      rw [hcj g hg]
      have h1 := conj_mem_center_T0 (inv_mem (hTR ⟨g, hSN hg⟩ hg)) hyZ.1 hyZ.2
      rwa [inv_inv] at h1
    have hne1 : ∀ x : ↥(normalizer (K : Set G)), (x : G) ∉ coreActionKernel K → ψ x ≠ 1 :=
      fun x hx h => hx (by simpa using hker 1 x (by rw [map_one, h]))
    have hne : ∀ x y : ↥(normalizer (K : Set G)), (x : G)⁻¹ * y ∉ coreActionKernel K →
        ψ x ≠ ψ y := fun x y hxy h => hxy (hker x y h)
    exact false_of_five_center_T0 (P := fun t => t ∈ T0 ∧ ∀ s ∈ T0, t * s = s * t)
      card_center_T0
      ⟨one_mem _, fun s _ => by rw [one_mul, mul_one]⟩ hyZ (hZ g₂ hg₂) (hZ g₃ hg₃) (hZ g₄ hg₄)
      (hne1 _ h₁).symm (hne1 _ h₂).symm (hne1 _ h₃).symm (hne1 _ h₄).symm (hne _ _ h12)
      (hne _ _ h13) (hne _ _ h14) (hne _ _ h23) (hne _ _ h24) (hne _ _ h34)
  ·
    have hfS : g⁻¹ * e * g ∈ Sg := mul_mem (mul_mem (inv_mem hg) he) hg
    set f' : ↥(normalizer (K : Set G)) := ⟨g⁻¹ * e * g, hSN hfS⟩
    set σ : Equiv.Perm (Fin 42) := ψ ⟨g, hSN hg⟩
    have hσ : σ ∈ TR := hTR _ hg
    have hf' : ψ f' = σ⁻¹ * ψ e' * σ := hcj g hg
    have hyTR' : ψ f' ∈ TR := hTR f' hfS
    have hy2' : ψ f' * ψ f' = 1 := by
      rw [hf', show σ⁻¹ * ψ e' * σ * (σ⁻¹ * ψ e' * σ) = σ⁻¹ * (ψ e' * ψ e') * σ by group, hy2]
      group
    have hyZ' : ¬ (ψ f' ∈ T0 ∧ ∀ t ∈ T0, ψ f' * t = t * ψ f') := by
      intro h
      apply hyZ
      have h1 := conj_mem_center_T0 hσ h.1 h.2
      rwa [hf', show σ * (σ⁻¹ * ψ e' * σ) * σ⁻¹ = ψ e' by group] at h1
    have hyc' : ∀ τ ∈ T0, ψ f' * (τ * ψ f' * τ⁻¹) = τ * ψ f' * τ⁻¹ * ψ f' := by
      intro τ hτ
      obtain ⟨h, hh, rfl⟩ := hlift τ hτ
      have hhS : (h : G) ∈ Sg := (mem_inf.1 hh).1
      have h1 := hec g hg (g * (h : G)⁻¹) (mul_mem hg (inv_mem hhS))
      have h2 : ψ (f' * (h * f' * h⁻¹)) = ψ (h * f' * h⁻¹ * f') := congrArg ψ (Subtype.ext (by
        simp only [f', Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [show (h : G) * (g⁻¹ * e * g) * (h : G)⁻¹ =
          (g * (h : G)⁻¹)⁻¹ * e * (g * (h : G)⁻¹) by group]
        exact h1))
      simpa only [map_mul, map_inv] using h2
    obtain ⟨τ, hτ, hτy⟩ := exists_conj_eq_mul_center_T0 hyTR' hy2' hyZ' hyc' hzT hzc
    obtain ⟨g', hg', hgτ⟩ := hlift τ⁻¹ (inv_mem hτ)
    have hgS : (g' : G) ∈ Sg := (mem_inf.1 hg').1
    refine ⟨g', hgS, ?_⟩
    have h1 : ψ (g'⁻¹ * f' * g') = ψ (f' * a') := by
      rw [map_mul, map_mul, map_inv, map_mul, hgτ, inv_inv, hτy]
    exact hker _ _ h1

end Real

end CFSG.ComponentClassification.HSFLit.AutL34
