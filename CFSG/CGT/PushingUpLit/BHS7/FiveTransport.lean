module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6

variable {Γ : Type} [Group Γ]

theorem isNatBy_of_decomp {S M : Type*} [Group S] [Group M] {act : S → M → M}
    {G W V : Subgroup Γ} (hnat : IsNatBy act G W) (hWV : W ≤ V)
    (hGW : G ≤ Subgroup.normalizer (W : Set Γ)) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hdec : ∀ v ∈ V, ∃ w ∈ W, ∃ c ∈ V ⊓ Subgroup.centralizer (G : Set Γ), v = w * c)
    (hker : G ⊓ Subgroup.centralizer (V : Set Γ) = G ⊓ Subgroup.centralizer (W : Set Γ)) :
    IsNatBy act G V := by
  classical
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe⟩ := hnat
  have hψC : ∀ w : ↥W, (w : Γ) ∈ Subgroup.centralizer (G : Set Γ) → ψ w = 1 := by
    intro w hw
    have : w ∈ ψ.ker := by
      rw [hψk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨w.2, hw⟩
    exact this
  have hψC' : ∀ w : ↥W, ψ w = 1 → (w : Γ) ∈ Subgroup.centralizer (G : Set Γ) := by
    intro w hw
    have : w ∈ ψ.ker := hw
    rw [hψk, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at this
    exact this.2
  have hdec' : ∀ v : ↥V, ∃ w : ↥W, ∃ c : Γ, c ∈ Subgroup.centralizer (G : Set Γ) ∧
      (v : Γ) = (w : Γ) * c := by
    intro v
    obtain ⟨w, hw, c, hc, h⟩ := hdec v v.2
    exact ⟨⟨w, hw⟩, c, hc.2, h⟩
  have hwd : ∀ (w w' : ↥W) (c c' : Γ), c ∈ Subgroup.centralizer (G : Set Γ) →
      c' ∈ Subgroup.centralizer (G : Set Γ) → (w : Γ) * c = (w' : Γ) * c' → ψ w = ψ w' := by
    intro w w' c c' hc hc' h
    have h1 : (w' : Γ)⁻¹ * w = c' * c⁻¹ := by
      calc (w' : Γ)⁻¹ * w = (w' : Γ)⁻¹ * (w * c) * c⁻¹ := by group
        _ = (w' : Γ)⁻¹ * (w' * c') * c⁻¹ := by rw [h]
        _ = c' * c⁻¹ := by group
    have hcen : ((w'⁻¹ * w : ↥W) : Γ) ∈ Subgroup.centralizer (G : Set Γ) := by
      have : ((w'⁻¹ * w : ↥W) : Γ) = c' * c⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact h1
      rw [this]
      exact (Subgroup.centralizer (G : Set Γ)).mul_mem hc' ((Subgroup.centralizer _).inv_mem hc)
    have := hψC _ hcen
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  let f : ↥V → M := fun v => ψ (Classical.choose (hdec' v))
  have hf : ∀ (v : ↥V) (w : ↥W) (c : Γ), c ∈ Subgroup.centralizer (G : Set Γ) →
      (v : Γ) = (w : Γ) * c → f v = ψ w := by
    intro v w c hc h
    obtain ⟨c₀, hc₀, h₀⟩ := Classical.choose_spec (hdec' v)
    exact hwd _ w _ c hc₀ hc (h₀.symm.trans h)
  have hf1 : f 1 = 1 := by
    have := hf 1 1 1 (Subgroup.one_mem _) (by simp)
    rw [this, map_one]
  have hfmul : ∀ x y : ↥V, f (x * y) = f x * f y := by
    intro x y
    obtain ⟨w₁, c₁, hc₁, h₁⟩ := hdec' x
    obtain ⟨w₂, c₂, hc₂, h₂⟩ := hdec' y
    have hc₁V : c₁ ∈ V := by
      have : c₁ = (w₁ : Γ)⁻¹ * x := by rw [h₁]; group
      rw [this]
      exact V.mul_mem (V.inv_mem (hWV w₁.2)) x.2
    have hcomm : c₁ * (w₂ : Γ) = (w₂ : Γ) * c₁ := hVab _ hc₁V _ (hWV w₂.2)
    have hxy : ((x * y : ↥V) : Γ) = ((w₁ * w₂ : ↥W) : Γ) * (c₁ * c₂) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h₁, h₂]
      calc (w₁ : Γ) * c₁ * ((w₂ : Γ) * c₂) = (w₁ : Γ) * (c₁ * (w₂ : Γ)) * c₂ := by group
        _ = (w₁ : Γ) * ((w₂ : Γ) * c₁) * c₂ := by rw [hcomm]
        _ = (w₁ : Γ) * (w₂ : Γ) * (c₁ * c₂) := by group
    rw [hf (x * y) (w₁ * w₂) (c₁ * c₂)
      ((Subgroup.centralizer (G : Set Γ)).mul_mem hc₁ hc₂) hxy, map_mul, hf x w₁ c₁ hc₁ h₁,
      hf y w₂ c₂ hc₂ h₂]
  let ψV : ↥V →* M := { toFun := f, map_one' := hf1, map_mul' := hfmul }
  refine ⟨φ, ψV, hφs, ?_, ?_, ?_, ?_⟩
  · rw [hφk, hker]
  · intro m
    obtain ⟨w, hw⟩ := hψs m
    refine ⟨⟨(w : Γ), hWV w.2⟩, ?_⟩
    show f ⟨(w : Γ), hWV w.2⟩ = m
    rw [hf ⟨(w : Γ), hWV w.2⟩ w 1 (Subgroup.one_mem _) (by simp), hw]
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    obtain ⟨w, c, hc, h⟩ := hdec' v
    show f v = 1 ↔ _
    rw [hf v w c hc h]
    constructor
    · intro hw
      refine ⟨v.2, ?_⟩
      rw [h]
      exact (Subgroup.centralizer (G : Set Γ)).mul_mem (hψC' w hw) hc
    · rintro ⟨-, hv⟩
      apply hψC
      have : (w : Γ) = (v : Γ) * c⁻¹ := by rw [h]; group
      rw [this]
      exact (Subgroup.centralizer (G : Set Γ)).mul_mem hv ((Subgroup.centralizer _).inv_mem hc)
  · intro e v hv
    obtain ⟨w, c, hc, h⟩ := hdec' v
    have hew : (e : Γ) * w * (e : Γ)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hGW e.2) w).mp w.2
    have hec : (e : Γ) * c * (e : Γ)⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.mp hc (e : Γ) e.2
      rw [this]
      group
    have hv' : ((⟨(e : Γ) * v * (e : Γ)⁻¹, hv⟩ : ↥V) : Γ) =
        (((⟨(e : Γ) * w * (e : Γ)⁻¹, hew⟩ : ↥W)) : Γ) * c := by
      show (e : Γ) * v * (e : Γ)⁻¹ = (e : Γ) * w * (e : Γ)⁻¹ * c
      rw [h]
      calc (e : Γ) * ((w : Γ) * c) * (e : Γ)⁻¹
          = (e : Γ) * w * (e : Γ)⁻¹ * ((e : Γ) * c * (e : Γ)⁻¹) := by group
        _ = (e : Γ) * w * (e : Γ)⁻¹ * c := by rw [hec]
    show f ⟨(e : Γ) * v * (e : Γ)⁻¹, hv⟩ = act (φ e) (f v)
    rw [hf _ ⟨(e : Γ) * w * (e : Γ)⁻¹, hew⟩ c hc hv', hf v w c hc h]
    exact hψe e w hew

end CFSG.CGT.PushingUpLit.BHS7
