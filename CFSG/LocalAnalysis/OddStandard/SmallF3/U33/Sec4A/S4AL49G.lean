module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem false_of_not_E_le_S (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {𝒮 E : Subgroup G} (hS𝒮 : S ≤ 𝒮) (hC : invCent t ⊓ 𝒮 = S)
    (hidx : S.relIndex (ctxS1 S 𝒮) = 2) (hE𝒮 : E ≤ 𝒮) (hEn : (E.subgroupOf 𝒮).Normal)
    (hEe : CFSG.Open.IsElemAbelian 2 E) (hEc : Nat.card E = 8)
    (hCE : 4 ≤ Nat.card ↥(E ⊓ invCent t)) (hES : ¬ E ≤ S) {α : G} (hα : α ∈ ctxS1 S 𝒮)
    (hswap : ∀ x : G, x ∈ ctxX t tau x₁ x₂ ↔ α * x * α⁻¹ ∈ ctxYt t tau x₁ x₂) : False := by
  set E₀ : Subgroup G := E ⊓ invCent t with hE0def
  have hE0_eq : E₀ = E ⊓ S := by
    rw [hE0def]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have hx' : x ∈ invCent t ⊓ 𝒮 := ⟨hx.2, hE𝒮 hx.1⟩
      rwa [hC] at hx'
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hx.1, h.toCtx0.le_invCent hx.2⟩
  have hE0_le : E₀ ≤ E := by rw [hE0_eq]; exact inf_le_left
  have hE0_le_S : E₀ ≤ S := by rw [hE0_eq]; exact inf_le_right
  have hCE' : 4 ≤ Nat.card E₀ := by rw [hE0def]; exact hCE
  have hES' : ∃ β : G, β ∈ E ∧ β ∉ S := by
    by_contra h
    apply hES
    intro x hx
    by_contra hxS
    exact h ⟨x, hx, hxS⟩
  obtain ⟨β, hβE, hβS⟩ := hES'
  have hE0_ne : E₀ ≠ E := by
    intro hEq
    have hβE0 : β ∈ E₀ := by rw [hEq]; exact hβE
    rw [hE0_eq] at hβE0
    exact hβS (Subgroup.mem_inf.mp hβE0).2
  have hE0_lt : E₀ < E := lt_of_le_of_ne hE0_le hE0_ne
  have hcard_lt8 : Nat.card E₀ < 8 := by
    have h := Subgroup.card_lt_of_lt hE0_lt
    rwa [hEc] at h
  have hcard_sub : Nat.card (E₀.subgroupOf E) = Nat.card E₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0_le).toEquiv
  have hdiv8 : Nat.card E₀ ∣ 8 := by
    rw [← hcard_sub]
    simpa [hEc] using Subgroup.card_subgroup_dvd_card (E₀.subgroupOf E)
  have hcardE0 : Nat.card E₀ = 4 := by
    have hdiv8' : Nat.card E₀ ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hdiv8
    obtain ⟨k, _hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv8'
    have h4le : 4 ≤ 2 ^ k := by rw [← hk]; exact hCE'
    have hlt8 : 2 ^ k < 8 := by rw [← hk]; exact hcard_lt8
    interval_cases k
    · norm_num at h4le
    · norm_num at h4le
    · norm_num at hk
      exact hk
    · norm_num at hlt8
  have hidx2 : (E₀.subgroupOf E).index = 2 := by
    have hmul := Subgroup.card_mul_index (E₀.subgroupOf E)
    rw [hcard_sub, hEc, hcardE0] at hmul
    omega
  have hmul_mem : ∀ {a b : E}, a ∉ E₀.subgroupOf E → b ∉ E₀.subgroupOf E →
      (a * b : E) ∈ E₀.subgroupOf E := fun ha hb =>
    (Subgroup.mul_mem_iff_of_index_two hidx2).mpr (iff_of_false ha hb)
  have hEn' : ∀ h k, h ∈ E → k ∈ 𝒮 → k * h * k⁻¹ ∈ E :=
    (Subgroup.normal_subgroupOf_iff hE𝒮).mp hEn
  have key : ∀ γ ∈ E, γ ∉ S → ∀ y ∈ S, γ * y * γ⁻¹ ∈ S := by
    intro γ hγE hγS y hyS
    have hγE0 : γ ∉ E₀ := fun h => hγS (hE0_le_S h)
    have hy𝒮 : y ∈ 𝒮 := hS𝒮 hyS
    have hγinvE : γ⁻¹ ∈ E := Subgroup.inv_mem E hγE
    have huE : y * γ⁻¹ * y⁻¹ ∈ E := hEn' γ⁻¹ y hγinvE hy𝒮
    have huE0 : y * γ⁻¹ * y⁻¹ ∉ E₀ := by
      intro hu
      have huS : y * γ⁻¹ * y⁻¹ ∈ S := hE0_le_S hu
      have hconj : y⁻¹ * (y * γ⁻¹ * y⁻¹) * y = γ⁻¹ := by group
      have hmemS : y⁻¹ * (y * γ⁻¹ * y⁻¹) * y ∈ S :=
        Subgroup.mul_mem S (Subgroup.mul_mem S (Subgroup.inv_mem S hyS) huS) hyS
      rw [hconj] at hmemS
      exact hγS (by simpa using Subgroup.inv_mem S hmemS)
    have hγ_not : (⟨γ, hγE⟩ : E) ∉ E₀.subgroupOf E :=
      fun hh => hγE0 (Subgroup.mem_subgroupOf.mp hh)
    have hu_not : (⟨y * γ⁻¹ * y⁻¹, huE⟩ : E) ∉ E₀.subgroupOf E :=
      fun hh => huE0 (Subgroup.mem_subgroupOf.mp hh)
    have hc_sub : (⟨γ, hγE⟩ : E) * (⟨y * γ⁻¹ * y⁻¹, huE⟩ : E) ∈ E₀.subgroupOf E :=
      hmul_mem hγ_not hu_not
    have hcE0 : γ * (y * γ⁻¹ * y⁻¹) ∈ E₀ := by
      simpa using Subgroup.mem_subgroupOf.mp hc_sub
    have hcS : γ * (y * γ⁻¹ * y⁻¹) ∈ S := hE0_le_S hcE0
    have heq : γ * y * γ⁻¹ = (γ * (y * γ⁻¹ * y⁻¹)) * y := by group
    rw [heq]
    exact Subgroup.mul_mem S hcS hyS
  have hnormβ : β ∈ normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact key β hβE hβS x hx
    · intro hx
      have hβinvS : β⁻¹ ∉ S := fun h => hβS (by simpa using Subgroup.inv_mem S h)
      have hmem := key β⁻¹ (Subgroup.inv_mem E hβE) hβinvS (β * x * β⁻¹) hx
      have heq : β⁻¹ * (β * x * β⁻¹) * β⁻¹⁻¹ = x := by group
      rwa [heq] at hmem
  have hβS1 : β ∈ ctxS1 S 𝒮 := by
    rw [ctxS1]
    exact Subgroup.mem_inf.mpr ⟨hnormβ, hE𝒮 hβE⟩
  have hαS : α ∉ S := by
    intro hαS
    have hXiff : ∀ x : G, x ∈ ctxX t tau x₁ x₂ ↔ α * x * α⁻¹ ∈ ctxX t tau x₁ x₂ := by
      intro x
      constructor
      · intro hx; exact (normalIn_ctxX h h43 h44).2 α hαS x hx
      · intro hx
        have hmem := (normalIn_ctxX h h43 h44).2 α⁻¹ (Subgroup.inv_mem S hαS) (α * x * α⁻¹) hx
        have heq : α⁻¹ * (α * x * α⁻¹) * α⁻¹⁻¹ = x := by group
        rwa [heq] at hmem
    have hXY : ctxX t tau x₁ x₂ = ctxYt t tau x₁ x₂ := by
      ext u
      have h1 : α⁻¹ * u * α ∈ ctxX t tau x₁ x₂ ↔ u ∈ ctxYt t tau x₁ x₂ := by
        have h := hswap (α⁻¹ * u * α)
        have heq : α * (α⁻¹ * u * α) * α⁻¹ = u := by group
        rwa [heq] at h
      have h2 : α⁻¹ * u * α ∈ ctxX t tau x₁ x₂ ↔ u ∈ ctxX t tau x₁ x₂ := by
        have h := hXiff (α⁻¹ * u * α)
        have heq : α * (α⁻¹ * u * α) * α⁻¹ = u := by group
        rwa [heq] at h
      rw [← h2, h1]
    exact (ctxX_ne_ctxYt h h44) hXY
  have hsS : α⁻¹ * β ∈ S := by
    have hmem := (Subgroup.mul_mem_iff_of_index_two (H := S.subgroupOf (ctxS1 S 𝒮)) hidx
      (a := (⟨α⁻¹, Subgroup.inv_mem _ hα⟩ : ctxS1 S 𝒮))
      (b := (⟨β, hβS1⟩ : ctxS1 S 𝒮)))
    have ha : (⟨α⁻¹, Subgroup.inv_mem _ hα⟩ : ctxS1 S 𝒮) ∉ S.subgroupOf (ctxS1 S 𝒮) :=
      fun hh => hαS (by
        have h' : α⁻¹ ∈ S := by simpa using Subgroup.mem_subgroupOf.mp hh
        simpa using Subgroup.inv_mem S h')
    have hb : (⟨β, hβS1⟩ : ctxS1 S 𝒮) ∉ S.subgroupOf (ctxS1 S 𝒮) :=
      fun hh => hβS (by simpa using Subgroup.mem_subgroupOf.mp hh)
    simpa using Subgroup.mem_subgroupOf.mp (hmem.mpr (iff_of_false ha hb))
  have hβswap : ∀ x ∈ ctxX t tau x₁ x₂, β * x * β⁻¹ ∈ ctxYt t tau x₁ x₂ := by
    intro x hx
    have hsx : (α⁻¹ * β) * x * (α⁻¹ * β)⁻¹ ∈ ctxX t tau x₁ x₂ :=
      (normalIn_ctxX h h43 h44).2 (α⁻¹ * β) hsS x hx
    have hmem := (hswap ((α⁻¹ * β) * x * (α⁻¹ * β)⁻¹)).mp hsx
    have heq : α * ((α⁻¹ * β) * x * (α⁻¹ * β)⁻¹) * α⁻¹ = β * x * β⁻¹ := by group
    rwa [heq] at hmem
  have hτβ : tau⁻¹ * β * tau ∈ E := by
    have hmem := hEn' β tau⁻¹ hβE (hS𝒮 (Subgroup.inv_mem S h.tau_mem))
    simpa using hmem
  exact false_of_swap_elem h h44 hEe hβE hτβ hβswap

end CFSG.OddStandard.SmallF3.HarrisU33.S4A