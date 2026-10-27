module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

theorem exists_block_hom {Ω ι : Type*} {n : ℕ} (gens : Fin n → Equiv.Perm Ω)
    (G : Subgroup (Equiv.Perm Ω)) (hG : Subgroup.closure (Set.range gens) = G)
    (β : Ω → Option ι) (hsurj : ∀ i : ι, ∃ p, β p = some i)
    (τ : Fin n → Equiv.Perm ι) (hτ : ∀ k p, β (gens k p) = (β p).map (τ k)) :
    ∃ ρ : ↥G →* Equiv.Perm ι,
      (∀ (g : ↥G) (p : Ω), β ((g : Equiv.Perm Ω) p) = (β p).map (ρ g)) ∧
      (∀ (k : Fin n) (h : gens k ∈ G), ρ ⟨gens k, h⟩ = τ k) ∧
      ρ.range = Subgroup.closure (Set.range τ) := by
  classical
  have huniq : ∀ σ σ' : Equiv.Perm ι, (∀ p, (β p).map σ = (β p).map σ') → σ = σ' := by
    intro σ σ' h
    ext i
    obtain ⟨p, hp⟩ := hsurj i
    have h' := h p
    rw [hp] at h'
    exact Option.some.inj h'
  let S : Subgroup (Equiv.Perm Ω) :=
    { carrier := {g | ∃ σ : Equiv.Perm ι, ∀ p, β (g p) = (β p).map σ}
      one_mem' := ⟨1, by intro p; simp⟩
      mul_mem' := by
        rintro a b ⟨σa, ha⟩ ⟨σb, hb⟩
        refine ⟨σa * σb, ?_⟩
        intro p
        rw [Equiv.Perm.mul_apply, ha, hb, Option.map_map]
        rfl
      inv_mem' := by
        rintro a ⟨σ, hσ⟩
        refine ⟨σ⁻¹, ?_⟩
        intro p
        rw [Equiv.Perm.inv_def]
        have h := hσ (a.symm p)
        rw [Equiv.apply_symm_apply] at h
        rw [h, Option.map_map]
        simp }
  have hGS : G ≤ S := by
    rw [← hG, Subgroup.closure_le]
    rintro g ⟨k, rfl⟩
    exact ⟨τ k, hτ k⟩
  let f : ↥G → Equiv.Perm ι :=
    fun g => Classical.choose
      (show ∃ σ : Equiv.Perm ι, ∀ p, β ((g : Equiv.Perm Ω) p) = (β p).map σ from hGS g.2)
  have hf_spec : ∀ (g : ↥G) (p : Ω),
      β ((g : Equiv.Perm Ω) p) = (β p).map (f g) :=
    fun g => Classical.choose_spec
      (show ∃ σ : Equiv.Perm ι, ∀ p, β ((g : Equiv.Perm Ω) p) = (β p).map σ from hGS g.2)
  have hf_one : f 1 = 1 := by
    apply huniq
    intro p
    have h := (hf_spec (1 : ↥G) p).symm
    rw [h]
    simp
  have hf_mul : ∀ a b : ↥G, f (a * b) = f a * f b := by
    intro a b
    apply huniq
    intro p
    have h1 := (hf_spec (a * b) p).symm
    have h2 := hf_spec a ((b : Equiv.Perm Ω) p)
    have h3 := hf_spec b p
    rw [h1, Subgroup.coe_mul, Equiv.Perm.mul_apply, h2, h3, Option.map_map]
    rfl
  let ρ : ↥G →* Equiv.Perm ι :=
    { toFun := f
      map_one' := hf_one
      map_mul' := hf_mul }
  have hρ : ∀ g : ↥G, ρ g = f g := fun g => rfl
  have hρgen : ∀ (k : Fin n) (h : gens k ∈ G), ρ ⟨gens k, h⟩ = τ k := by
    intro k h
    apply huniq
    intro p
    have h1 := (hf_spec (⟨gens k, h⟩ : ↥G) p).symm
    rw [hρ, h1, hτ k p]
  refine ⟨ρ, ?_, hρgen, ?_⟩
  · intro g p
    rw [hρ]
    exact hf_spec g p
  · apply le_antisymm
    ·
      have key : ∀ (g : Equiv.Perm Ω) (hg : g ∈ Subgroup.closure (Set.range gens)),
          ρ ⟨g, hG ▸ hg⟩ ∈ Subgroup.closure (Set.range τ) := by
        intro g hg
        refine Subgroup.closure_induction
          (p := fun g hg => ρ ⟨g, hG ▸ hg⟩ ∈ Subgroup.closure (Set.range τ))
          ?_ ?_ ?_ ?_ hg
        · intro x hx
          obtain ⟨k, rfl⟩ := hx
          rw [hρgen k (hG ▸ Subgroup.subset_closure (Set.mem_range_self k))]
          exact Subgroup.subset_closure ⟨k, rfl⟩
        · rw [show (⟨(1 : Equiv.Perm Ω),
                hG ▸ Subgroup.one_mem (Subgroup.closure (Set.range gens))⟩ : ↥G) = 1
              from Subtype.ext rfl, hρ]
          rw [hf_one]
          exact Subgroup.one_mem (Subgroup.closure (Set.range τ))
        · intro x y hx hy ihx ihy
          have hxy : (⟨x * y,
                hG ▸ Subgroup.mul_mem (Subgroup.closure (Set.range gens)) hx hy⟩ : ↥G) =
              ⟨x, hG ▸ hx⟩ * ⟨y, hG ▸ hy⟩ := Subtype.ext rfl
          rw [hxy, map_mul]
          exact Subgroup.mul_mem (Subgroup.closure (Set.range τ)) ihx ihy
        · intro x hx ihx
          have hxy : (⟨x⁻¹,
                hG ▸ Subgroup.inv_mem (Subgroup.closure (Set.range gens)) hx⟩ : ↥G) =
              (⟨x, hG ▸ hx⟩ : ↥G)⁻¹ := Subtype.ext rfl
          rw [hxy, map_inv]
          exact Subgroup.inv_mem (Subgroup.closure (Set.range τ)) ihx
      rintro x ⟨g, rfl⟩
      have hg' : (g : Equiv.Perm Ω) ∈ Subgroup.closure (Set.range gens) := by
        simpa only [← hG] using g.2
      exact key (g : Equiv.Perm Ω) hg'
    ·
      rw [Subgroup.closure_le]
      rintro x ⟨k, rfl⟩
      exact ⟨⟨gens k, hG ▸ Subgroup.subset_closure (Set.mem_range_self k)⟩, hρgen k _⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
