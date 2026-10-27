module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockFixOfNormalW
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightOfData

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

@[expose] noncomputable def embL (r s : ℕ) : Perm (Fin r × Bool) →* Perm (OmegaE r s) :=
  (Perm.sumCongrHom (Fin r × Bool) (Fin s)).comp (MonoidHom.inl _ _)

theorem embL_apply_inl (r s : ℕ) (x : Perm (Fin r × Bool)) (p : Fin r × Bool) :
    embL r s x (Sum.inl p) = Sum.inl (x p) := rfl

theorem embL_apply_inr (r s : ℕ) (x : Perm (Fin r × Bool)) (j : Fin s) :
    embL r s x (Sum.inr j) = Sum.inr j := rfl

theorem embL_injective (r s : ℕ) : Function.Injective (embL r s) := by
  intro x y h
  refine Equiv.ext fun p => ?_
  have := congrArg (fun f => f (Sum.inl p)) h
  simpa [embL_apply_inl] using this

@[expose] noncomputable def Wr (r s : ℕ) : Subgroup (Perm (OmegaE r s)) :=
  (blockFix (Fin r)).map (embL r s)

theorem Wr_apply_inr {r s : ℕ} {w : Perm (OmegaE r s)} (hw : w ∈ Wr r s) (j : Fin s) :
    w (Sum.inr j) = Sum.inr j := by
  obtain ⟨x, -, rfl⟩ := hw
  rfl

theorem exists_Wr_moves {r s : ℕ} (p : Fin r × Bool) :
    ∃ w ∈ Wr r s, w (Sum.inl p) ≠ Sum.inl p := by
  refine ⟨embL r s (swap (p.1, false) (p.1, true)), ⟨swap (p.1, false) (p.1, true), swap_mem_blockFix (u := (p.1, false)) (v := (p.1, true)) rfl, rfl⟩, ?_⟩
  rw [embL_apply_inl]
  intro h
  have h' := Sum.inl_injective h
  obtain ⟨i, b⟩ := p
  cases b
  · rw [swap_apply_left] at h'; simp at h'
  · rw [swap_apply_right] at h'; simp at h'

theorem normalizer_Wr_inr {r s : ℕ} {h : Perm (OmegaE r s)}
    (hh : h ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s)))) (j : Fin s) :
    ∃ j', h (Sum.inr j) = Sum.inr j' := by
  have hinv : h⁻¹ ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := inv_mem hh
  set a := h (Sum.inr j) with ha
  have hfix : ∀ w ∈ Wr r s, w a = a := by
    intro w hw
    have hc : h⁻¹ * w * h ∈ Wr r s := ((Subgroup.mem_normalizer_iff.1 hinv) w).1 hw
    have := Wr_apply_inr hc j
    have h2 : (h⁻¹ * w * h) (Sum.inr j) = Sum.inr j := this
    simp only [Perm.mul_apply] at h2
    have h3 := congrArg h h2
    simpa [ha] using h3
  rcases hA : a with p | j'
  · exfalso
    obtain ⟨w, hw, hmove⟩ := exists_Wr_moves (s := s) p
    exact hmove (by have := hfix w hw; rw [hA] at this; exact this)
  · exact ⟨j', rfl⟩

theorem conj_sumCongr_embL {r s : ℕ} (σ₁ y : Perm (Fin r × Bool)) (σ₂ : Perm (Fin s)) :
    Perm.sumCongr σ₁ σ₂ * embL r s y * (Perm.sumCongr σ₁ σ₂)⁻¹ = embL r s (σ₁ * y * σ₁⁻¹) := by
  have h : Perm.sumCongr σ₁ σ₂ = Perm.sumCongrHom (Fin r × Bool) (Fin s) (σ₁, σ₂) := rfl
  rw [h]
  unfold embL
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  simp

theorem sumCongr_mem_normalizer {r s : ℕ} {σ₁ : Perm (Fin r × Bool)} (hσ₁ : σ₁ ∈ wStab (Fin r) Bool)
    (σ₂ : Perm (Fin s)) :
    Perm.sumCongr σ₁ σ₂ ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := by
  have hσ : σ₁ ∈ blockStab (Fin r) := mem_blockStab.2 (mem_wStab.1 hσ₁)
  have key : ∀ (τ₁ : Perm (Fin r × Bool)), τ₁ ∈ blockStab (Fin r) → ∀ τ₂ : Perm (Fin s),
      ∀ k ∈ Wr r s, Perm.sumCongr τ₁ τ₂ * k * (Perm.sumCongr τ₁ τ₂)⁻¹ ∈ Wr r s := by
    intro τ₁ hτ τ₂ k hk
    obtain ⟨y, hy, rfl⟩ := hk
    rw [conj_sumCongr_embL]
    exact ⟨_, conj_mem_blockFix hτ hy, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key σ₁ hσ σ₂ h hh, fun hh => ?_⟩
  have := key σ₁⁻¹ ((blockStab (Fin r)).inv_mem hσ) σ₂⁻¹ _ hh
  have e : (Perm.sumCongr σ₁⁻¹ σ₂⁻¹) = (Perm.sumCongr σ₁ σ₂)⁻¹ := by
    ext x <;> simp
  have e2 : Perm.sumCongr σ₁⁻¹ σ₂⁻¹ * (Perm.sumCongr σ₁ σ₂ * h * (Perm.sumCongr σ₁ σ₂)⁻¹) *
      (Perm.sumCongr σ₁⁻¹ σ₂⁻¹)⁻¹ = h := by
    rw [e]; group
  rwa [e2] at this

theorem exists_sumCongr_of_mem_normalizer {r s : ℕ} {g : Perm (OmegaE r s)}
    (hg : g ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s)))) :
    ∃ σ₁ ∈ wStab (Fin r) Bool, ∃ σ₂ : Perm (Fin s), g = Perm.sumCongr σ₁ σ₂ := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := inv_mem hg
  have hmaps : Set.MapsTo g (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨p, rfl⟩
    rcases hq : g (Sum.inl p) with q | j
    · exact ⟨q, rfl⟩
    · exfalso
      obtain ⟨j', hj'⟩ := normalizer_Wr_inr hginv j
      have : g⁻¹ (Sum.inr j) = Sum.inl p := by rw [← hq]; simp
      rw [this] at hj'
      exact Sum.inl_ne_inr hj'
  obtain ⟨⟨σ₁, σ₂⟩, hσ⟩ := Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
  have hgeq : g = Perm.sumCongr σ₁ σ₂ := hσ.symm
  refine ⟨σ₁, ?_, σ₂, hgeq⟩
  have hnorm : σ₁ ∈ Subgroup.normalizer (blockFix (Fin r) : Set (Perm (Fin r × Bool))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hc := (Subgroup.mem_normalizer_iff.1 hg) (embL r s y)
    rw [hgeq, conj_sumCongr_embL] at hc
    constructor
    · intro hy
      have : embL r s (σ₁ * y * σ₁⁻¹) ∈ Wr r s := hc.1 ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzz⟩ := this
      have := embL_injective r s hzz
      rw [← this]; exact hz
    · intro hy
      have : embL r s (σ₁ * y * σ₁⁻¹) ∈ Wr r s := ⟨_, hy, rfl⟩
      obtain ⟨z, hz, hzz⟩ := hc.2 this
      have := embL_injective r s hzz
      rw [← this]; exact hz
  have hfl : ∀ i : Fin r, ∃ w ∈ blockFix (Fin r), w (i, false) = (i, true) := fun i =>
    ⟨swap (i, false) (i, true), swap_mem_blockFix rfl, swap_apply_left _ _⟩
  have := blockStab_of_mem_normalizer (le_refl _) hfl hnorm
  exact mem_wStab.2 (mem_blockStab.1 this)

theorem mem_normalizer_Wr_iff {r s : ℕ} {g : Perm (OmegaE r s)} :
    g ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) ↔
      ∃ σ₁ ∈ wStab (Fin r) Bool, ∃ σ₂ : Perm (Fin s), g = Perm.sumCongr σ₁ σ₂ :=
  ⟨exists_sumCongr_of_mem_normalizer, by
    rintro ⟨σ₁, h₁, σ₂, rfl⟩
    exact sumCongr_mem_normalizer h₁ σ₂⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
