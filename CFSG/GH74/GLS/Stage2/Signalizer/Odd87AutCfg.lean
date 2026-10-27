module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

structure AutCfg (K : Type) [Group K] (α : MulAut K) (p : ℕ) (Xb : Subgroup (MulAut K)) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  alpha_sq : α * α = 1
  alpha_ne : α ≠ 1
  pgroup : IsPGroup p ↥Xb
  ne_bot : Xb ≠ ⊥
  alpha_norm : α ∈ normalizer (Xb : Set (MulAut K))
  cent_norm : ∀ k : K, α * MulAut.conj k = MulAut.conj k * α →
    MulAut.conj k ∈ normalizer (Xb : Set (MulAut K))
  comm : ⁅Xb, zpowers α⁆ = Xb

section Reduction

variable {A : Type} [Group A] [Finite A]

noncomputable def layerHom (A : Type) [Group A] [Finite A] : A →* MulAut ↥(layer A) :=
  haveI : (layer A).Normal := layer_normal
  MulAut.conjNormal

theorem layerHom_apply (a : A) (x : ↥(layer A)) : ((layerHom A a x : ↥(layer A)) : A) = a * x * a⁻¹ := by
  have : (layer A).Normal := layer_normal
  exact MulAut.conjNormal_apply a x

theorem layerHom_eq_layerAut (a : A) : layerHom A a = layerAut a := by
  ext x
  rw [layerHom_apply, coe_layerAut]

theorem layerHom_coe (k : ↥(layer A)) : layerHom A (k : A) = MulAut.conj k := by
  ext x
  rw [layerHom_apply, MulAut.conj_apply]
  rfl

theorem layerHom_mem_normalizer {X : Subgroup A} {g : A} (hg : g ∈ normalizer (X : Set A)) :
    layerHom A g ∈ normalizer ((X.map (layerHom A) : Subgroup (MulAut ↥(layer A))) : Set (MulAut ↥(layer A))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hx, by simp⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp ((normalizer (X : Set A)).inv_mem hg) x).mp hx
      simpa using this
    · have : layerHom A x = layerHom A g * y * (layerHom A g)⁻¹ := hxy
      rw [map_mul, map_mul, map_inv, this]
      group

theorem autCfg_of_cellData {zb : A} {p : ℕ} {X : Subgroup A} (h : CellData zb p X)
    (hZ : center ↥(layer A) = ⊥) :
    AutCfg ↥(layer A) (layerAut zb) p (X.map (layerHom A)) := by
  classical
  have hKn : (layer A).Normal := layer_normal
  have hαφ : layerAut zb = layerHom A zb := (layerHom_eq_layerAut zb).symm
  have hnc : ∃ k ∈ layer A, ∃ x ∈ X, ⁅k, x⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply h.nc
    rw [Subgroup.commutator_le]
    intro k hk x hx
    have := hcon k hk x hx
    rw [this]
    exact Subgroup.one_mem _
  refine ⟨h.A4.prime, h.A4.odd, ?_, ?_, h.A4.pgroup.map _, ?_, ?_, ?_, ?_⟩
  · ext x
    rw [MulAut.mul_apply, layerAut_layerAut h.z2]
    rfl
  · intro h1
    obtain ⟨k, hk, hne⟩ := h.exists_not_commute
    apply hne
    have h2 : layerAut zb ⟨k, hk⟩ = ⟨k, hk⟩ := by rw [h1]; rfl
    have h3 := congrArg Subtype.val h2
    rw [coe_layerAut] at h3
    simp only at h3
    calc zb * k = (zb * k * zb⁻¹) * zb := by group
      _ = k * zb := by rw [h3]
  · intro hbot
    obtain ⟨k, hk, x, hx, hne⟩ := hnc
    apply hne
    have hx1 : layerHom A x = 1 := by
      have : layerHom A x ∈ (⊥ : Subgroup (MulAut ↥(layer A))) := hbot ▸ Subgroup.mem_map_of_mem _ hx
      exact this
    have h4 := congrArg (fun σ : MulAut ↥(layer A) => ((σ ⟨k, hk⟩ : ↥(layer A)) : A)) hx1
    simp only [layerHom_apply, MulAut.one_apply] at h4
    calc ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
      _ = 1 := by
        have : x * k⁻¹ * x⁻¹ = k⁻¹ := by
          have h5 : x * k * x⁻¹ = k := h4
          calc x * k⁻¹ * x⁻¹ = (x * k * x⁻¹)⁻¹ := by group
            _ = k⁻¹ := by rw [h5]
        rw [this]; group
  · rw [hαφ]
    exact layerHom_mem_normalizer (z_mem_normalizer_of_sig4A h.A4)
  · intro k hk
    set kk : ↥(layer A) := k with hkk
    have h1 : layerAut zb * MulAut.conj k = MulAut.conj (layerAut zb k) * layerAut zb := by
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply]
    rw [h1] at hk
    have h2 : MulAut.conj (layerAut zb k) = MulAut.conj k := by
      have := congrArg (fun σ : MulAut ↥(layer A) => σ * (layerAut zb)⁻¹) hk
      simpa using this
    have h3 : layerAut zb k = k := by
      have h4 : (layerAut zb k)⁻¹ * k ∈ center ↥(layer A) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h5 := congrArg (fun σ : MulAut ↥(layer A) => σ g) h2
        simp only [MulAut.conj_apply] at h5
        calc g * ((layerAut zb k)⁻¹ * k) = (layerAut zb k)⁻¹ * ((layerAut zb k) * g * (layerAut zb k)⁻¹) * k := by group
          _ = (layerAut zb k)⁻¹ * (k * g * k⁻¹) * k := by rw [h5]
          _ = ((layerAut zb k)⁻¹ * k) * g := by group
      rw [hZ, Subgroup.mem_bot] at h4
      exact inv_mul_eq_one.mp h4
    have h6 : zb * (k : A) = (k : A) * zb := by
      have h7 := congrArg Subtype.val h3
      rw [coe_layerAut] at h7
      calc zb * (k : A) = (zb * k * zb⁻¹) * zb := by group
        _ = k * zb := by rw [h7]
    have hkN : (k : A) ∈ normalizer (X : Set A) :=
      h.A4.inv k (Subgroup.mem_top _) (Subgroup.mem_centralizer_singleton_iff.mpr h6.symm)
    rw [← layerHom_coe k]
    exact layerHom_mem_normalizer hkN
  · rw [hαφ, ← MonoidHom.map_zpowers, ← Subgroup.map_commutator, h.A4.comm]

end Reduction

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
