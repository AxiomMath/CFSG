module

public import CFSG.GroupTheory.AutomorphismAction.CommutingPGroup
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.GroupTheory.AutomorphismAction.CommutingPGroup

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_isotropic_of_normalized_two_group {ψ : G →* (V ≃ₗ[ZMod 2] V)}
    {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hψ : Function.Injective ψ) (hiso : ∀ x u v, B (ψ x u) (ψ x v) = B u v)
    {Bb W : Subgroup G} (hW : IsPGroup 2 W) (hBW : Bb ≤ Subgroup.normalizer (W : Set G))
    (hW1 : W ≠ ⊥) :
    ∃ I : Submodule (ZMod 2) V, I ≠ ⊥ ∧ (∀ u ∈ I, ∀ v ∈ I, B u v = 0) ∧
      ∀ b ∈ Bb, ∀ v ∈ I, ψ b v ∈ I := by
  classical
  let σ : ↥W →* (V ≃ₗ[ZMod 2] V) := ψ.comp W.subtype
  let F : Submodule (ZMod 2) V := fixedSubmodule σ
  have hF : ∀ v, v ∈ F ↔ ∀ w : G, w ∈ W → ψ w v = v := fun v =>
    ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w w.2⟩
  have hadj : ∀ x f v, B f (ψ x v) = B (ψ x⁻¹ f) v := fun x f v => by
    have h1 : ψ x (ψ x⁻¹ f) = f := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    calc B f (ψ x v) = B (ψ x (ψ x⁻¹ f)) (ψ x v) := by rw [h1]
      _ = B (ψ x⁻¹ f) v := hiso x _ _
  have hFb : ∀ b ∈ Bb, ∀ v ∈ F, ψ b v ∈ F := by
    intro b hb v hv
    rw [hF] at hv ⊢
    intro w hw
    have hmem : b⁻¹ * w * b ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hBW (Subgroup.inv_mem _ hb)) w).mp hw
      simpa using this
    have hcomm : ψ b * ψ (b⁻¹ * w * b) = ψ w * ψ b := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have h2 := congrArg (fun e : V ≃ₗ[ZMod 2] V => e v) hcomm
    simp only [LinearEquiv.mul_apply, hv _ hmem] at h2
    exact h2.symm
  have hF'b : ∀ b ∈ Bb, ∀ v ∈ B.orthogonal F, ψ b v ∈ B.orthogonal F := by
    intro b hb v hv f hf
    rw [hadj]
    exact hv _ (hFb b⁻¹ (Subgroup.inv_mem _ hb) f hf)
  have hF'w : ∀ x u, u ∈ B.orthogonal F → σ x u ∈ B.orthogonal F := by
    intro x u hu f hf
    show B f (ψ (x : G) u) = 0
    rw [hadj]
    have : ψ (x : G)⁻¹ f = f := (hF f).mp hf _ (Subgroup.inv_mem _ x.2)
    rw [this]
    exact hu f hf
  refine ⟨F ⊓ B.orthogonal F, ?_, fun u hu v hv => hv.2 u hu.1,
    fun b hb v hv => ⟨hFb b hb v hv.1, hF'b b hb v hv.2⟩⟩
  intro hI0
  have hF'bot : B.orthogonal F = ⊥ := by
    by_contra hne
    obtain ⟨u, hu, hu0, hufix⟩ := exists_fixed_of_invariant hW σ _ hF'w hne
    have huF : u ∈ F := hufix
    have : u ∈ F ⊓ B.orthogonal F := ⟨huF, hu⟩
    rw [hI0] at this
    exact hu0 ((Submodule.mem_bot _).mp this)
  have hFtop : F = ⊤ := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl F, hF'bot,
      LinearMap.BilinForm.orthogonal_bot]
  apply hW1
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  apply hψ
  rw [map_one]
  ext v
  have hv : v ∈ F := hFtop ▸ Submodule.mem_top
  exact (hF v).mp hv w hw

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
