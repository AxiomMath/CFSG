module

public import CFSG.Quasithin.Background.SmithB42Sp4Nat
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.Quasithin.B42Sp4 (spM)
open CFSG.Quasithin.H (StdMod natAut natImage natNorm)
open CFSG.QuasithinUnique.Setup.Layer (binPsi)
open CFSG.QuasithinUnique.Setup.Layer.Actor
  (natCard_fixGL_map natCard_eq isElemAbelian2_iff_map)

private def b2linear_theta {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F)) :
    StdMod (Fin 2 ⊕ Fin 2) F ≃* Multiplicative M :=
  (AddEquiv.toMultiplicative φ).symm

private theorem b2linear_binPsi_natAut_apply {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F)) (s : StatedSp 2 F) (w : M) :
    binPsi (b2linear_theta φ) (natAut (StatedSp 2 F) s) w = φ.symm ((spM s).mulVec (φ w)) :=
  rfl

private theorem b2linear_binPsi_natAut {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F))
    (π : StatedSp 2 F →* (M ≃ₗ[ZMod 2] M)) (α : MulAut (StatedSp 2 F))
    (hφ : ∀ g w, φ (π g w) = (spM (α g)).mulVec (φ w)) (g : StatedSp 2 F) :
    binPsi (b2linear_theta φ) (natAut (StatedSp 2 F) (α g)) = π g := by
  refine LinearEquiv.ext fun w => ?_
  rw [b2linear_binPsi_natAut_apply, ← hφ g w, AddEquiv.symm_apply_apply]

private theorem b2linear_map_natImage_eq {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F))
    (π : StatedSp 2 F →* (M ≃ₗ[ZMod 2] M)) (α : MulAut (StatedSp 2 F))
    (hφ : ∀ g w, φ (π g w) = (spM (α g)).mulVec (φ w)) :
    (natImage (StatedSp 2 F)).map (binPsi (b2linear_theta φ)).toMonoidHom = π.range := by
  ext x
  constructor
  · rintro ⟨z, ⟨γ, rfl⟩, rfl⟩
    exact ⟨α⁻¹ γ, by
      simpa using (b2linear_binPsi_natAut φ π α hφ (α⁻¹ γ)).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨natAut (StatedSp 2 F) (α g), ⟨α g, rfl⟩,
      b2linear_binPsi_natAut φ π α hφ g⟩

private theorem b2linear_mem_natImage_iff {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F))
    (π : StatedSp 2 F →* (M ≃ₗ[ZMod 2] M)) (α : MulAut (StatedSp 2 F))
    (hφ : ∀ g w, φ (π g w) = (spM (α g)).mulVec (φ w))
    (z : MulAut (StdMod (Fin 2 ⊕ Fin 2) F)) :
    z ∈ natImage (StatedSp 2 F) ↔ binPsi (b2linear_theta φ) z ∈ π.range := by
  rw [← b2linear_map_natImage_eq φ π α hφ]
  exact (Subgroup.mem_map_iff_mem (binPsi (b2linear_theta φ)).injective).symm

private theorem b2linear_mem_natNorm_of_normalizes {F : Type} [Field F] {M : Type}
    [AddCommGroup M] [Module (ZMod 2) M] (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F))
    (π : StatedSp 2 F →* (M ≃ₗ[ZMod 2] M)) (α : MulAut (StatedSp 2 F))
    (hφ : ∀ g w, φ (π g w) = (spM (α g)).mulVec (φ w))
    {A : Subgroup (M ≃ₗ[ZMod 2] M)} (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    {a' : MulAut (StdMod (Fin 2 ⊕ Fin 2) F)} (ha' : binPsi (b2linear_theta φ) a' ∈ A) :
    a' ∈ natNorm (StatedSp 2 F) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [b2linear_mem_natImage_iff φ π α hφ, b2linear_mem_natImage_iff φ π α hφ,
    map_mul, map_mul, map_inv]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := hnorm _ ha' x
    exact ⟨y, by rw [← hx]; exact hy.symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hnorm _ (inv_mem ha') y
    refine ⟨x, ?_⟩
    rw [← hx, hy]
    group

theorem eq_rep_of_offender_of_natural_sp4 {F : Type} [Field F] [CharP F 2] [Fintype F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (π : StatedSp 2 F →* (M ≃ₗ[ZMod 2] M)) (α : MulAut (StatedSp 2 F))
    (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F)) (hφ : ∀ g w, φ (π g w) = (spM (α g)).mulVec (φ w))
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A)
    (hoff : Nat.card M ≤ Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m}) :
    ∀ a ∈ A, ∃ x, ∀ w, a w = π x w := by
  classical
  set θ := b2linear_theta φ with hθ
  set A' : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) F)) :=
    A.comap (binPsi θ).toMonoidHom with hA'
  have hA'map : A'.map (binPsi θ).toMonoidHom = A :=
    Subgroup.map_comap_eq_self_of_surjective (binPsi θ).surjective A
  have hE : CFSG.Quasithin.IsElemAbelian2 A' :=
    (isElemAbelian2_iff_map θ A').mpr (by rw [hA'map]; exact hAe)
  have hEN : A' ≤ natNorm (StatedSp 2 F) := fun a' ha' =>
    b2linear_mem_natNorm_of_normalizes φ π α hφ hnorm ha'
  have hcardA : Nat.card A' = Nat.card A := by
    have h1 : Nat.card (A'.map (binPsi θ).toMonoidHom) = Nat.card A' :=
      Subgroup.card_map_of_injective (binPsi θ).injective
    rw [hA'map] at h1
    exact h1.symm
  have hcardF : Nat.card (CFSG.Quasithin.fixV A') =
      Nat.card {m : M // ∀ a ∈ A, a m = m} := by
    have h1 := natCard_fixGL_map θ A'
    rw [hA'map] at h1
    exact h1.symm
  have hcardV : Nat.card (StdMod (Fin 2 ⊕ Fin 2) F) = Nat.card M := natCard_eq θ
  have hnat : A' ≤ natImage (StatedSp 2 F) := by
    by_contra hnot
    have hlt := CFSG.Quasithin.FFC.Sp4Off.card_mul_card_fixV_lt hn hF hEN hE hnot
    rw [hcardA, hcardF, hcardV] at hlt
    omega
  intro a ha
  rw [← hA'map] at ha
  obtain ⟨a', ha', ha'a⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy⟩ := hnat ha'
  have h2 : binPsi θ a' = π (α⁻¹ y) := by
    rw [← hy]
    simpa using b2linear_binPsi_natAut φ π α hφ (α⁻¹ y)
  have h3 : a = π (α⁻¹ y) := by
    rw [← ha'a]
    exact h2
  refine ⟨α⁻¹ y, fun w => ?_⟩
  rw [h3]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
