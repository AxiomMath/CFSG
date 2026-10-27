module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryAffine
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace ProjectiveGeometry

open Module

variable {K : Type*} [Field K] {d : ℕ}

theorem infinityPoint_smul {c : K} (hc : c ≠ 0) (u : Fin d → K) :
    infinityPoint (c • u) = infinityPoint u := by
  have h : extend (c • u) 0 = c • extend u 0 := by rw [extend_smul, mul_zero]
  rw [infinityPoint, infinityPoint, h, Submodule.span_singleton_smul_eq hc.isUnit]

theorem infinityPoint_single_add_single (i j : Fin d) :
    infinityPoint (Pi.single i (1 : K) + Pi.single j 1) =
      K ∙ (Pi.single i.castSucc 1 + Pi.single j.castSucc 1 : Fin (d + 1) → K) := by
  rw [infinityPoint, ← add_zero (0 : K), ← extend_add, extend_single, extend_single]

theorem common_coordinate_map
    (Ψ : Submodule K (Fin (d + 1) → K) ≃o Submodule K (Fin (d + 1) → K))
    (hΨe : ∀ i : Fin (d + 1), Ψ (K ∙ Pi.single i 1) = K ∙ Pi.single i 1)
    (hΨ1 : Ψ (K ∙ (1 : Fin (d + 1) → K)) = K ∙ (1 : Fin (d + 1) → K)) :
    ∃ σ : K ≃ K, σ 0 = 0 ∧ σ 1 = 1 ∧
      (∀ x : Fin d → K, Ψ (affinePoint x) = affinePoint fun i => σ (x i)) ∧
      ∀ i j : Fin d, i ≠ j →
        Ψ (K ∙ (Pi.single i.castSucc 1 + Pi.single j.castSucc 1 : Fin (d + 1) → K)) =
          K ∙ (Pi.single i.castSucc 1 + Pi.single j.castSucc 1 : Fin (d + 1) → K) := by
  classical
  obtain ⟨-, φ, hφ, ⟨f, hf01, hφf⟩, hline⟩ := affine_coordinates Ψ hΨe hΨ1
  have hφ0 : φ 0 = 0 := by
    rw [hφf]
    funext k
    exact (hf01 k).1
  have hdiag : ∀ i j : Fin d, i ≠ j → (∀ t, f i t = f j t) ∧
      Ψ (infinityPoint (Pi.single i 1 + Pi.single j 1)) =
        infinityPoint (Pi.single i 1 + Pi.single j 1) := by
    intro i j hij
    set u : Fin d → K := Pi.single i 1 + Pi.single j 1 with hu
    have hui : u i = 1 := by simp [hu, Pi.single_eq_of_ne hij]
    have huj : u j = 1 := by simp [hu, Pi.single_eq_of_ne hij.symm]
    have hu0 : u ≠ 0 := fun h => one_ne_zero (hui.symm.trans (congrFun h i))
    have hφu : φ u = u := by
      rw [hφf]
      funext k
      by_cases hki : k = i
      · subst hki
        rw [hui, (hf01 k).2]
      by_cases hkj : k = j
      · subst hkj
        rw [huj, (hf01 k).2]
      · have huk : u k = 0 := by simp [hu, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
        rw [huk, (hf01 k).1]
    obtain ⟨u', hu', hΨu, hl⟩ := hline u hu0
    have himg := hl 0
    rw [hφ0] at himg
    have hmemu : φ u ∈ φ '' affineLine 0 u := Set.mem_image_of_mem φ ⟨1, by simp⟩
    rw [himg, hφu] at hmemu
    obtain ⟨s, hs⟩ := hmemu
    simp only [zero_add] at hs
    have hs0 : s ≠ 0 := fun h => hu0 (by rw [← hs, h, zero_smul])
    have hu'eq : u' = s⁻¹ • u := by
      rw [← hs, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [hu'eq, affineLine_smul (inv_ne_zero hs0)] at himg
    refine ⟨fun t => ?_, ?_⟩
    · have hmem : φ (t • u) ∈ affineLine 0 u := by
        rw [← himg]
        exact Set.mem_image_of_mem φ ⟨t, by simp⟩
      obtain ⟨r, hr⟩ := hmem
      have h1 := congrFun hr i
      have h2 := congrFun hr j
      rw [hφf] at h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hui, huj, mul_one, zero_add,
        Pi.zero_apply] at h1 h2
      rw [← h1, ← h2]
    · rw [hΨu, hu'eq, infinityPoint_smul (inv_ne_zero hs0)]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨Equiv.refl K, rfl, rfl, fun x => ?_, fun i => i.elim0⟩
    rw [hφ x]
    congr 1
    funext i
    exact i.elim0
  set σ := f ⟨0, hd⟩ with hσ
  have hfσ : ∀ i t, f i t = σ t := by
    intro i t
    by_cases hi : i = ⟨0, hd⟩
    · rw [hi]
    · exact (hdiag i ⟨0, hd⟩ hi).1 t
  refine ⟨σ, (hf01 _).1, (hf01 _).2, fun x => ?_, fun i j hij => ?_⟩
  · rw [hφ x, hφf]
    simp_rw [hfσ]
  · rw [← infinityPoint_single_add_single]
    exact (hdiag i j hij).2

theorem coordinate_map_field (hd : 2 ≤ d)
    (Ψ : Submodule K (Fin (d + 1) → K) ≃o Submodule K (Fin (d + 1) → K))
    (hΨe : ∀ i : Fin (d + 1), Ψ (K ∙ Pi.single i 1) = K ∙ Pi.single i 1)
    (hΨ1 : Ψ (K ∙ (1 : Fin (d + 1) → K)) = K ∙ (1 : Fin (d + 1) → K)) :
    ∃ σ : K ≃+* K, ∀ x : Fin d → K, Ψ (affinePoint x) = affinePoint fun i => σ (x i) := by
  classical
  obtain ⟨σ, hσ0, hσ1, hσ, hdirfix⟩ := common_coordinate_map Ψ hΨe hΨ1
  obtain ⟨-, φ, hφ, -, hline⟩ := affine_coordinates Ψ hΨe hΨ1
  have hφσ : ∀ x, φ x = fun i => σ (x i) := fun x =>
    affinePoint_injective ((hφ x).symm.trans (hσ x))
  have hφ0 : φ 0 = 0 := by
    rw [hφσ]
    funext k
    exact hσ0
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin d := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by
    rw [hi₀, hi₁, Ne, Fin.ext_iff]
    exact zero_ne_one
  have hadd : ∀ b x : K, σ (b + x) = σ b + σ x := by
    intro b x
    set u : Fin d → K := Pi.single i₀ 1 + Pi.single i₁ 1 with hu
    have hu₀ : u i₀ = 1 := by simp [hu, Pi.single_eq_of_ne h01]
    have hu₁ : u i₁ = 1 := by simp [hu, Pi.single_eq_of_ne h01.symm]
    have hu0 : u ≠ 0 := fun h => one_ne_zero (hu₀.symm.trans (congrFun h i₀))
    obtain ⟨u', hu', hΨu, hl⟩ := hline u hu0
    have hfix : Ψ (infinityPoint u) = infinityPoint u := by
      rw [hu, infinityPoint_single_add_single]
      exact hdirfix i₀ i₁ h01
    obtain ⟨c, hc, rfl⟩ := eq_smul_of_infinityPoint_eq hu' (hfix.symm.trans hΨu)
    set p : Fin d → K := b • Pi.single i₁ 1 with hp
    have hp₀ : p i₀ = 0 := by simp [hp, Pi.single_eq_of_ne h01]
    have hp₁ : p i₁ = b := by simp [hp]
    have hmem : φ (p + x • u) ∈ affineLine (φ p) (c • u) := by
      rw [← hl p]
      exact Set.mem_image_of_mem φ ⟨x, rfl⟩
    rw [affineLine_smul hc] at hmem
    obtain ⟨r, hr⟩ := hmem
    have e₀ := congrFun hr i₀
    have e₁ := congrFun hr i₁
    rw [hφσ, hφσ] at e₀ e₁
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp₀, hp₁, hu₀, hu₁, mul_one, zero_add,
      hσ0] at e₀ e₁
    rw [← e₁, ← e₀]
  have hmul : ∀ a x : K, σ (x * a) = σ x * σ a := by
    intro a x
    set u : Fin d → K := Pi.single i₀ 1 + a • Pi.single i₁ 1 with hu
    have hu₀ : u i₀ = 1 := by simp [hu, Pi.single_eq_of_ne h01]
    have hu₁ : u i₁ = a := by simp [hu, Pi.single_eq_of_ne h01.symm]
    have hu0 : u ≠ 0 := fun h => one_ne_zero (hu₀.symm.trans (congrFun h i₀))
    obtain ⟨u', -, -, hl⟩ := hline u hu0
    have hmem1 : φ u ∈ affineLine (φ 0) u' := by
      rw [← hl 0]
      exact Set.mem_image_of_mem φ ⟨1, by simp⟩
    have hmem2 : φ (x • u) ∈ affineLine (φ 0) u' := by
      rw [← hl 0]
      exact Set.mem_image_of_mem φ ⟨x, by simp⟩
    rw [hφ0] at hmem1 hmem2
    obtain ⟨s, hs⟩ := hmem1
    obtain ⟨r, hr⟩ := hmem2
    have e₁ := congrFun hs i₀
    have e₂ := congrFun hs i₁
    have e₃ := congrFun hr i₀
    have e₄ := congrFun hr i₁
    rw [hφσ] at e₁ e₂ e₃ e₄
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu₀, hu₁, mul_one, zero_add,
      Pi.zero_apply, hσ1] at e₁ e₂ e₃ e₄
    rw [← e₄, ← e₃, ← e₂]
    linear_combination (-(r * u' i₁)) * e₁
  refine ⟨{ σ with
    map_mul' := fun x y => hmul y x
    map_add' := fun x y => hadd x y }, fun x => hσ x⟩

end ProjectiveGeometry

end CFSG.LocalAnalysis.ComponentInitial
