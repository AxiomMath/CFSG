module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XPerm

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

private lemma swap_fixed_pair :
    ∀ a b : Fin 4, a ≠ b →
      ∃ c d : Fin 4, c ≠ d ∧ ∀ i, (Equiv.swap a b) i = i ↔ (i = c ∨ i = d) := by
  decide +kernel

theorem exists_fixed_pair (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    (hm : ∀ u ∈ F, u ∉ centralizer (V : Set X) →
      2 ^ 6 ≤ Nat.card {v : V // u * (v : X) * u⁻¹ = v})
    {τ : normalizer (V : Set X)} (hτF : (τ : X) ∈ F) (hτ : planeHom hS τ ≠ 1) :
    ∃ c d : Fin 4, c ≠ d ∧ ∀ f ∈ F, ∀ w ∈ W c ⊔ W d, f * w * f⁻¹ = w := by
  classical
  have hmv : ∀ y : normalizer (V : Set X), (y : X) ∈ F → planeHom hS y ≠ 1 → mval hS y ≤ 2 := by
    intro y hyF hy1
    have hyC : (y : X) ∉ centralizer (V : Set X) := by
      intro hyC
      apply hy1
      refine planeHom_eq_one_of_centralizes hS y fun v hv => ?_
      have h := Subgroup.mem_centralizer_iff.mp hyC v hv
      rw [mul_inv_eq_iff_eq_mul]
      exact h.symm
    have h1 := card_centralizer_le_mval hS y (hF.sq (y : X) hyF)
    have h3 : 2 ^ 6 ≤ 2 ^ (8 - mval hS y) := (hm (y : X) hyF hyC).trans h1
    have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
    omega
  have hmoved : ∀ y : normalizer (V : Set X), (y : X) ∈ F → planeHom hS y ≠ 1 →
      (Finset.univ.filter fun i : Fin 4 => planeHom hS y i ≠ i).card ≤ 2 := by
    intro y hyF hy1
    have h := hmv y hyF hy1
    unfold mval at h
    omega
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 4), planeHom hS τ = π := ⟨_, rfl⟩
  have hπ1 : π ≠ 1 := hπ ▸ hτ
  have hmoved2 : (Finset.univ.filter fun i : Fin 4 => π i ≠ i).card = 2 := by
    have h := hmoved τ hτF hτ
    rw [hπ] at h
    exact le_antisymm h (perm_two_le_moved hπ1)
  obtain ⟨a, b, hab, hπab⟩ := perm_eq_swap_of_moved_two hmoved2
  obtain ⟨c, d, hcd, hcdfix⟩ := swap_fixed_pair a b hab
  have hfix : ∀ i, π i = i ↔ (i = c ∨ i = d) := fun i => by rw [hπab]; exact hcdfix i
  have hA : ∀ y : normalizer (V : Set X), (y : X) ∈ F → planeHom hS y = π →
      ∀ i, π i = i → ¬ ActsNontriv (W i) (y : X) := by
    intro y hyF hyπ i hi hnt
    have h := hmv y hyF (hyπ ▸ hπ1)
    unfold mval at h
    rw [hyπ] at h
    have hpos : 0 < (Finset.univ.filter fun i : Fin 4 =>
        π i = i ∧ ActsNontriv (W i) (y : X)).card :=
      Finset.card_pos.mpr ⟨i, by simp [hi, hnt]⟩
    omega
  obtain ⟨-, hmul, hsq⟩ := planeImage_group hS hF
  have hπmem : π ∈ planeImage hS F := (mem_planeImage hS).mpr ⟨τ, hτF, hπ⟩
  have hB : ∀ f : normalizer (V : Set X), (f : X) ∈ F → planeHom hS f ≠ 1 →
      planeHom hS f = π := by
    intro f hfF hf1
    by_contra hne
    have hm1 := hmoved f hfF hf1
    have hm0 : (Finset.univ.filter fun i : Fin 4 => π i ≠ i).card ≤ 2 := hmoved2.le
    have hπ'mem : planeHom hS f ∈ planeImage hS F := (mem_planeImage hS).mpr ⟨f, hfF, rfl⟩
    have h1 : π * π = 1 := hsq π hπmem
    have h2 : planeHom hS f * planeHom hS f = 1 := hsq _ hπ'mem
    have h3 : (π * planeHom hS f) * (π * planeHom hS f) = 1 :=
      hsq _ (hmul π hπmem _ hπ'mem)
    have hc : π * planeHom hS f = planeHom hS f * π := by
      have e1 : π * planeHom hS f = (π * planeHom hS f)⁻¹ := eq_inv_of_mul_eq_one_left h3
      rw [mul_inv_rev] at e1
      rw [e1, inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h1]
    have h4 := perm_moved_four h1 h2 hc (Ne.symm hne) hπ1 hf1 (by omega) (by omega)
    have hτfF : ((τ * f : normalizer (V : Set X)) : X) ∈ F := F.mul_mem hτF hfF
    have hτf1 : planeHom hS (τ * f) ≠ 1 := by
      rw [map_mul, hπ]
      intro h
      rw [h] at h4
      simp at h4
    have h5 := hmoved (τ * f) hτfF hτf1
    rw [map_mul, hπ] at h5
    omega
  have hC : ∀ f : normalizer (V : Set X), (f : X) ∈ F → planeHom hS f = 1 →
      ∀ i, π i = i → ∀ w ∈ W i, (f : X) * w * (f : X)⁻¹ = w := by
    intro f hfF hf1 i hi w hw
    have hτf : planeHom hS (τ * f) = π := by rw [map_mul, hf1, mul_one, hπ]
    have h1 : (τ : X) * (f : X) * w * ((τ : X) * (f : X))⁻¹ = w :=
      not_actsNontriv_iff.mp (hA (τ * f) (F.mul_mem hτF hfF) hτf i hi) w hw
    have h2 : (τ : X) * w * (τ : X)⁻¹ = w := not_actsNontriv_iff.mp (hA τ hτF hπ i hi) w hw
    calc (f : X) * w * (f : X)⁻¹
        = (τ : X)⁻¹ * ((τ : X) * (f : X) * w * ((τ : X) * (f : X))⁻¹) * (τ : X) := by group
      _ = (τ : X)⁻¹ * w * (τ : X) := by rw [h1]
      _ = (τ : X)⁻¹ * ((τ : X) * w * (τ : X)⁻¹) * (τ : X) := by rw [h2]
      _ = w := by group
  have htriv : ∀ f ∈ F, ∀ i, π i = i → ∀ w ∈ W i, f * w * f⁻¹ = w := by
    intro f hf i hi w hw
    have hfn := hF.le_normalizer hf
    by_cases h1 : planeHom hS ⟨f, hfn⟩ = 1
    · exact hC ⟨f, hfn⟩ hf h1 i hi w hw
    · exact not_actsNontriv_iff.mp (hA ⟨f, hfn⟩ hf (hB ⟨f, hfn⟩ hf h1) i hi) w hw
  have hle : ∀ i, π i = i → W i ≤ centralizer (F : Set X) := by
    intro i hi w hw
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact mul_inv_eq_iff_eq_mul.mp (htriv f hf i hi w hw)
  refine ⟨c, d, hcd, fun f hf w hw => ?_⟩
  have hmem := sup_le (hle c ((hfix c).mpr (Or.inl rfl))) (hle d ((hfix d).mpr (Or.inr rfl))) hw
  have h := Subgroup.mem_centralizer_iff.mp hmem f hf
  calc f * w * f⁻¹ = w * f * f⁻¹ := by rw [h]
    _ = w := by group

end CFSG.OddStandard.SmallF3.Omega
