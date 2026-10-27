module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL34c
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL33Facts

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem SCert.SE.gen1_mul_self : SE.gen 1 * SE.gen 1 = SE.gen 0 := by decide

theorem SCert.SE.gen1_mul_gen0_sq : SE.gen 1 * SE.gen 0 * (SE.gen 1 * SE.gen 0) = SE.gen 0 := by
  decide

theorem SCert.SE.one_mul_self_ne_gen0 : (1 : SE) * 1 ≠ SE.gen 0 := by decide

theorem SCert.SE.gen0_mul_self_ne_gen0 : SE.gen 0 * SE.gen 0 ≠ SE.gen 0 := by decide

namespace GHSylow

variable (D : GHSylow G)

abbrev l : G := D.toG (SE.gen 1)

omit [Finite G] in
theorem l_mem_E : D.l ∈ D.E := (D.toG_mem_E_iff).mpr SE.gen_predE.1

omit [Finite G] in
theorem l_mem_F : D.l ∈ D.F := (D.toG_mem_F_iff).mpr SE.gen_predF.1

omit [Finite G] in
theorem z_mem_E : D.z ∈ D.E := (D.toG_mem_E_iff).mpr SE.gen0_predE

omit [Finite G] in
theorem z_mem_F : D.z ∈ D.F := (D.toG_mem_F_iff).mpr SE.gen0_predF

omit [Finite G] in
theorem l_mul_l : D.l * D.l = D.z := by rw [← map_mul, SE.gen1_mul_self]

omit [Finite G] in
theorem lz_sq : D.l * D.z * (D.l * D.z) = D.z := by
  rw [← map_mul, ← map_mul, SE.gen1_mul_gen0_sq]

omit [Finite G] in
theorem eq_l_of_comm_gens {w₀ : SE} (hsq : w₀ * w₀ = SE.gen 0)
    (hc : w₀ = 1 ∨ w₀ = SE.gen 1 ∨ w₀ = SE.gen 0 ∨ w₀ = SE.gen 1 * SE.gen 0) :
    D.toG w₀ = D.l ∨ D.toG w₀ = D.l * D.z := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact absurd hsq SE.one_mul_self_ne_gen0
  · exact Or.inl rfl
  · exact absurd hsq SE.gen0_mul_self_ne_gen0
  · exact Or.inr (map_mul _ _ _)

theorem eq_l_of_conj {g w : G} (hg : g ∈ D.M)
    (hw : w ∈ (D.S : Subgroup G)) (h : g⁻¹ * w * g = D.l ∨ g⁻¹ * w * g = D.l * D.z) :
    w = D.l ∨ w = D.l * D.z := by
  have hgz := D.z_comm_of_mem_M hg
  have hw2 : w * w = D.z := by
    have h1 : g⁻¹ * (w * w) * g = D.z := by
      rw [show g⁻¹ * (w * w) * g = (g⁻¹ * w * g) * (g⁻¹ * w * g) by group]
      rcases h with h | h <;> rw [h]
      · exact D.l_mul_l
      · exact D.lz_sq
    calc w * w = g * (g⁻¹ * (w * w) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * D.z * g) * g⁻¹ := by rw [h1, hgz]
      _ = D.z := by group
  have hy : ∀ x : G, x ∈ D.E ∨ x ∈ D.F → (g⁻¹ * w * g) * x = x * (g⁻¹ * w * g) := by
    rintro x hx
    have hxz : x * D.z = D.z * x := by
      obtain ⟨x₀, -, rfl⟩ : x ∈ (⊤ : Subgroup SE).map D.toG := by
        rcases hx with ⟨x₀, -, rfl⟩ | ⟨x₀, -, rfl⟩ <;> exact ⟨x₀, mem_top _, rfl⟩
      rw [← map_mul, ← map_mul, SE.mul_gen0_comm]
    have hxl : x * D.l = D.l * x := by
      rcases hx with ⟨x₀, hx₀, rfl⟩ | ⟨x₀, hx₀, rfl⟩
      · rw [← map_mul, ← map_mul, SE.l_comm_E x₀ hx₀]
      · rw [← map_mul, ← map_mul, SE.l_comm_F x₀ hx₀]
    rcases h with h | h <;> rw [h]
    · exact hxl.symm
    · rw [mul_assoc, ← hxz, ← mul_assoc, ← hxl, mul_assoc]
  rcases D.mem_E_or_F hw hw2 with hE | hF
  · obtain ⟨k, -, hkE, hk⟩ := D.exists_normalizer_E hE hg
      (h.elim (fun h' => h' ▸ D.l_mem_E) fun h' => h' ▸ mul_mem D.l_mem_E D.z_mem_E)
    obtain ⟨w₀, hw₀, rfl⟩ := hE
    have hcomm : ∀ e ∈ D.E, D.toG w₀ * e = e * D.toG w₀ := by
      intro e he
      have := hy _ (Or.inl (hkE e he))
      rw [← hk] at this
      have h' : k⁻¹ * (D.toG w₀ * e) * k = k⁻¹ * (e * D.toG w₀) * k := by
        rw [show k⁻¹ * (D.toG w₀ * e) * k = k⁻¹ * D.toG w₀ * k * (k⁻¹ * e * k) by group, this]
        group
      simpa using h'
    have hc : ∀ i : Fin 9, SE.predE (SE.gen i) → w₀ * SE.gen i = SE.gen i * w₀ := fun i hi =>
      D.toG_injective (by rw [map_mul, map_mul]; exact hcomm _ ((D.toG_mem_E_iff).mpr hi))
    refine D.eq_l_of_comm_gens (D.toG_injective (by rw [map_mul, hw2])) (SE.center_E w₀ hw₀
      (hc 1 SE.gen_predE.1) (hc 2 SE.gen_predE.2.1) (hc 3 SE.gen_predE.2.2.1)
      (hc 4 SE.gen_predE.2.2.2.1) (hc 5 SE.gen_predE.2.2.2.2))
  · obtain ⟨k, -, hkF, hk⟩ := D.exists_normalizer_F hF hg
      (h.elim (fun h' => h' ▸ D.l_mem_F) fun h' => h' ▸ mul_mem D.l_mem_F D.z_mem_F)
    obtain ⟨w₀, hw₀, rfl⟩ := hF
    have hcomm : ∀ f ∈ D.F, D.toG w₀ * f = f * D.toG w₀ := by
      intro f hf
      have := hy _ (Or.inr (hkF f hf))
      rw [← hk] at this
      have h' : k⁻¹ * (D.toG w₀ * f) * k = k⁻¹ * (f * D.toG w₀) * k := by
        rw [show k⁻¹ * (D.toG w₀ * f) * k = k⁻¹ * D.toG w₀ * k * (k⁻¹ * f * k) by group, this]
        group
      simpa using h'
    have hc : ∀ i : Fin 9, SE.predF (SE.gen i) → w₀ * SE.gen i = SE.gen i * w₀ := fun i hi =>
      D.toG_injective (by rw [map_mul, map_mul]; exact hcomm _ ((D.toG_mem_F_iff).mpr hi))
    refine D.eq_l_of_comm_gens (D.toG_injective (by rw [map_mul, hw2])) (SE.center_F w₀ hw₀
      (hc 1 SE.gen_predF.1) (hc 2 SE.gen_predF.2.1) (hc 3 SE.gen_predF.2.2.1)
      (hc 6 SE.gen_predF.2.2.2.1) (hc 7 SE.gen_predF.2.2.2.2))

end GHSylow

end CFSG.ComponentClassification.GHarris
