module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb2

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem SCert.SE.exists_gen_conj_mul_z_S1 : ∀ u : SE, u.d.val < 4 → u * u = 1 → u ≠ 1 →
    u ≠ gen 0 → ∃ i : Fin 8, (gen i.castSucc)⁻¹ * (u * gen 0) * gen i.castSucc = u := by
  decide +kernel

theorem SCert.SE.gen_lt_four : ∀ i : Fin 8, (gen i.castSucc).d.val < 4 := by decide

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

omit [Finite Y] in
theorem toG_mem_S1 {s₀ : SE} (hs : s₀.d.val < 4) : D.toG s₀ ∈ D.S1 :=
  mem_inf.mpr ⟨D.toG_mem s₀, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, (SE.mem_centralizer_l_iff s₀).mpr hs])⟩

theorem exists_conj_Y1_of_conj_Xt {u₁ u₂ : D.Y1} (hu₂S : (u₂ : Y) ∈ D.S1)
    (hu₁2 : u₁ * u₁ = 1) (hu₂2 : u₂ * u₂ = 1) (hu₂1 : u₂ ≠ 1) (hu₂z : (u₂ : Y) ≠ D.z)
    {g : D.Y1} (hg : D.piX (g⁻¹ * u₁ * g) = D.piX u₂) : ∃ h : D.Y1, h⁻¹ * u₁ * h = u₂ := by
  obtain ⟨w, hw⟩ : ∃ w, w = g⁻¹ * u₁ * g := ⟨_, rfl⟩
  rw [← hw] at hg
  have hw2 : w * w = 1 := by
    rw [hw, show g⁻¹ * u₁ * g * (g⁻¹ * u₁ * g) = g⁻¹ * (u₁ * u₁) * g by group, hu₁2]; group
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, D.mem_zpowers_l_iff]
    at hg
  obtain ⟨c, hc⟩ : ∃ c, c = w⁻¹ * u₂ := ⟨_, rfl⟩
  rw [← hc] at hg
  have hu₂ : u₂ = w * c := by rw [hc]; group
  have hcl : ∀ y : D.Y1, y * c = c * y := by
    intro y
    have hcen : ∀ v : D.Y1, ((v : Y) = 1 ∨ (v : Y) = D.l ∨ (v : Y) = D.z ∨
        (v : Y) = D.l * D.z) → y * v = v * y := by
      intro v hv
      have hyl : (y : Y) * D.l = D.l * y := mem_centralizer_singleton_iff.mp y.2
      have hyz : (y : Y) * D.z = D.z * y := by
        have := mem_centralizer_singleton_iff.mp (D.l_mem_M)
        calc (y : Y) * D.z = y * (D.l * D.l) := by rw [D.l_mul_l]
          _ = D.l * D.l * y := by rw [← mul_assoc, hyl, mul_assoc, hyl, mul_assoc]
          _ = D.z * y := by rw [D.l_mul_l]
      apply Subtype.ext
      rcases hv with h | h | h | h <;> simp only [Subgroup.coe_mul] <;> rw [h]
      · simp
      · exact hyl
      · exact hyz
      · rw [← mul_assoc, hyl, mul_assoc, hyz, mul_assoc]
    exact hcen c hg
  have hc2 : c * c = 1 := by
    have h1 : u₂ * u₂ = w * w * (c * c) := by
      calc u₂ * u₂ = (w * c) * (w * c) := by rw [← hu₂]
        _ = w * (c * w) * c := by group
        _ = w * (w * c) * c := by rw [← hcl w]
        _ = w * w * (c * c) := by group
    rw [hu₂2, hw2, one_mul] at h1
    exact h1.symm
  have hc' : (c : Y) = 1 ∨ (c : Y) = D.z := by
    rcases hg with h | h | h | h
    · exact Or.inl h
    · exfalso
      have : (c : Y) * c = D.l * D.l := by rw [h]
      rw [← Subgroup.coe_mul, hc2, Subgroup.coe_one, D.l_mul_l] at this
      exact D.z_ne_one this.symm
    · exact Or.inr h
    · exfalso
      have : (c : Y) * c = D.l * D.z * (D.l * D.z) := by rw [h]
      rw [← Subgroup.coe_mul, hc2, Subgroup.coe_one, D.lz_sq] at this
      exact D.z_ne_one this.symm
  rcases hc' with h | h
  · refine ⟨g, ?_⟩
    rw [← hw, hu₂, show c = 1 from Subtype.ext h, mul_one]
  ·
    obtain ⟨u₀, hu₀⟩ := D.exists_toG (mem_inf.mp hu₂S).1
    have hu₀d : u₀.d.val < 4 := D.pre_mem_S1 (by rw [hu₀]; exact hu₂S)
    have hu₀2 : u₀ * u₀ = 1 := D.toG_injective (by
      rw [map_mul, hu₀, map_one, ← Subgroup.coe_mul, hu₂2, Subgroup.coe_one])
    have hu₀1 : u₀ ≠ 1 := fun h1 => hu₂1 (Subtype.ext (by rw [← hu₀, h1, map_one]; rfl))
    have hu₀z : u₀ ≠ SE.gen 0 := fun h1 => hu₂z (by rw [← hu₀, h1])
    obtain ⟨i, hi⟩ := SE.exists_gen_conj_mul_z_S1 u₀ hu₀d hu₀2 hu₀1 hu₀z
    have hsY : D.toG (SE.gen i.castSucc) ∈ D.Y1 := D.S1_le_Y1 (D.toG_mem_S1 (SE.gen_lt_four i))
    refine ⟨g * ⟨_, hsY⟩, Subtype.ext ?_⟩
    have hw' : (w : Y) = (u₂ : Y) * D.z := by
      have : (u₂ : Y) = w * c := by rw [hu₂]; rfl
      rw [this, h, mul_assoc, D.z_mul_z, mul_one]
    calc ((g * ⟨_, hsY⟩)⁻¹ * u₁ * (g * ⟨_, hsY⟩) : D.Y1) =
        (D.toG (SE.gen i.castSucc))⁻¹ * (w : Y) * D.toG (SE.gen i.castSucc) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw]; group
      _ = D.toG ((SE.gen i.castSucc)⁻¹ * (u₀ * SE.gen 0) * SE.gen i.castSucc) := by
          rw [hw', ← hu₀]; simp only [map_mul, map_inv]
      _ = u₂ := by rw [hi, hu₀]

end GHSylow

end CFSG.ComponentClassification.GHarris
