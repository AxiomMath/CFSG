module

public import CFSG.LieType.Chevalley.RootIdealNormality
public import CFSG.LieType.Steinberg.Adjoint.CommAll
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Matrix

variable {τ : Tag}

theorem dotProduct_mulVec_symmetrizedCartan_eq_sum (u v : Fin τ.rank → ℤ) :
    u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) = ∑ i, ∑ j, u i * τ.symmetrizedCartan i j * v j := by
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem rootForm_smul
    (w : WeylGroup τ) (u v : Fin τ.rank → ℤ) :
    (w • u) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (w • v)) = u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) := by
  obtain ⟨c, hc, h⟩ := RootSpace.exists_inner_eq_smul τ
  have h1 := h (RootSpace.ofLattice (w • u)) (RootSpace.ofLattice (w • v))
  have h2 := h (RootSpace.ofLattice u) (RootSpace.ofLattice v)
  have hinv : inner ℝ (RootSpace.ofLattice (w • u)) (RootSpace.ofLattice (w • v)) =
      inner ℝ (RootSpace.ofLattice u) (RootSpace.ofLattice v) := by
    rw [← weylAct_ofLattice, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map]
  have h3 := mul_left_cancel₀ hc.ne' (h1.symm.trans (hinv.trans h2))
  simp only [RootSpace.ofLattice_apply] at h3
  rw [dotProduct_mulVec_symmetrizedCartan_eq_sum, dotProduct_mulVec_symmetrizedCartan_eq_sum]
  exact_mod_cast h3

theorem rootForm_self
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : α ⬝ᵥ (τ.symmetrizedCartan *ᵥ α) = 2 := by
  obtain ⟨w, k, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  rw [rootForm_smul, single_dotProduct, one_mul, mulVec_single_one]
  change τ.symmetrizedCartan k k = 2
  rcases hτ with rfl | rfl | rfl | rfl <;> fin_cases k <;> decide

theorem symmetrizedCartan_transpose (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    τ.symmetrizedCartanᵀ = τ.symmetrizedCartan := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide

theorem simply_laced_orthogonal_root_commutation
    (τ : Tag)
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (∀ α : Fin τ.rank → ℤ, IsRoot τ α → α ⬝ᵥ (τ.symmetrizedCartan *ᵥ α) = 2) ∧
    ∀ (R : Type) [CommRing R] (α β : Fin τ.rank → ℤ), IsRoot τ α → IsRoot τ β →
      α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0 →
      ∀ x ∈ rootSubgroup τ R α, ∀ y ∈ rootSubgroup τ R β, x * y = y * x := by
  refine ⟨fun α hα => rootForm_self hτ hα, fun R _ α β hα hβ h0 x hx y hy => ?_⟩
  have hsymm : ∀ u v : Fin τ.rank → ℤ, u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) =
      v ⬝ᵥ (τ.symmetrizedCartan *ᵥ u) := fun u v => by
    rw [dotProduct_mulVec, ← mulVec_transpose, symmetrizedCartan_transpose hτ, dotProduct_comm]
  have hαα := rootForm_self hτ hα
  have hββ := rootForm_self hτ hβ
  have h0' : β ⬝ᵥ (τ.symmetrizedCartan *ᵥ α) = 0 := by rw [hsymm]; exact h0
  have hne : α ≠ β := fun h => by
    subst h
    rw [hαα] at h0
    exact absurd h0 (by norm_num)
  have hne' : α ≠ -β := fun h => by
    subst h
    rw [neg_dotProduct, hββ] at h0
    exact absurd h0 (by norm_num)
  have hlin := Steinberg.Adjoint.linIndepPair_of_ne hα hβ hne hne'
  obtain ⟨w, hwα, hwβ⟩ := Steinberg.Adjoint.exists_weyl_height_pos hα hβ hlin
  have hwne : (⟨w • α, IsRoot.smul hα w⟩ : Root τ) ≠ ⟨w • β, IsRoot.smul hβ w⟩ := fun h =>
    hne (smul_left_cancel _ (congrArg Subtype.val h))
  have hc := ringCommContained_pos R ⟨w • α, IsRoot.smul hα w⟩ ⟨w • β, IsRoot.smul hβ w⟩ hwα hwβ
    hwne
  obtain ⟨ω, -, hω⟩ := (coxeterSystem τ).exists_isReduced w⁻¹
  have ht := (rootOperatorFamily τ).ring_comm_transport_list ω hc
  have hprod : (ω.map (simple τ)).prod = w⁻¹ := hω.symm
  have e1 : (ω.map (simple τ)).prod • (⟨w • α, IsRoot.smul hα w⟩ : Root τ) = ⟨α, hα⟩ :=
    Subtype.ext (by rw [coe_smul_root, hprod, inv_smul_smul])
  have e2 : (ω.map (simple τ)).prod • (⟨w • β, IsRoot.smul hβ w⟩ : Root τ) = ⟨β, hβ⟩ :=
    Subtype.ext (by rw [coe_smul_root, hprod, inv_smul_smul])
  rw [e1, e2] at ht
  rw [rootSubgroup_eq_ringRootSubgroup R hα] at hx
  rw [rootSubgroup_eq_ringRootSubgroup R hβ] at hy
  have hmem := ht x hx y hy
  have hbot : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      γ.1 = a • (⟨α, hα⟩ : Root τ).1 + b • (⟨β, hβ⟩ : Root τ).1),
      (rootOperatorFamily τ).ringRootSubgroup R γ) = ⊥ := by
    refine iSup₂_eq_bot.2 fun γ ⟨a, b, ha, hb, hγ⟩ => absurd (rootForm_self hτ γ.2) ?_
    rw [hγ, ← Nat.cast_smul_eq_nsmul ℤ a α, ← Nat.cast_smul_eq_nsmul ℤ b β]
    simp only [add_dotProduct, dotProduct_add, mulVec_add, mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hαα, hββ, h0, h0']
    intro h
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  rw [hbot, Subgroup.mem_bot] at hmem
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hmem, one_mul]

end CFSG.LieType.Chevalley
