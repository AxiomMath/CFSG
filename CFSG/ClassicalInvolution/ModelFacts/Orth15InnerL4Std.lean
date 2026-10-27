module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Rig
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.FrameVertex CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem mem_center_of_conj_mem_center {S : Type*} [Group S] {g a : S}
    (h : g * a * g⁻¹ ∈ Subgroup.center S) : a ∈ Subgroup.center S := by
  have := Subgroup.Normal.conj_mem inferInstance _ h g⁻¹
  have e : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
  rwa [e] at this

theorem u0_not_central : u0 F ∉ Subgroup.center SL(4, F) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have e := congrFun (congrFun hr 0) 1
  simp [coe_u0, Matrix.scalar_apply] at e

theorem t0_not_central : t0 F ∉ Subgroup.center SL(4, F) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have e := congrFun (congrFun hr 0) 1
  simp [coe_t0, Matrix.scalar_apply] at e

theorem x0_not_central (h2 : (2 : F) ≠ 0) : x0 F ∉ Subgroup.center SL(4, F) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have e0 := congrFun (congrFun hr 0) 0
  have e2 := congrFun (congrFun hr 2) 2
  simp [coe_x0, Matrix.scalar_apply] at e0 e2
  apply h2
  linear_combination e0 - e2

theorem coe_r0_inv : ((r0⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_r0, Matrix.adjugate_fin_two_of]
  simp

theorem t0_eq_blk : t0 F = blk r0⁻¹ r0 := by
  apply Subtype.ext
  rw [coe_t0, coe_blk, coe_r0_inv, coe_r0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_conj_t0 [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ g' : SL(4, F), g' * u0 F * g'⁻¹ = t0 F ∧ g' * x0 F * g'⁻¹ = x0 F := by
  have hr : ((r0⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (r0⁻¹ : SL(2, F)) = -1 := by
    rw [coe_r0_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨h, hh⟩ := exists_conj_r0 h2 r0⁻¹ hr
  have hhr : h * r0 = r0⁻¹ * h := mul_inv_eq_iff_eq_mul.mp hh
  refine ⟨blockSL F 4 2 0 (by norm_num) h, ?_, ?_⟩
  · rw [mul_inv_eq_iff_eq_mul, t0_eq_blk, u0_eq_blk, blk, blk]
    calc blockSL F 4 2 0 (by norm_num) h * (blockSL F 4 2 0 (by norm_num) r0 *
          blockSL F 4 2 2 (by norm_num) r0)
        = blockSL F 4 2 0 (by norm_num) (h * r0) * blockSL F 4 2 2 (by norm_num) r0 := by
          rw [map_mul, mul_assoc]
      _ = blockSL F 4 2 0 (by norm_num) (r0⁻¹ * h) * blockSL F 4 2 2 (by norm_num) r0 := by
          rw [hhr]
      _ = blockSL F 4 2 0 (by norm_num) r0⁻¹ * (blockSL F 4 2 0 (by norm_num) h *
          blockSL F 4 2 2 (by norm_num) r0) := by rw [map_mul, mul_assoc]
      _ = blockSL F 4 2 0 (by norm_num) r0⁻¹ * (blockSL F 4 2 2 (by norm_num) r0 *
          blockSL F 4 2 0 (by norm_num) h) := by rw [blockSL_comm h r0]
      _ = (blockSL F 4 2 0 (by norm_num) r0⁻¹ * blockSL F 4 2 2 (by norm_num) r0) *
          blockSL F 4 2 0 (by norm_num) h := by rw [mul_assoc]
  · rw [mul_inv_eq_iff_eq_mul]
    exact blockSL_zero_comm_x0 h

theorem rigid_psl4 [Finite F] [Group.IsPerfect SL(4, F)] (h2 : (2 : F) ≠ 0)
    {H : Type} [Group H] (ψ : SL(4, F) →* H) (hker : ψ.ker ≤ Subgroup.center SL(4, F))
    (g : SL(4, F)) (Q : Subgroup SL(4, F)) (hU1 : U1 F ∈ Q) (c : ↥(inducedAutOn ψ.range))
    (hodd : Odd (orderOf c))
    (hQ₁ : ∀ q ∈ R0 F ⊔ R0' F, c * innerHom ψ (g * q * g⁻¹) = innerHom ψ (g * q * g⁻¹) * c)
    (hQ₂ : ∀ q ∈ Q, c * innerHom ψ (g * q * g⁻¹) = innerHom ψ (g * q * g⁻¹) * c) : c = 1 := by
  have hπ : Function.Surjective (proj 4 F) := proj_surjective 4 F
  have hπk : (proj 4 F).ker = Subgroup.center SL(4, F) :=
    (ker_proj (n := 4) (K := F)).trans (scalars_eq_center 4 F)
  set φ : MulAut (projectiveSL 4 F) := outerAction ψ hker (proj 4 F) hπ hπk c with hφ
  have hfix : ∀ r : SL(4, F), c * innerHom ψ r = innerHom ψ r * c →
      φ (proj 4 F r) = proj 4 F r := by
    intro r hr
    apply (outerEquiv ψ hker (proj 4 F) hπ hπk).injective
    apply Subtype.ext
    rw [hφ, outerAction_apply, outerEquiv_apply, hr]
    group
  set γ : MulAut (projectiveSL 4 F) := MulAut.conj (proj 4 F g) with hγ
  have hγp : ∀ s : SL(4, F), γ (proj 4 F s) = proj 4 F (g * s * g⁻¹) := fun s => by
    rw [hγ, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set α : MulAut (projectiveSL 4 F) := γ⁻¹ * φ * γ with hα
  have hαp : ∀ s : SL(4, F), α (proj 4 F s) = (γ⁻¹) (φ (γ (proj 4 F s))) := fun s => rfl
  have hαfix : ∀ q : SL(4, F),
      c * innerHom ψ (g * q * g⁻¹) = innerHom ψ (g * q * g⁻¹) * c →
        α (proj 4 F q) = proj 4 F q := by
    intro q hq
    rw [hαp, hγp, hfix _ hq, ← hγp]
    simp
  have hφn : φ ^ orderOf c = 1 := by
    rw [hφ, ← map_pow, pow_orderOf_eq_one, map_one]
  have hαn : α ^ orderOf c = 1 := by
    have := conj_pow (a := γ⁻¹) (b := φ) (i := orderOf c)
    rw [inv_inv] at this
    rw [hα, this, hφn]
    group
  have hα1 : α = 1 := by
    refine eq_one_of_fix_U1 h2 α hodd hαn ?_ ?_ ?_
    · intro r hr
      exact hαfix r (hQ₁ r (Subgroup.mem_sup_left (by simpa [R0] using hr)))
    · intro r hr
      exact hαfix r (hQ₁ r (Subgroup.mem_sup_right (by simpa [R0'] using hr)))
    · exact hαfix _ (hQ₂ _ hU1)
  have hφ1 : φ = 1 := by
    have : φ = γ * α * γ⁻¹ := by rw [hα]; group
    rw [this, hα1]
    group
  exact eq_one_of_outerAction_eq_one ψ hker (proj 4 F) hπ hπk hφ1

theorem alphaOf_klein_psl4 [Finite F] [Group.IsPerfect SL(4, F)] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F)
    (hQ : ∃ Q : Subgroup SL(4, F), SLayer (u0 F) Q ∧ t0 F ∈ Q ∧ U1 F ∈ Q)
    {H : Type} [Group H] [Finite H] (ψ : SL(4, F) →* H)
    (hker : ψ.ker ≤ Subgroup.center SL(4, F)) (hz : ψ (zneg F) = 1) (g : SL(4, F)) :
    alphaOf (Subgroup.closure ({innerHom ψ (g * u0 F * g⁻¹), innerHom ψ (g * x0 F * g⁻¹)} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  obtain ⟨hcen, hnorm, -⟩ := innerHom_spec ψ hker
  have : (innerHom ψ).range.Normal := hnorm
  obtain ⟨Q, hQu, ht0Q, hU1Q⟩ := hQ
  obtain ⟨g', hg'u, hg'x⟩ := exists_conj_t0 h2
  have hekernel : (innerHom ψ).ker ≤ Subgroup.center SL(4, F) := fun s hs => hcen s hs
  let τ : MulAut SL(4, F) := MulAut.conj g
  have hτ : ∀ s, τ s = g * s * g⁻¹ := fun s => rfl
  have hτz : τ (zneg F) = zneg F := by
    rw [hτ, Subgroup.mem_center_iff.mp zneg_mem_center g]
    group
  have hez : innerHom ψ (zneg F) = 1 := by
    have : (⟨ψ (zneg F), mem_normalizer_range ψ (zneg F)⟩ :
        ↥(Subgroup.normalizer (ψ.range : Set H))) = 1 := Subtype.ext hz
    rw [innerHom_apply, this, map_one]
  have ht0u : t0 F = x0 F * u0 F := rfl
  have hux : u0 F * x0 F = t0 F := x0_mul_u0.symm
  have hxt : x0 F * t0 F = u0 F := by rw [ht0u, ← mul_assoc, x0_mul_self, one_mul]
  have hg't : g' * t0 F * g'⁻¹ = u0 F := by
    calc g' * t0 F * g'⁻¹ = (g' * x0 F * g'⁻¹) * (g' * u0 F * g'⁻¹) := by rw [ht0u]; group
      _ = u0 F := by rw [hg'x, hg'u, hxt]
  show alphaOf (Subgroup.closure ({innerHom ψ (τ (u0 F)), innerHom ψ (τ (x0 F))} :
      Set ↥(inducedAutOn ψ.range))) = ⊥
  have hb12 : innerHom ψ (τ (u0 F)) * innerHom ψ (τ (x0 F)) = innerHom ψ (τ (t0 F)) := by
    rw [← map_mul, ← map_mul, hux]
  have hb₁sq : innerHom ψ (τ (u0 F)) * innerHom ψ (τ (u0 F)) = 1 := by
    rw [← map_mul, ← map_mul, u0_mul_self, hτz, hez]
  have hb₂sq : innerHom ψ (τ (x0 F)) * innerHom ψ (τ (x0 F)) = 1 := by
    rw [← map_mul, ← map_mul, x0_mul_self, map_one, map_one]
  have hcomm : innerHom ψ (τ (u0 F)) * innerHom ψ (τ (x0 F)) =
      innerHom ψ (τ (x0 F)) * innerHom ψ (τ (u0 F)) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, x0_mul_u0]
  have hne₁ : innerHom ψ (τ (u0 F)) ≠ 1 := fun h => by
    have := hcen _ h
    rw [hτ] at this
    exact u0_not_central (mem_center_of_conj_mem_center this)
  have hne₂ : innerHom ψ (τ (x0 F)) ≠ 1 := fun h => by
    have := hcen _ h
    rw [hτ] at this
    exact x0_not_central h2 (mem_center_of_conj_mem_center this)
  have hne₃ : innerHom ψ (τ (u0 F)) * innerHom ψ (τ (x0 F)) ≠ 1 := fun h => by
    rw [hb12] at h
    have := hcen _ h
    rw [hτ] at this
    exact t0_not_central (mem_center_of_conj_mem_center this)
  have hL₁ := (slayer_x0 h2 h4).map τ
  have hL₂ := hQu.map τ
  have hL₃ := (hQu.map (MulAut.conj g')).map τ
  rw [show (MulAut.conj g') (u0 F) = t0 F from hg'u] at hL₃
  set B : Subgroup ↥(inducedAutOn ψ.range) := Subgroup.closure
    ({innerHom ψ (τ (u0 F)), innerHom ψ (τ (x0 F))} : Set ↥(inducedAutOn ψ.range)) with hB
  have hu0Q' : u0 F ∈ Q.map (MulAut.conj g').toMonoidHom := ⟨t0 F, ht0Q, hg't⟩
  have hx0eq : innerHom ψ (τ (x0 F)) =
      innerHom ψ (τ (t0 F)) * (innerHom ψ (τ (u0 F)))⁻¹ := by
    rw [ht0u, map_mul, map_mul, mul_inv_cancel_right]
  have hcov₁ : B ≤ Subgroup.zpowers (innerHom ψ (τ (x0 F))) ⊔
      ((R0 F ⊔ R0' F).map τ.toMonoidHom).map (innerHom ψ) := by
    rw [hB, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_right ⟨τ (u0 F), ⟨u0 F, u0_mem, rfl⟩, rfl⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hcov₂ : B ≤ Subgroup.zpowers (innerHom ψ (τ (u0 F))) ⊔
      (Q.map τ.toMonoidHom).map (innerHom ψ) := by
    rw [hB, Subgroup.closure_le]
    have hP : innerHom ψ (τ (t0 F)) ∈ (Q.map τ.toMonoidHom).map (innerHom ψ) :=
      ⟨τ (t0 F), ⟨t0 F, ht0Q, rfl⟩, rfl⟩
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [hx0eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hP)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  have hcov₃ : B ≤ Subgroup.zpowers (innerHom ψ (τ (t0 F))) ⊔
      ((Q.map (MulAut.conj g').toMonoidHom).map τ.toMonoidHom).map (innerHom ψ) := by
    rw [hB, Subgroup.closure_le]
    have hP : innerHom ψ (τ (u0 F)) ∈
        ((Q.map (MulAut.conj g').toMonoidHom).map τ.toMonoidHom).map (innerHom ψ) :=
      ⟨τ (u0 F), ⟨u0 F, hu0Q', rfl⟩, rfl⟩
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_right hP
    · rw [hx0eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hP))
  have d₁ := hL₁.layerData (innerHom ψ) hekernel B hcov₁
  have d₂ := hL₂.layerData (innerHom ψ) hekernel B hcov₂
  have d₃ := hL₃.layerData (innerHom ψ) hekernel B hcov₃
  have d₃' : LayerData (innerHom ψ).range B
      (innerHom ψ (τ (u0 F)) * innerHom ψ (τ (x0 F)))
      (((Q.map (MulAut.conj g').toMonoidHom).map τ.toMonoidHom).map (innerHom ψ)) := by
    rw [hb12]
    exact d₃
  refine alphaOf_klein_of_three_layers (innerHom ψ).range ⟨_, rfl⟩ ⟨_, rfl⟩ hb₁sq hb₂sq hcomm
    hne₁ hne₂ hne₃ d₂ d₁ d₃' ?_
  intro c hodd hc₁ hc₂ _
  refine rigid_psl4 h2 ψ hker g Q hU1Q c hodd ?_ ?_
  · intro q hq
    exact hc₂ _ ⟨τ q, ⟨q, hq, rfl⟩, rfl⟩
  · intro q hq
    exact hc₁ _ ⟨τ q, ⟨q, hq, rfl⟩, rfl⟩

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
