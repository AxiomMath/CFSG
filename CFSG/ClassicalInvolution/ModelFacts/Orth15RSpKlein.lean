module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpLayer
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Std

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp

open QuadraticAlgebra CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Sp
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (QE r0 coe_r0 exists_conj_r0 sl2_sq_cases
  mem_sup_of_comm isQuasisimple_sl2 sup_le_normalizer_of_comm exists_sq_add_sq)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (sp4_aut_blocks)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]


theorem rigid_psp [Finite F] [Group.IsPerfect (StatedSp 2 F)] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) {H : Type} [Group H] (ψ : StatedSp 2 F →* H)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (g : StatedSp 2 F)
    (c : ↥(inducedAutOn ψ.range)) (hodd : Odd (orderOf c))
    (hQ : ∀ q ∈ R0 F ⊔ R0' F, c * innerHom ψ (g * q * g⁻¹) = innerHom ψ (g * q * g⁻¹) * c) :
    c = 1 := by
  have hπ : Function.Surjective (proj 2 F) := proj_surjective
  have hπk : (proj 2 F).ker = Subgroup.center (StatedSp 2 F) :=
    ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 F).symm
  set φ : MulAut (StatedProj (StatedSp 2 F)) := outerAction ψ hker (proj 2 F) hπ hπk c with hφ
  have hfix : ∀ r : StatedSp 2 F, c * innerHom ψ r = innerHom ψ r * c →
      φ (proj 2 F r) = proj 2 F r := by
    intro r hr
    apply (outerEquiv ψ hker (proj 2 F) hπ hπk).injective
    apply Subtype.ext
    rw [hφ, outerAction_apply, outerEquiv_apply, hr]
    group
  set γ : MulAut (StatedProj (StatedSp 2 F)) := MulAut.conj (proj 2 F g) with hγ
  have hγp : ∀ s : StatedSp 2 F, γ (proj 2 F s) = proj 2 F (g * s * g⁻¹) := fun s => by
    rw [hγ, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set α : MulAut (StatedProj (StatedSp 2 F)) := γ⁻¹ * φ * γ with hα
  have hαp : ∀ s : StatedSp 2 F, α (proj 2 F s) = (γ⁻¹) (φ (γ (proj 2 F s))) := fun s => rfl
  have hαfix : ∀ q : StatedSp 2 F,
      c * innerHom ψ (g * q * g⁻¹) = innerHom ψ (g * q * g⁻¹) * c →
        α (proj 2 F q) = proj 2 F q := by
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
  have hα2 : α * α = 1 := by
    refine sp4_aut_blocks h2 h4 α fun k r hr => ?_
    have hmem : r ∈ R0 F ⊔ R0' F := by
      fin_cases k
      · exact Subgroup.mem_sup_left hr
      · exact Subgroup.mem_sup_right hr
    exact hαfix r (hQ r hmem)
  have hα1 : α = 1 := by
    obtain ⟨m, hm⟩ := hodd
    have : α ^ (2 * m + 1) = α := by
      rw [pow_succ, pow_mul, pow_two, hα2, one_pow, one_mul]
    rw [← this, ← hm, hαn]
  have hφ1 : φ = 1 := by
    have : φ = γ * α * γ⁻¹ := by rw [hα]; group
    rw [this, hα1]
    group
  exact eq_one_of_outerAction_eq_one ψ hker (proj 2 F) hπ hπk hφ1


theorem alphaOf_klein_psp [Finite F] [Group.IsPerfect (StatedSp 2 F)] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) {H : Type} [Group H] [Finite H] (ψ : StatedSp 2 F →* H)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (hz : ψ (zneg F) = 1) (g : StatedSp 2 F) :
    alphaOf (Subgroup.closure ({innerHom ψ (g * u0 F * g⁻¹), innerHom ψ (g * x0 F * g⁻¹)} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  obtain ⟨hcen, hnorm, -⟩ := innerHom_spec ψ hker
  have : (innerHom ψ).range.Normal := hnorm
  obtain ⟨Q, hQu, ht0Q⟩ := exists_layer_u0 h2 h4
  obtain ⟨g', hg'u, hg'x⟩ := exists_conj_t0 h2
  have hekernel : (innerHom ψ).ker ≤ Subgroup.center (StatedSp 2 F) := fun s hs => hcen s hs
  let τ : MulAut (StatedSp 2 F) := MulAut.conj g
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
    exact u0_not_central (InnerL4.mem_center_of_conj_mem_center this)
  have hne₂ : innerHom ψ (τ (x0 F)) ≠ 1 := fun h => by
    have := hcen _ h
    rw [hτ] at this
    exact x0_not_central h2 (InnerL4.mem_center_of_conj_mem_center this)
  have hne₃ : innerHom ψ (τ (u0 F)) * innerHom ψ (τ (x0 F)) ≠ 1 := fun h => by
    rw [hb12] at h
    have := hcen _ h
    rw [hτ] at this
    exact t0_not_central (InnerL4.mem_center_of_conj_mem_center this)
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
  refine rigid_psp h2 h4 ψ hker g c hodd ?_
  intro q hq
  exact hc₂ _ ⟨τ q, ⟨q, hq, rfl⟩, rfl⟩


end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
