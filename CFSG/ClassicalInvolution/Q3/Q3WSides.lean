module

public import CFSG.ClassicalInvolution.Q3.Q3WAdjust
public import CFSG.ClassicalInvolution.WeakCT.Sides

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {X : Type} [Group X]

theorem rotConj_image_coord :
    (MulAut.conj (rotSL : SL(2, F3))).toMonoidHom '' coordSet F3 = coordSet F3 :=
  image_coordSet_eq (MulAut.conj (rotSL : SL(2, F3))) fun _ hg => rotConj_coord hg

theorem coord_flip (θ : SL(3, F3) →* X) (u : Fin 2) :
    ((θ.comp (MulAut.conj (swapSL : SL(3, F3))).toMonoidHom).comp (blk F3 u)) ''
        coordSet F3 = (θ.comp (blk F3 u.rev)) '' coordSet F3 := by
  have h : (θ.comp (MulAut.conj (swapSL : SL(3, F3))).toMonoidHom).comp (blk F3 u) =
      (θ.comp (blk F3 u.rev)).comp (MulAut.conj (rotSL : SL(2, F3))).toMonoidHom :=
    MonoidHom.ext fun A => congrArg θ (swap_blk u A)
  rw [h, MonoidHom.coe_comp, Set.image_comp, rotConj_image_coord]

theorem coord_agree_base {θ₁ θ₂ : SL(3, F3) →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center SL(3, F3)) (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F3))
    (hM : (B23 F3).map θ₁ = (B12 F3).map θ₂)
    (hcomm : ∀ x ∈ (B12 F3).map θ₁, ∀ y ∈ (B23 F3).map θ₂, x * y = y * x) :
    (θ₁.comp (blockSL F3 3 2 1 (by omega))) '' coordSet F3 =
      (θ₂.comp (blockSL F3 3 2 0 (by omega))) '' coordSet F3 := by
  obtain ⟨α, hα, hαC⟩ := exists_alpha3 (V₀ := (B12 F3).map θ₁) h₁ h₂ rfl rfl hM.symm rfl hcomm
  have h : θ₁.comp (blockSL F3 3 2 1 (by omega)) =
      (θ₂.comp (blockSL F3 3 2 0 (by omega))).comp α.toMonoidHom :=
    MonoidHom.ext fun A => (hα A).symm
  rw [h, MonoidHom.coe_comp, Set.image_comp]
  have : α.toMonoidHom '' coordSet F3 = coordSet F3 := image_coordSet_eq α hαC
  rw [this]

theorem coord_agree_gen (s t : Fin 2) {θ₁ θ₂ : SL(3, F3) →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center SL(3, F3)) (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F3))
    (hM : (Bs F3 s).map θ₁ = (Bs F3 t).map θ₂)
    (hcomm : ∀ x ∈ (Bs F3 s.rev).map θ₁, ∀ y ∈ (Bs F3 t.rev).map θ₂, x * y = y * x) :
    (θ₁.comp (blk F3 s)) '' coordSet F3 = (θ₂.comp (blk F3 t)) '' coordSet F3 := by
  have hflip : ∀ θ : SL(3, F3) →* X, θ.ker ≤ Subgroup.center SL(3, F3) →
      (θ.comp (MulAut.conj (swapSL : SL(3, F3))).toMonoidHom).ker ≤
        Subgroup.center SL(3, F3) :=
    fun θ h => ker_comp_mulEquiv_le_center h _
  fin_cases s <;> fin_cases t
  ·
    have := coord_agree_base (hflip θ₁ h₁) h₂
      (by rw [show B23 F3 = Bs F3 1 from rfl, map_flip_Bs]; exact hM)
      (by
        intro x hx y hy
        rw [show B12 F3 = Bs F3 0 from rfl, map_flip_Bs] at hx
        exact hcomm x hx y hy)
    have h' := coord_flip θ₁ 1
    exact h'.symm.trans this
  ·
    exact (coord_agree_base h₂ h₁ hM.symm (fun x hx y hy => (hcomm y hy x hx).symm)).symm
  ·
    exact coord_agree_base h₁ h₂ hM hcomm
  ·
    have := coord_agree_base h₁ (hflip θ₂ h₂)
      (by rw [show B12 F3 = Bs F3 0 from rfl, map_flip_Bs]; exact hM)
      (by
        intro x hx y hy
        rw [show B23 F3 = Bs F3 1 from rfl, map_flip_Bs] at hy
        exact hcomm x hx y hy)
    have h' := coord_flip θ₂ 0
    exact this.trans h'

theorem exists_extend_side3 (s : Fin 2) (α : SL(2, F3) ≃* SL(2, F3))
    (hα : ∀ g ∈ coordSet F3, α g ∈ coordSet F3) :
    ∃ β : SL(3, F3) ≃* SL(3, F3), (∀ A, β (blk F3 s A) = blk F3 s (α A)) ∧
      (Bs F3 s.rev).map β.toMonoidHom = Bs F3 s.rev ∧
        ∃ γ : SL(2, F3) ≃* SL(2, F3), (∀ A, β (blk F3 s.rev A) = blk F3 s.rev (γ A)) ∧
          ∀ g ∈ coordSet F3, γ g ∈ coordSet F3 := by
  have hext : ∀ α : SL(2, F3) ≃* SL(2, F3), (∀ g ∈ coordSet F3, α g ∈ coordSet F3) →
      ∃ β : SL(3, F3) ≃* SL(3, F3),
        (∀ A, β (blockSL F3 3 2 0 (by omega) A) = blockSL F3 3 2 0 (by omega) (α A)) ∧
          (B23 F3).map β.toMonoidHom = B23 F3 ∧
          ∃ γ : SL(2, F3) ≃* SL(2, F3),
            (∀ C, β (blockSL F3 3 2 1 (by omega) C) = blockSL F3 3 2 1 (by omega) (γ C)) ∧
              ∀ g ∈ coordSet F3, γ g ∈ coordSet F3 := by
    intro α hα
    obtain ⟨t₁, -, ht₁⟩ := coordSet_cases (hα _ (xp_mem_coordSet (one_ne_zero (α := F3))))
    obtain ⟨t₂, -, ht₂⟩ := coordSet_cases (hα _ (xm_mem_coordSet (one_ne_zero (α := F3))))
    exact exists_extend_unip α ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
  fin_cases s
  · obtain ⟨β, hβ0, hβ1, γ, hγ, hγC⟩ := hext α hα
    exact ⟨β, hβ0, hβ1, γ, hγ, hγC⟩
  · let cr : SL(2, F3) ≃* SL(2, F3) := MulAut.conj rotSL
    let sw : SL(3, F3) ≃* SL(3, F3) := MulAut.conj swapSL
    have hcr : ∀ g ∈ coordSet F3, cr g ∈ coordSet F3 := fun g hg => rotConj_coord hg
    have hcrs : ∀ g ∈ coordSet F3, cr.symm g ∈ coordSet F3 := fun g hg => by
      show (MulAut.conj (rotSL : SL(2, F3))).symm g ∈ coordSet F3
      rw [MulAut.conj_symm_apply]
      exact rotConj_inv_coord hg
    let α₀ : SL(2, F3) ≃* SL(2, F3) := cr.symm.trans (α.trans cr.symm)
    have hα₀ : ∀ g ∈ coordSet F3, α₀ g ∈ coordSet F3 := fun g hg =>
      hcrs _ (hα _ (hcrs _ hg))
    obtain ⟨β₀, hβ0, hβ1, γ₀, hγ₀, hγ₀C⟩ := hext α₀ hα₀
    let β₁ : SL(3, F3) ≃* SL(3, F3) := sw.trans (β₀.trans sw)
    have hblk : ∀ (u : Fin 2) (A : SL(2, F3)), sw (blk F3 u A) = blk F3 u.rev (cr A) := fun u A =>
      swap_blk u A
    refine ⟨β₁, fun A => ?_, ?_, cr.trans (γ₀.trans cr), fun A => ?_, fun g hg => ?_⟩
    · change sw (β₀ (sw (blk F3 1 A))) = blk F3 1 (α A)
      rw [hblk 1 A]
      change sw (β₀ (blk F3 0 (cr A))) = _
      rw [show blk F3 0 (cr A) = blockSL F3 3 2 0 (by omega) (cr A) from rfl, hβ0]
      change sw (blk F3 0 (α₀ (cr A))) = _
      rw [hblk 0]
      have : cr (α₀ (cr A)) = α A := by
        change cr (cr.symm (α (cr.symm (cr A)))) = α A
        rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
      change blk F3 1 (cr (α₀ (cr A))) = _
      rw [this]
    · have hmap : ∀ H : Subgroup SL(3, F3), H.map β₁.toMonoidHom =
          ((H.map sw.toMonoidHom).map β₀.toMonoidHom).map sw.toMonoidHom := by
        intro H
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      have e0 : Fin.rev (0 : Fin 2) = 1 := rfl
      have e1 : Fin.rev (1 : Fin 2) = 0 := rfl
      show (Bs F3 0).map β₁.toMonoidHom = Bs F3 0
      rw [hmap, show sw.toMonoidHom = (MulAut.conj (swapSL : SL(3, F3))).toMonoidHom from rfl,
        map_conj_swapSL_Bs 0, e0, show Bs F3 1 = B23 F3 from rfl, hβ1,
        show B23 F3 = Bs F3 1 from rfl, map_conj_swapSL_Bs 1, e1]
    · change sw (β₀ (sw (blk F3 0 A))) = blk F3 0 (cr (γ₀ (cr A)))
      rw [hblk 0 A]
      change sw (β₀ (blk F3 1 (cr A))) = _
      rw [show blk F3 1 (cr A) = blockSL F3 3 2 1 (by omega) (cr A) from rfl, hγ₀ (cr A)]
      change sw (blk F3 1 (γ₀ (cr A))) = _
      rw [hblk 1]
      rfl
    · exact hcr _ (hγ₀C _ (hcr _ hg))

theorem exists_adjust_side3 (s : Fin 2) {θ₀ : SL(3, F3) →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, F3)) {ρ : SL(2, F3) →* X}
    (hρ : Function.Injective ρ) (hrange : ρ.range = (Bs F3 s).map θ₀)
    (hcoord : ρ '' coordSet F3 = (θ₀.comp (blk F3 s)) '' coordSet F3) :
    ∃ θ' : SL(3, F3) →* X, θ'.ker ≤ Subgroup.center SL(3, F3) ∧ θ'.comp (blk F3 s) = ρ ∧
      (Bs F3 s.rev).map θ' = (Bs F3 s.rev).map θ₀ ∧
      (θ'.comp (blk F3 s.rev)) '' coordSet F3 = (θ₀.comp (blk F3 s.rev)) '' coordSet F3 := by
  have hm : Function.Injective (θ₀.comp (blk F3 s)) := comp_blk_injective hθ₀ s
  have hrr : ρ.range = (θ₀.comp (blk F3 s)).range := by rw [hrange, map_Bs]
  let α : SL(2, F3) ≃* SL(2, F3) :=
    (MonoidHom.ofInjective hρ).trans
      ((MulEquiv.subgroupCongr hrr).trans (MonoidHom.ofInjective hm).symm)
  have hα : ∀ A, θ₀ (blk F3 s (α A)) = ρ A := by
    intro A
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hm).apply_symm_apply
      (MulEquiv.subgroupCongr hrr (MonoidHom.ofInjective hρ A)))
    exact h
  have hαC : ∀ g ∈ coordSet F3, α g ∈ coordSet F3 := by
    intro g hg
    have hmem : ρ g ∈ (θ₀.comp (blk F3 s)) '' coordSet F3 := hcoord ▸ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hg'eq⟩ := hmem
    have : α g = g' := hm ((hα g).trans hg'eq.symm)
    rw [this]
    exact hg'
  obtain ⟨β, hβs, hβB, γ, hγ, hγC⟩ := exists_extend_side3 s α hαC
  refine ⟨θ₀.comp β.toMonoidHom, ker_comp_mulEquiv_le_center hθ₀ β, ?_, ?_, ?_⟩
  · refine MonoidHom.ext fun A => ?_
    show θ₀ (β (blk F3 s A)) = ρ A
    rw [hβs, hα]
  · rw [map_comp_mulEquiv, hβB]
  · have h : (θ₀.comp β.toMonoidHom).comp (blk F3 s.rev) =
        (θ₀.comp (blk F3 s.rev)).comp γ.toMonoidHom :=
      MonoidHom.ext fun A => congrArg θ₀ (hγ A)
    rw [h, MonoidHom.coe_comp, Set.image_comp]
    have : γ.toMonoidHom '' coordSet F3 = coordSet F3 := image_coordSet_eq γ hγC
    rw [this]

end CFSG.ClassicalInvolution.Q3.Q3W
