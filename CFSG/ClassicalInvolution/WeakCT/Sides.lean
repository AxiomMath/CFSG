module

public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.ClassicalInvolution.WeakCT.TorusAgree

public section

namespace CFSG.ClassicalInvolution.WeakCT

open scoped MatrixGroups

section Sides

variable (K : Type) [Field K]

@[expose] def blk (s : Fin 2) : SL(2, K) →* SL(3, K) :=
  match s with
  | 0 => blockSL K 3 2 0 (by omega)
  | 1 => blockSL K 3 2 1 (by omega)

@[expose] def Bs (s : Fin 2) : Subgroup SL(3, K) :=
  (blk K s).range

@[expose] def Ds (s : Fin 2) : Subgroup SL(3, K) :=
  (diagTorus2 K).map (blk K s)

variable {K}

theorem blk_injective (s : Fin 2) : Function.Injective (blk K s) := by
  fin_cases s
  · exact blockSL_injective (K := K) (m := 3) (k := 2) (i := 0) (by omega)
  · exact blockSL_injective (K := K) (m := 3) (k := 2) (i := 1) (by omega)

theorem comp_blk_injective {X : Type} [Group X] {θ : SL(3, K) →* X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, K)) (s : Fin 2) :
    Function.Injective (θ.comp (blk K s)) := by
  fin_cases s
  · exact comp_blockSL_injective (m := 3) (i := 0) (k := 2) hθ (by omega) (by omega)
  · exact comp_blockSL_injective (m := 3) (i := 1) (k := 2) hθ (by omega) (by omega)

theorem blk_mem_Bs (s : Fin 2) (A : SL(2, K)) : blk K s A ∈ Bs K s :=
  ⟨A, rfl⟩

theorem Ds_le_Bs (s : Fin 2) : Ds K s ≤ Bs K s :=
  Subgroup.map_le_range _ _

theorem map_Ds {X : Type*} [Group X] (θ : SL(3, K) →* X) (s : Fin 2) :
    (Ds K s).map θ = (diagTorus2 K).map (θ.comp (blk K s)) :=
  Subgroup.map_map _ _ _

theorem map_Bs {X : Type*} [Group X] (θ : SL(3, K) →* X) (s : Fin 2) :
    (Bs K s).map θ = (θ.comp (blk K s)).range :=
  (MonoidHom.range_comp _ _).symm

theorem swap_blk (s : Fin 2) (A : SL(2, K)) :
    swapSL * blk K s A * swapSL⁻¹ = blk K s.rev (rotSL * A * rotSL⁻¹) := by
  fin_cases s
  · exact swapSL_mul_blockSL_zero_mul_inv A
  · exact swapSL_mul_blockSL_one_mul_inv A

theorem map_conj_swapSL_Bs (s : Fin 2) :
    (Bs K s).map (MulAut.conj (swapSL : SL(3, K))).toMonoidHom = Bs K s.rev := by
  fin_cases s
  · exact map_conj_swapSL_B12
  · exact map_conj_swapSL_B23

theorem rotSL_mul_torusHom_mul_inv (s : Kˣ) :
    rotSL * torusHom K s * rotSL⁻¹ = torusHom K s⁻¹ := by
  have h : ((rotSL * torusHom K s * rotSL⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      ((torusHom K s⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_inv, coe_torusHom]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotSL, CFSG.ClassicalInvolution.Phan.rotMat, CFSG.ClassicalInvolution.Phan.rotMatInv,
        Matrix.mul_apply, Fin.sum_univ_two]
  exact Subtype.ext h

theorem map_conj_rotSL_diagTorus2 :
    (diagTorus2 K).map (MulAut.conj (rotSL : SL(2, K))).toMonoidHom = diagTorus2 K := by
  ext A
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s⁻¹, (rotSL_mul_torusHom_mul_inv s).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨torusHom K s⁻¹, ⟨s⁻¹, rfl⟩, ?_⟩
    change rotSL * torusHom K s⁻¹ * rotSL⁻¹ = torusHom K s
    rw [rotSL_mul_torusHom_mul_inv, inv_inv]

theorem map_conj_swapSL_Ds (s : Fin 2) :
    (Ds K s).map (MulAut.conj (swapSL : SL(3, K))).toMonoidHom = Ds K s.rev := by
  have h : (MulAut.conj (swapSL : SL(3, K))).toMonoidHom.comp (blk K s) =
      (blk K s.rev).comp (MulAut.conj (rotSL : SL(2, K))).toMonoidHom :=
    MonoidHom.ext fun A => swap_blk s A
  unfold Ds
  rw [Subgroup.map_map, h, ← Subgroup.map_map, map_conj_rotSL_diagTorus2]

end Sides

section Flip

variable {K : Type} [Field K] {X : Type*} [Group X]

theorem map_flip_Bs (θ : SL(3, K) →* X) (u : Fin 2) :
    (Bs K u).map (θ.comp (MulAut.conj (swapSL : SL(3, K))).toMonoidHom) = (Bs K u.rev).map θ := by
  rw [map_comp_mulEquiv, map_conj_swapSL_Bs]

theorem map_flip_Ds (θ : SL(3, K) →* X) (u : Fin 2) :
    (Ds K u).map (θ.comp (MulAut.conj (swapSL : SL(3, K))).toMonoidHom) = (Ds K u.rev).map θ := by
  rw [map_comp_mulEquiv, map_conj_swapSL_Ds]

end Flip

section TorusAgree

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem torus_agree_gen (hK : 3 ≤ Nat.card K) (s t : Fin 2) {θ₁ θ₂ : SL(3, K) →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center SL(3, K)) (h₂ : θ₂.ker ≤ Subgroup.center SL(3, K))
    (hM : (Bs K s).map θ₁ = (Bs K t).map θ₂)
    (hcomm : ∀ x ∈ (Bs K s.rev).map θ₁, ∀ y ∈ (Bs K t.rev).map θ₂, x * y = y * x) :
    (Ds K s).map θ₁ = (Ds K t).map θ₂ := by
  have hflip : ∀ θ : SL(3, K) →* X, θ.ker ≤ Subgroup.center SL(3, K) →
      (θ.comp (MulAut.conj (swapSL : SL(3, K))).toMonoidHom).ker ≤ Subgroup.center SL(3, K) :=
    fun θ h => ker_comp_mulEquiv_le_center h _
  fin_cases s <;> fin_cases t
  ·
    have := torus_agree hK (hflip θ₁ h₁) h₂
      (by rw [show B23 K = Bs K 1 from rfl, map_flip_Bs]; exact hM)
      (by
        intro x hx y hy
        rw [show B12 K = Bs K 0 from rfl, map_flip_Bs] at hx
        exact hcomm x hx y hy)
    rw [show D23 K = Ds K 1 from rfl, map_flip_Ds] at this
    exact this
  ·
    exact (torus_agree hK h₂ h₁ hM.symm (fun x hx y hy => (hcomm y hy x hx).symm)).symm
  ·
    exact torus_agree hK h₁ h₂ hM hcomm
  ·
    have := torus_agree hK h₁ (hflip θ₂ h₂)
      (by rw [show B12 K = Bs K 0 from rfl, map_flip_Bs]; exact hM)
      (by
        intro x hx y hy
        rw [show B23 K = Bs K 1 from rfl, map_flip_Bs] at hy
        exact hcomm x hx y hy)
    rw [show D12 K = Ds K 0 from rfl, map_flip_Ds] at this
    exact this

end TorusAgree

section Extend

variable {K : Type} [Field K] [Finite K]

theorem exists_extend_D (hK : 4 ≤ Nat.card K) (α : SL(2, K) ≃* SL(2, K))
    (hα : (diagTorus2 K).map α.toMonoidHom ≤ diagTorus2 K) :
    ∃ β : SL(3, K) ≃* SL(3, K),
      (∀ A, β (blockSL K 3 2 0 (by omega) A) = blockSL K 3 2 0 (by omega) (α A)) ∧
        (B23 K).map β.toMonoidHom = B23 K ∧ (D23 K).map β.toMonoidHom = D23 K := by
  obtain ⟨β, hβ0, hβ1⟩ := exists_extend hK α hα
  refine ⟨β, hβ0, hβ1, ?_⟩
  obtain ⟨s₀, hs₀⟩ := exists_unit_ne_one (K := K) (by omega)
  obtain ⟨s', hs'⟩ : α (torusHom K s₀) ∈ diagTorus2 K := hα ⟨_, ⟨s₀, rfl⟩, rfl⟩
  have hs'1 : s' ≠ 1 := by
    rintro rfl
    apply hs₀
    apply torusHom_injective
    apply α.injective
    rw [← hs', map_one, map_one]
  have hle : (D23 K).map β.toMonoidHom ≤ D23 K := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨A, hA⟩ : β z ∈ B23 K := hβ1 ▸ ⟨z, D23_le_B23 hz, rfl⟩
    have hw : β (blockSL K 3 2 0 (by omega) (torusHom K s₀)) =
        blockSL K 3 2 0 (by omega) (torusHom K s') := by rw [hβ0, hs']
    have hcomm : blockSL K 3 2 1 (by omega) A * blockSL K 3 2 0 (by omega) (torusHom K s') =
        blockSL K 3 2 0 (by omega) (torusHom K s') * blockSL K 3 2 1 (by omega) A := by
      rw [hA, ← hw, ← map_mul, ← map_mul]
      exact congrArg β
        (D12_D23_comm (mem_D12_iff.mpr ⟨s₀, rfl⟩) hz).symm
    exact ⟨A, mem_diagTorus2_of_commute_one hs'1 hcomm, hA⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective β.injective])

theorem exists_extend_side (hK : 4 ≤ Nat.card K) (s : Fin 2) (α : SL(2, K) ≃* SL(2, K))
    (hα : (diagTorus2 K).map α.toMonoidHom ≤ diagTorus2 K) :
    ∃ β : SL(3, K) ≃* SL(3, K), (∀ A, β (blk K s A) = blk K s (α A)) ∧
      (Bs K s.rev).map β.toMonoidHom = Bs K s.rev ∧
        (Ds K s.rev).map β.toMonoidHom = Ds K s.rev := by
  fin_cases s
  · exact exists_extend_D hK α hα
  · let cr : SL(2, K) ≃* SL(2, K) := MulAut.conj rotSL
    let sw : SL(3, K) ≃* SL(3, K) := MulAut.conj swapSL
    have hcr : ∀ d ∈ diagTorus2 K, cr.symm d ∈ diagTorus2 K := by
      intro d hd
      have hd' : d ∈ (diagTorus2 K).map cr.toMonoidHom := by
        rw [show cr.toMonoidHom = (MulAut.conj (rotSL : SL(2, K))).toMonoidHom from rfl,
          map_conj_rotSL_diagTorus2]
        exact hd
      obtain ⟨e, he, hed⟩ := hd'
      have : cr.symm d = e := by rw [← hed]; exact cr.symm_apply_apply e
      rwa [this]
    have hcr' : ∀ d ∈ diagTorus2 K, cr d ∈ diagTorus2 K := by
      intro d hd
      rw [← map_conj_rotSL_diagTorus2 (K := K)]
      exact ⟨d, hd, rfl⟩
    let α₀ : SL(2, K) ≃* SL(2, K) := cr.symm.trans (α.trans cr.symm)
    have hα₀ : (diagTorus2 K).map α₀.toMonoidHom ≤ diagTorus2 K := by
      rintro _ ⟨d, hd, rfl⟩
      exact hcr _ (hα ⟨_, hcr d hd, rfl⟩)
    obtain ⟨β₀, hβ0, hβ1, hβD⟩ := exists_extend_D hK α₀ hα₀
    have hsw2 : ∀ x : SL(3, K), sw (sw x) = x := by
      intro x
      change swapSL * (swapSL * x * swapSL⁻¹) * swapSL⁻¹ = x
      have h1 : swapSL * (swapSL : SL(3, K)) = 1 := by
        have h := swapSL_inv (K := K)
        calc swapSL * (swapSL : SL(3, K)) = swapSL * swapSL⁻¹ := by rw [h]
          _ = 1 := mul_inv_cancel _
      calc swapSL * (swapSL * x * swapSL⁻¹) * swapSL⁻¹
          = (swapSL * swapSL) * x * (swapSL⁻¹ * swapSL⁻¹) := by group
        _ = x := by
          rw [h1, swapSL_inv, h1]
          simp
    let β₁ : SL(3, K) ≃* SL(3, K) := sw.trans (β₀.trans sw)
    have hblk : ∀ (u : Fin 2) (A : SL(2, K)), sw (blk K u A) = blk K u.rev (cr A) := fun u A =>
      swap_blk u A
    refine ⟨β₁, fun A => ?_, ?_, ?_⟩
    · change sw (β₀ (sw (blk K 1 A))) = blk K 1 (α A)
      rw [hblk 1 A]
      change sw (β₀ (blk K 0 (cr A))) = _
      rw [show blk K 0 (cr A) = blockSL K 3 2 0 (by omega) (cr A) from rfl, hβ0]
      change sw (blk K 0 (α₀ (cr A))) = _
      rw [hblk 0]
      have : cr (α₀ (cr A)) = α A := by
        change cr (cr.symm (α (cr.symm (cr A)))) = α A
        rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
      change blk K 1 (cr (α₀ (cr A))) = _
      rw [this]
    · have hmap : ∀ H : Subgroup SL(3, K), H.map β₁.toMonoidHom =
          ((H.map sw.toMonoidHom).map β₀.toMonoidHom).map sw.toMonoidHom := by
        intro H
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      have e0 : Fin.rev (0 : Fin 2) = 1 := rfl
      have e1 : Fin.rev (1 : Fin 2) = 0 := rfl
      show (Bs K 0).map β₁.toMonoidHom = Bs K 0
      rw [hmap, show sw.toMonoidHom = (MulAut.conj (swapSL : SL(3, K))).toMonoidHom from rfl,
        map_conj_swapSL_Bs 0, e0, show Bs K 1 = B23 K from rfl, hβ1,
        show B23 K = Bs K 1 from rfl, map_conj_swapSL_Bs 1, e1]
    · have hmap : ∀ H : Subgroup SL(3, K), H.map β₁.toMonoidHom =
          ((H.map sw.toMonoidHom).map β₀.toMonoidHom).map sw.toMonoidHom := by
        intro H
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      have e0 : Fin.rev (0 : Fin 2) = 1 := rfl
      have e1 : Fin.rev (1 : Fin 2) = 0 := rfl
      show (Ds K 0).map β₁.toMonoidHom = Ds K 0
      rw [hmap, show sw.toMonoidHom = (MulAut.conj (swapSL : SL(3, K))).toMonoidHom from rfl,
        map_conj_swapSL_Ds 0, e0, show Ds K 1 = D23 K from rfl, hβD,
        show D23 K = Ds K 1 from rfl, map_conj_swapSL_Ds 1, e1]

end Extend

section Adjust

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem exists_adjust_side (hK : 4 ≤ Nat.card K) (s : Fin 2) {θ₀ : SL(3, K) →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, K)) {ρ : SL(2, K) →* X} (hρ : Function.Injective ρ)
    (hrange : ρ.range = (Bs K s).map θ₀) (htor : (diagTorus2 K).map ρ = (Ds K s).map θ₀) :
    ∃ θ' : SL(3, K) →* X, θ'.ker ≤ Subgroup.center SL(3, K) ∧ θ'.comp (blk K s) = ρ ∧
      (Bs K s.rev).map θ' = (Bs K s.rev).map θ₀ ∧ (Ds K s.rev).map θ' = (Ds K s.rev).map θ₀ := by
  have hm : Function.Injective (θ₀.comp (blk K s)) := comp_blk_injective hθ₀ s
  have hrr : ρ.range = (θ₀.comp (blk K s)).range := by rw [hrange, map_Bs]
  let α : SL(2, K) ≃* SL(2, K) :=
    (MonoidHom.ofInjective hρ).trans
      ((MulEquiv.subgroupCongr hrr).trans (MonoidHom.ofInjective hm).symm)
  have hα : ∀ A, θ₀ (blk K s (α A)) = ρ A := by
    intro A
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hm).apply_symm_apply
      (MulEquiv.subgroupCongr hrr (MonoidHom.ofInjective hρ A)))
    exact h
  have hαD : (diagTorus2 K).map α.toMonoidHom ≤ diagTorus2 K := by
    rintro _ ⟨d, hd, rfl⟩
    have hmem : ρ d ∈ (diagTorus2 K).map (θ₀.comp (blk K s)) := by
      rw [← map_Ds, ← htor]
      exact ⟨d, hd, rfl⟩
    obtain ⟨d', hd', hd'eq⟩ := hmem
    have hαd : α d = d' := hm ((hα d).trans hd'eq.symm)
    simpa [hαd] using hd'
  obtain ⟨β, hβs, hβB, hβD⟩ := exists_extend_side hK s α hαD
  refine ⟨θ₀.comp β.toMonoidHom, ker_comp_mulEquiv_le_center hθ₀ β, ?_, ?_, ?_⟩
  · refine MonoidHom.ext fun A => ?_
    show θ₀ (β (blk K s A)) = ρ A
    rw [hβs, hα]
  · rw [map_comp_mulEquiv, hβB]
  · rw [map_comp_mulEquiv, hβD]

end Adjust

end CFSG.ClassicalInvolution.WeakCT
