module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidChar

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Factor

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit hQ in
theorem oKappaGL_mem_oXt {Y : GL ι₂ K} (hY : Y ∈ StatedOmega ⇑Q₂) :
    oKappaGL oe Y ∈ oXt oe Q₂ :=
  mem_sup_right (mem_sup_right ⟨Y, hY, rfl⟩)

omit hQ [CharP K 2] in
theorem eBlk_oKappaGL_mul_oRhoTwoGL (Y : GL ι₂ K) (A : SL(2, K)) :
    eBlk oe ((oKappaGL oe Y * oRhoTwoGL oe A : GL ι K) : Matrix ι ι K) =
      (A : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, coe_oKappaGL, coe_oRhoTwoGL, oblk_mul, Matrix.mul_one, Matrix.one_mul,
    eBlk_oblk]
  funext s t
  rw [rhoTwoMat_apply, fromBlocks_apply₁₁]

theorem eBlk_beta_oKappaGL_eq_one (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hsimpSL : IsSimpleGroup SL(2, K)) (hsimp : IsSimpleGroup ↥(StatedOmega ⇑Q₂))
    (hcard : Nat.card ↥(StatedOmega ⇑Q₂) ≠ Nat.card SL(2, K)) (β : MulAut ↥(oXt oe Q₂))
    (hβL : ((oL₀ oe Q₂).subgroupOf (oXt oe Q₂)).map β.toMonoidHom =
      (oL₀ oe Q₂).subgroupOf (oXt oe Q₂))
    {Y : GL ι₂ K} (hY : Y ∈ StatedOmega ⇑Q₂) :
    eBlk oe (((β ⟨oKappaGL oe Y, oKappaGL_mem_oXt hY⟩ : ↥(oXt oe Q₂)) : GL ι K) :
      Matrix ι ι K) = 1 := by
  set κX : ↥(StatedOmega ⇑Q₂) →* ↥(oXt oe Q₂) :=
    ((oKappaGL oe).comp (StatedOmega ⇑Q₂).subtype).codRestrict _ fun Z => oKappaGL_mem_oXt Z.2
  set θE : ↥(oXt oe Q₂) →* GL (Fin 2) K :=
    (eBlkHom K oe).toHomUnits.comp (Subgroup.inclusion (oXt_le_cenM₀ oe Q₂))
  have hθEv : ∀ g : ↥(oXt oe Q₂), ((θE g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      eBlk oe (((g : ↥(oXt oe Q₂)) : GL ι K) : Matrix ι ι K) := fun g => rfl
  set ε : ↥(StatedOmega ⇑Q₂) →* GL (Fin 2) K := θE.comp (β.toMonoidHom.comp κX)
  have hεv : ∀ Z : ↥(StatedOmega ⇑Q₂), ε Z = θE (β (κX Z)) := fun Z => rfl
  have hdet : ∀ Z : ↥(StatedOmega ⇑Q₂),
      ((ε Z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := fun Z => by
    rw [hεv, hθEv]
    have hm := (β (κX Z)).2
    exact det_eBlk hQ (commute_oN₀_of_mem (oXt_le_cenM₀ oe Q₂ hm))
      (quad_mulVec_of_mem_statedOmega (hle hm))
  set E : Subgroup SL(2, K) := ε.range.comap Matrix.SpecialLinearGroup.toGL with hE
  have hEε : ∀ Z, ∃ A ∈ E, Matrix.SpecialLinearGroup.toGL A = ε Z := fun Z =>
    ⟨⟨_, hdet Z⟩, ⟨Z, Units.ext rfl⟩, Units.ext rfl⟩
  have hθEρ : ∀ (A : SL(2, K)) (hA : oRhoTwoGL oe A ∈ oXt oe Q₂),
      θE ⟨_, hA⟩ = Matrix.SpecialLinearGroup.toGL A := fun A hA => by
    apply Units.ext
    rw [hθEv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    show eBlk oe ((oRhoTwoGL oe A : GL ι K) : Matrix ι ι K) = (A : Matrix (Fin 2) (Fin 2) K)
    rw [coe_oRhoTwoGL, eBlk_oblk]
    funext s t
    rw [rhoTwoMat_apply, fromBlocks_apply₁₁]
  have hEn : E.Normal := by
    refine ⟨fun B hB A => ?_⟩
    obtain ⟨Z, hZ⟩ := hB
    have hAX : oRhoTwoGL oe A ∈ oXt oe Q₂ := mem_sup_right (mem_sup_left ⟨A, rfl⟩)
    have hA : (⟨_, hAX⟩ : ↥(oXt oe Q₂)) ∈ (oL₀ oe Q₂).subgroupOf (oXt oe Q₂) :=
      mem_sup_left ⟨A, rfl⟩
    rw [← hβL] at hA
    obtain ⟨l, hl, hlA⟩ := hA
    have hl2 : (l : GL ι K) ∈ oL₀ oe Q₂ := hl
    obtain ⟨Y₁, hY₁, A₁, hl'⟩ := mem_oL₀_iff.mp hl2
    set Z'' : ↥(StatedOmega ⇑Q₂) := ⟨Y₁ * (Z : GL ι₂ K) * Y₁⁻¹,
      mul_mem (mul_mem hY₁ Z.2) (inv_mem hY₁)⟩
    have hconj : κX Z'' = l * κX Z * l⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hl']
      change oKappaGL oe (Y₁ * (Z : GL ι₂ K) * Y₁⁻¹) = oKappaGL oe Y₁ * oRhoTwoGL oe A₁ *
        oKappaGL oe (Z : GL ι₂ K) * (oKappaGL oe Y₁ * oRhoTwoGL oe A₁)⁻¹
      have hc := (commute_oKappaGL_oRhoTwoGL (oe := oe) (Z : GL ι₂ K) A₁).eq
      rw [map_mul, map_mul, map_inv, _root_.mul_inv_rev]
      calc oKappaGL oe Y₁ * oKappaGL oe ↑Z * (oKappaGL oe Y₁)⁻¹ =
          oKappaGL oe Y₁ * (oKappaGL oe ↑Z * oRhoTwoGL oe A₁) * (oRhoTwoGL oe A₁)⁻¹ *
            (oKappaGL oe Y₁)⁻¹ := by group
        _ = _ := by rw [hc]; group
    refine ⟨Z'', ?_⟩
    have hlA' : β l = ⟨_, hAX⟩ := hlA
    rw [hεv, hconj]
    simp only [map_mul, map_inv, hlA', hθEρ A hAX]
    rw [← hεv, hZ]
  have := hsimpSL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal E with hbot | htop
  ·
    obtain ⟨A, hA, hAε⟩ := hEε ⟨Y, hY⟩
    rw [hbot, mem_bot] at hA
    have h1 := congrArg Units.val hAε
    rw [hA, map_one, Units.val_one] at h1
    rw [hεv, hθEv] at h1
    exact h1.symm
  ·
    exfalso
    have := hsimp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ε.ker with hk | hk
    · have hinjε : Function.Injective ε := (MonoidHom.ker_eq_bot_iff ε).mp hk
      have hr : ε.range = (Matrix.SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K).range := by
        apply le_antisymm
        · rintro _ ⟨Z, rfl⟩
          obtain ⟨A, -, hA⟩ := hEε Z
          exact ⟨A, hA⟩
        · rintro _ ⟨A, rfl⟩
          have hA : A ∈ E := htop ▸ mem_top A
          exact hA
      apply hcard
      rw [Nat.card_congr (MonoidHom.ofInjective hinjε).toEquiv, hr,
        ← Nat.card_congr (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).toEquiv]
    · have h1 : ∀ A : SL(2, K), A = 1 := fun A => by
        have hA : A ∈ E := htop ▸ mem_top A
        obtain ⟨Z, hZ⟩ := hA
        have hZ1 : ε Z = 1 := by
          have : Z ∈ ε.ker := hk ▸ mem_top Z
          exact this
        apply Matrix.SpecialLinearGroup.toGL_injective
        rw [← hZ, hZ1, map_one]
      have h2 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) (h1 (slTr 1))
      simp [slTr] at h2

theorem exists_beta_oKappaGL (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hsimpSL : IsSimpleGroup SL(2, K)) (hsimp : IsSimpleGroup ↥(StatedOmega ⇑Q₂))
    (hcard : Nat.card ↥(StatedOmega ⇑Q₂) ≠ Nat.card SL(2, K)) (β : MulAut ↥(oXt oe Q₂))
    (hβL : ((oL₀ oe Q₂).subgroupOf (oXt oe Q₂)).map β.toMonoidHom =
      (oL₀ oe Q₂).subgroupOf (oXt oe Q₂))
    {Y : GL ι₂ K} (hY : Y ∈ StatedOmega ⇑Q₂) :
    ∃ Y' ∈ StatedOmega ⇑Q₂, ((β ⟨oKappaGL oe Y, oKappaGL_mem_oXt hY⟩ : ↥(oXt oe Q₂)) :
      GL ι K) = oKappaGL oe Y' := by
  have he := eBlk_beta_oKappaGL_eq_one hQ hle hsimpSL hsimp hcard β hβL hY
  have hL : β ⟨oKappaGL oe Y, oKappaGL_mem_oXt hY⟩ ∈ (oL₀ oe Q₂).subgroupOf (oXt oe Q₂) := by
    rw [← hβL]
    exact ⟨_, mem_sup_right ⟨Y, hY, rfl⟩, rfl⟩
  obtain ⟨Y', hY', A', hA'⟩ := mem_oL₀_iff.mp hL
  have hA'' : ((β ⟨oKappaGL oe Y, oKappaGL_mem_oXt hY⟩ : ↥(oXt oe Q₂)) : GL ι K) =
      oKappaGL oe Y' * oRhoTwoGL oe A' := hA'
  refine ⟨Y', hY', ?_⟩
  rw [hA''] at he ⊢
  rw [eBlk_oKappaGL_mul_oRhoTwoGL] at he
  have hA1 : A' = 1 := Subtype.ext he
  rw [hA1, map_one, mul_one]

end Factor

end CFSG.ComponentClassification.RankTwoClassical.ORigid
