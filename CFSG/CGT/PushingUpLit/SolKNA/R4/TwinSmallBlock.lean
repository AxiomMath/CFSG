module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallM2
public import CFSG.ClassicalInvolution.Q3.TA3FrameL4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Q3.TA3.Frame
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped MatrixGroups

theorem noQ8Fix_mono {P : Type} [Group P] {H H' : Subgroup P} (h : NoQ8Fix P H) (hle : H ≤ H') :
    NoQ8Fix P H' :=
  fun ψ hψ hfix => h ψ hψ fun a x hx => hfix a x (hle hx)


theorem twin_false_of_simple {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) {P : Type} [Group P]
    (e : ↥(genFittingFStar Y) ≃* P) (htT : t ∈ genFittingFStar Y) {u : P}
    (hu : e ⟨t, htT⟩ = u) {H : Subgroup P} [IsSimpleGroup H] [Group.IsPerfect H]
    (hHt : H ≤ Subgroup.centralizer ({u} : Set P))
    (hmax : ∀ M : Subgroup P, M ≤ Subgroup.centralizer ({u} : Set P) → ⁅M, M⁆ = M → M ≤ H)
    (hfix : NoQ8Fix P H) : False := by
  have hK : IsComponentOf H (Subgroup.centralizer ({u} : Set P)) :=
    isComponentOf_of_normal hHt (FL4.normal_of_perfect_max hHt
      (Subgroup.isPerfect_iff.mp inferInstance) hmax) FL4.isQuasisimple_of_simple
  exact twin_false_of_model h e htT hu H H hK hK (by rw [sup_idem]; exact hfix)

theorem twin_false_of_block {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) {P : Type} [Group P]
    (e : ↥(genFittingFStar Y) ≃* P) (htT : t ∈ genFittingFStar Y) {u : P}
    (hu : e ⟨t, htT⟩ = u) {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (β : SL(2, F) × SL(2, F) →* P) (hinl : Function.Injective (β.comp (MonoidHom.inl _ _)))
    (hinr : Function.Injective (β.comp (MonoidHom.inr _ _)))
    (hHt : β.range ≤ Subgroup.centralizer ({u} : Set P)) (hHp : ⁅β.range, β.range⁆ = β.range)
    (hmax : ∀ M : Subgroup P, M ≤ Subgroup.centralizer ({u} : Set P) → ⁅M, M⁆ = M →
      M ≤ β.range)
    (hfix : NoQ8Fix P β.range) : False := by
  set C := Subgroup.centralizer ({u} : Set P) with hC
  have hnH := FL4.normal_of_perfect_max hHt hHp hmax
  have hle1 : (β.comp (MonoidHom.inl _ _)).range ≤ β.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have hle2 : (β.comp (MonoidHom.inr _ _)).range ≤ β.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have hK1 : IsComponentOf (β.comp (MonoidHom.inl _ _)).range C :=
    ⟨hle1.trans hHt, IsSubnormal.step hle1 (FL4.normal_inl β) (IsSubnormal.step hHt hnH
      (IsSubnormal.refl C)), isQuasisimple_of_equiv_sl2 h4 (MonoidHom.ofInjective hinl).symm⟩
  have hK2 : IsComponentOf (β.comp (MonoidHom.inr _ _)).range C :=
    ⟨hle2.trans hHt, IsSubnormal.step hle2 (FL4.normal_inr β) (IsSubnormal.step hHt hnH
      (IsSubnormal.refl C)), isQuasisimple_of_equiv_sl2 h4 (MonoidHom.ofInjective hinr).symm⟩
  refine twin_false_of_model h e htT hu _ _ hK1 hK2 (noQ8Fix_mono hfix ?_)
  rintro _ ⟨⟨a, b⟩, rfl⟩
  have e' : β (a, b) = (β.comp (MonoidHom.inl _ _)) a * (β.comp (MonoidHom.inr _ _)) b := by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply]
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [e']
  exact mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨b, rfl⟩)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
