module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGLType
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
open scoped MatrixGroups

theorem Ivk93Cfg2.two_blocks {F : Type} [Field F] [Finite F] (htwo : (2 : F) ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {x : StatedProj (StatedSL n F)} {q₁ q₂ : ℕ}
    {L₁ L₂ : Subgroup (StatedProj (StatedSL n F))} (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a + b = n ∧ Nonempty (SL(a, F) ≃* ↥L₁) ∧
      Nonempty (SL(b, F) ≃* ↥L₂) := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  set φ := CatFactsL4U4.projToPGL n F with hφdef
  have hφ : Function.Injective φ := CatFactsL4U4.projToPGL_injective n
  have := projToPGL_range_normal n F
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (φ x)
  have hx2 : x ^ 2 = 1 := by rw [← h.ord, pow_orderOf_eq_one]
  have hne : Matrix.ProjGenLinGroup.mk A ≠ 1 := by
    rw [hA]
    intro h1
    exact h.ne_one (hφ (h1.trans (map_one φ).symm))
  have hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1 := by
    rw [hA, ← map_pow, hx2, map_one]
  obtain ⟨hK₁le, hK₁⟩ := isPComponent_map_of_normal φ hφ h.le₁ h.comp₁.2
  obtain ⟨hK₂le, hK₂⟩ := isPComponent_map_of_normal φ hφ h.le₂ h.comp₂.2
  rw [← hA] at hK₁ hK₂ hK₁le hK₂le
  have hMne : (L₁.map φ).subgroupOf (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _)) ≠
      (L₂.map φ).subgroupOf (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _)) := by
    intro heq
    apply h.ne
    have h1 := subgroupOf_inj.mp heq
    rw [inf_of_le_left hK₁le, inf_of_le_left hK₂le] at h1
    exact map_injective hφ h1
  obtain ⟨a, b, ha, hb, hab, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    ivk93l_pgl_two_blocks htwo hn A hne hinv hK₁ hK₂ hMne
  exact ⟨a, b, ha, hb, hab,
    ⟨e₁.trans ((Subgroup.subgroupOfEquivOfLe hK₁le).trans
      (L₁.equivMapOfInjective φ hφ).symm)⟩,
    ⟨e₂.trans ((Subgroup.subgroupOfEquivOfLe hK₂le).trans
      (L₂.equivMapOfInjective φ hφ).symm)⟩⟩

theorem Ivk93Cfg2.five_le_of_equiv_sl2 {J : Type} [Group J] [Finite J] {x : J} {q₁ q₂ : ℕ}
    {L₁ L₂ : Subgroup J} (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {F : Type} [Field F] [Finite F]
    (e : SL(2, F) ≃* ↥L₁) : 5 ≤ Nat.card F := by
  by_contra hlt
  have h1 : Nat.card ↥L₁ = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
  have h2 := h.card_ge₁
  have h3 := sl2_card_mono (show Nat.card F ≤ 4 by omega)
  norm_num at h3
  omega

theorem Ivk93Cfg2.five_le_of_equiv_sl2' {J : Type} [Group J] [Finite J] {x : J} {q₁ q₂ : ℕ}
    {L₁ L₂ : Subgroup J} (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {F : Type} [Field F] [Finite F]
    (e : SL(2, F) ≃* ↥L₂) : 5 ≤ Nat.card F :=
  h.symm.five_le_of_equiv_sl2 e

end CFSG.GH74.GLS.IVK.Proofs2
