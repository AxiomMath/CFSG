module

public import CFSG.GH74.GLS.Stage1.Main.BrG2Shape
public import CFSG.GH74.GLS.Stage1.Main.BrG2Ctx

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section ShapeT

variable {X : Type} [Group X] {S A : Subgroup X} {a t y : X} {n : ℕ}

theorem shape_a_mem (h : ShapeConds S A a t y n) : a ∈ A := by
  rw [h.2.1]; exact mem_sup_left (mem_zpowers a)

theorem shape_closure_eq (h : ShapeConds S A a t y n) :
    Subgroup.closure ({a, t, y} : Set X) = S := by
  have hle := ShapeConds.le_S h
  have hS := h.2.2.2.2.2.2.2.2.2.2.2.2
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact hle.1 (shape_a_mem h)
    · exact hle.2.1
    · exact hle.2.2
  · rw [hS]
    have hat : t⁻¹ * a * t ∈ Subgroup.closure ({a, t, y} : Set X) :=
      mul_mem (mul_mem (inv_mem (subset_closure (by simp))) (subset_closure (by simp)))
        (subset_closure (by simp))
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [h.2.1]
      refine sup_le ?_ ?_
      · rw [zpowers_le]; exact subset_closure (by simp)
      · rw [zpowers_le]; exact hat
    · rw [zpowers_le]; exact subset_closure (by simp)
    · rw [zpowers_le]; exact subset_closure (by simp)

theorem shape_three_gen (h : ShapeConds S A a t y n) :
    ∃ a' t' y' : ↥S, Subgroup.closure ({a', t', y'} : Set ↥S) = ⊤ := by
  have hle := ShapeConds.le_S h
  have ha : a ∈ S := hle.1 (shape_a_mem h)
  refine ⟨⟨a, ha⟩, ⟨t, hle.2.1⟩, ⟨y, hle.2.2⟩, ?_⟩
  apply Subgroup.map_injective S.subtype_injective
  rw [MonoidHom.map_closure]
  have h1 : (S.subtype : ↥S → X) '' ({⟨a, ha⟩, ⟨t, hle.2.1⟩, ⟨y, hle.2.2⟩} : Set ↥S) = {a, t, y} := by
    simp [Set.image_insert_eq]
  rw [h1, shape_closure_eq h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem shape_card_A (h : ShapeConds S A a t y n) : Nat.card ↥A = 2 ^ (2 * n) := by
  have hD := shape_data h
  have hsemi : SemiconjBy t⁻¹ a (t⁻¹ * a * t) := (mul_inv_cancel_right (t⁻¹ * a) t).symm
  have hb_ord : orderOf (t⁻¹ * a * t) = 2 ^ n := by rw [← hsemi.orderOf_eq, h.1]
  have hN : Function.Injective hD.fN := hD.fN_injective h.1 hb_ord (disjoint_iff.2 h.2.2.1)
  have h1 : Nat.card ↥A = Nat.card (ShapeModel.ShapeN n) := by
    rw [shape_A_eq h]
    exact (Nat.card_congr (MonoidHom.ofInjective hN).toEquiv).symm
  rw [h1, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  ring

end ShapeT

section TCtx

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

noncomputable def G2Ctx.eT (hcen : Cen2 G z S) : ↥(barOf z S) ≃* ↥C.S' :=
  (barEquiv z S hcen.sylow.le (cen2_S_inf_oddCore hcen)).symm.trans C.eS

include C in
theorem G2Ctx.three_gen (hcen : Cen2 G z S) :
    ∃ a t y : ↥(barOf z S), Subgroup.closure ({a, t, y} : Set ↥(barOf z S)) = ⊤ := by
  obtain ⟨a', t', y', h⟩ := shape_three_gen C.shape
  refine ⟨(C.eT hcen).symm a', (C.eT hcen).symm t', (C.eT hcen).symm y', ?_⟩
  have h1 := MonoidHom.map_closure (C.eT hcen).symm.toMonoidHom ({a', t', y'} : Set ↥C.S')
  rw [h, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 (C.eT hcen).symm.surjective] at h1
  have himg : (((C.eT hcen).symm.toMonoidHom : ↥C.S' →* ↥(barOf z S)) : ↥C.S' → ↥(barOf z S)) ''
      ({a', t', y'} : Set ↥C.S') =
      {(C.eT hcen).symm a', (C.eT hcen).symm t', (C.eT hcen).symm y'} := by
    simp [Set.image_insert_eq]
  rw [himg] at h1
  exact h1.symm

include C in
theorem G2Ctx.exists_AT (hcen : Cen2 G z S) :
    ∃ B : Subgroup (CentralizerBar z), B ≤ barOf z S ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
      Nat.card ↥B = 2 ^ (2 * C.n) := by
  set e := C.eT hcen with he
  refine ⟨((C.A.subgroupOf C.S').map e.symm.toMonoidHom).map (barOf z S).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨u', hu', rfl⟩ := hx'
    have hcomm := ShapeConds.A_comm C.shape (u : C.Gs) hu (u' : C.Gs) hu'
    show (((e.symm u : ↥(barOf z S)) : CentralizerBar z)) * ((e.symm u' : ↥(barOf z S)) : CentralizerBar z) =
      ((e.symm u' : ↥(barOf z S)) : CentralizerBar z) * ((e.symm u : ↥(barOf z S)) : CentralizerBar z)
    have : u * u' = u' * u := Subtype.ext hcomm
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, this]
  · rw [Subgroup.card_map_of_injective (barOf z S).subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective,
      ← shape_card_A C.shape]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ShapeConds.le_S C.shape).1).toEquiv

end TCtx

end CFSG.GH74.GLS.Stage1.Main
