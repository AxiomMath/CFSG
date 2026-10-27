module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open scoped IsMulCommutative

theorem aut_mem_center {G : Type*} [Group G] (φ : MulAut G) {x : G}
    (hx : x ∈ Subgroup.center G) : φ x ∈ Subgroup.center G := by
  have h := Subgroup.map_center_eq φ
  rw [← h]
  exact Subgroup.mem_map_of_mem _ hx

theorem average_fixed {G : Type*} [Group G] {E : Type*} [Group E] [Fintype E]
    (α : E →* MulAut G) (k : G) (hz : ∀ e, k⁻¹ * α e k ∈ Subgroup.center G) :
    ∃ y : G, (∀ e, α e y = y) ∧ ∃ w ∈ Subgroup.center G, y = k ^ Fintype.card E * w := by
  classical
  let z : E → ↥(Subgroup.center G) := fun e => ⟨k⁻¹ * α e k, hz e⟩
  have hzk : ∀ e, α e k = k * (z e : G) := fun e => by
    show α e k = k * (k⁻¹ * α e k)
    group
  let αZ : E → (↥(Subgroup.center G) →* ↥(Subgroup.center G)) := fun e =>
    ((α e).toMonoidHom.comp (Subgroup.center G).subtype).codRestrict (Subgroup.center G) (fun x => aut_mem_center (α e) x.2)
  have hαZ : ∀ e (x : ↥(Subgroup.center G)), ((αZ e x : ↥(Subgroup.center G)) : G) = α e (x : G) := fun e x => rfl
  have hcoc : ∀ e f, (z (e * f) : G) = (z e : G) * α e (z f : G) := by
    intro e f
    show k⁻¹ * α (e * f) k = (k⁻¹ * α e k) * α e (k⁻¹ * α f k)
    rw [map_mul, MulAut.mul_apply, map_mul, map_inv]
    group
  have hw : ∀ e, αZ e (∏ f, z f) = (z e)⁻¹ ^ Fintype.card E * ∏ f, z f := by
    intro e
    rw [map_prod]
    have h1 : ∀ f, αZ e (z f) = (z e)⁻¹ * z (e * f) := by
      intro f
      apply Subtype.ext
      rw [hαZ, Subgroup.coe_mul, Subgroup.coe_inv, hcoc e f]
      group
    rw [Finset.prod_congr rfl (fun f _ => h1 f), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft e) _ _ (fun f => rfl)
  refine ⟨k ^ Fintype.card E * ((∏ f, z f : ↥(Subgroup.center G)) : G), ?_, _, (∏ f, z f).2, rfl⟩
  intro e
  have hcomm : Commute k (z e : G) := Subgroup.mem_center_iff.1 (z e).2 k
  have hwe : α e ((∏ f, z f : ↥(Subgroup.center G)) : G) =
      (((z e : G))⁻¹) ^ Fintype.card E * ((∏ f, z f : ↥(Subgroup.center G)) : G) := by
    have h := congrArg (fun x : ↥(Subgroup.center G) => (x : G)) (hw e)
    simp only [hαZ] at h
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] at h
    exact h
  rw [map_mul, map_pow, hzk e, hwe, hcomm.mul_pow]
  have h2 : (z e : G) ^ Fintype.card E * ((z e : G)⁻¹) ^ Fintype.card E = 1 := by
    rw [inv_pow, mul_inv_cancel]
  calc k ^ Fintype.card E * (z e : G) ^ Fintype.card E *
        (((z e : G))⁻¹ ^ Fintype.card E * ((∏ f, z f : ↥(Subgroup.center G)) : G))
      = k ^ Fintype.card E * ((z e : G) ^ Fintype.card E * ((z e : G))⁻¹ ^ Fintype.card E) *
        ((∏ f, z f : ↥(Subgroup.center G)) : G) := by group
    _ = k ^ Fintype.card E * ((∏ f, z f : ↥(Subgroup.center G)) : G) := by rw [h2, mul_one]

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
