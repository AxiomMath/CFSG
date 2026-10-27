module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G]

theorem card_le_card_centralizer_mul_card_of_comm_mem [Finite G] {H A : Subgroup G} {x : G}
    (h : ∀ w ∈ H, w * x * w⁻¹ * x⁻¹ ∈ A) :
    Nat.card H ≤ Nat.card ((centralizer ({x} : Set G)).subgroupOf H) * Nat.card A := by
  classical
  set C : Subgroup H := (centralizer ({x} : Set G)).subgroupOf H with hC
  rw [← C.card_mul_index]
  refine Nat.mul_le_mul_left _ ?_
  rw [Subgroup.index]
  let f : H ⧸ C → A := Quotient.lift
    (fun w : H => (⟨(w : G) * x * (w : G)⁻¹ * x⁻¹, h w w.2⟩ : A)) (by
      intro w w' hww'
      have hmem : w⁻¹ * w' ∈ C := QuotientGroup.leftRel_apply.mp hww'
      rw [hC, mem_subgroupOf, mem_centralizer_iff] at hmem
      have hc := hmem x (Set.mem_singleton x)
      simp only [coe_mul, coe_inv] at hc
      apply Subtype.ext
      have e : (w' : G) * x * (w' : G)⁻¹ = (w : G) * x * (w : G)⁻¹ := by
        calc (w' : G) * x * (w' : G)⁻¹ =
              (w : G) * (((w : G)⁻¹ * (w' : G)) * x) * ((w : G)⁻¹ * (w' : G))⁻¹ * (w : G)⁻¹ := by
                group
          _ = (w : G) * (x * ((w : G)⁻¹ * (w' : G))) * ((w : G)⁻¹ * (w' : G))⁻¹ * (w : G)⁻¹ := by
                rw [hc]
          _ = (w : G) * x * (w : G)⁻¹ := by group
      show (w : G) * x * (w : G)⁻¹ * x⁻¹ = (w' : G) * x * (w' : G)⁻¹ * x⁻¹
      rw [e])
  have hf : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H w => ?_
    induction b using QuotientGroup.induction_on with | H w' => ?_
    have e : (w : G) * x * (w : G)⁻¹ * x⁻¹ = (w' : G) * x * (w' : G)⁻¹ * x⁻¹ :=
      congrArg Subtype.val hab
    apply QuotientGroup.eq.mpr
    rw [hC, mem_subgroupOf, mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    simp only [coe_mul, coe_inv]
    have e2 : (w : G) * x * (w : G)⁻¹ = (w' : G) * x * (w' : G)⁻¹ := mul_right_cancel e
    calc x * ((w : G)⁻¹ * (w' : G)) = (w : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * (w' : G) := by group
      _ = (w : G)⁻¹ * ((w' : G) * x * (w' : G)⁻¹) * (w' : G) := by rw [e2]
      _ = (w : G)⁻¹ * (w' : G) * x := by group
  exact Nat.card_le_card_of_injective f hf

theorem not_conj_of_card_lt [Finite G] {t x : G} {m : ℕ}
    (ht : ∀ P : Subgroup G, P ≤ centralizer ({t} : Set G) → IsPGroup 2 P → Nat.card P ≤ m)
    {P : Subgroup G} (hP2 : IsPGroup 2 P) (hPx : P ≤ centralizer ({x} : Set G))
    (hcard : m < Nat.card P) (g : G) : g * t * g⁻¹ ≠ x := by
  rintro rfl
  have hle : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_iff]
    rintro y rfl
    have hc := mem_centralizer_iff.mp (hPx hp) (g * y * g⁻¹) (Set.mem_singleton _)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc y * (g⁻¹ * p * g) = g⁻¹ * ((g * y * g⁻¹) * p) * g := by group
      _ = g⁻¹ * (p * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * p * g * y := by group
  have h2 : IsPGroup 2 (P.map (MulAut.conj g⁻¹).toMonoidHom) := hP2.map _
  have hcm := ht _ hle h2
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at hcm
  omega

end CFSG.SeitzReduction.RankOne
