module

public import CFSG.Foundations.MaxOrderThompsonDefs
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG
open scoped commutatorElement

section Act

variable {A : Type*} [Group A] (J : Subgroup A)

@[expose] noncomputable def actJ : ↥(normalizer (J : Set A)) →* MulAut (↥J ⧸ center ↥J) where
  toFun n := QuotientGroup.congr (center ↥J) (center ↥J) (J.normalizerMonoidHom n)
    (Subgroup.map_center_eq _)
  map_one' := by
    ext w
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
    show (QuotientGroup.mk (J.normalizerMonoidHom 1 j) : ↥J ⧸ center ↥J) = _
    rw [map_one]
    rfl
  map_mul' n m := by
    ext w
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
    show (QuotientGroup.mk (J.normalizerMonoidHom (n * m) j) : ↥J ⧸ center ↥J) = _
    rw [map_mul]
    rfl

theorem actJ_mk (n : ↥(normalizer (J : Set A))) (j : ↥J) :
    actJ J n (QuotientGroup.mk j) = QuotientGroup.mk (J.normalizerMonoidHom n j) := rfl

theorem actJ_of_mem {j : A} (hj : j ∈ J) :
    actJ J ⟨j, Subgroup.le_normalizer hj⟩ = MulAut.conj (QuotientGroup.mk (⟨j, hj⟩ : ↥J)) := by
  ext w
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
  rw [actJ_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

theorem mem_centralizer_of_actJ_eq_one (hJ : Group.IsPerfect ↥J)
    {n : ↥(normalizer (J : Set A))} (hn : actJ J n = 1) : (n : A) ∈ centralizer (J : Set A) := by
  set α : MulAut ↥J := J.normalizerMonoidHom n with hα
  have hcen : ∀ j : ↥J, j⁻¹ * α j ∈ center ↥J := by
    intro j
    have h1 := congrArg (fun φ : MulAut (↥J ⧸ center ↥J) => φ (QuotientGroup.mk j)) hn
    simp only [MulAut.one_apply] at h1
    rw [actJ_mk, QuotientGroup.eq] at h1
    have h2 := (center ↥J).inv_mem h1
    simpa using h2
  have hfix : ∀ a b : ↥J, α ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨u, hu⟩ : ∃ u ∈ center ↥J, α a = a * u := ⟨a⁻¹ * α a, hcen a, by group⟩
    obtain ⟨v, hv⟩ : ∃ v ∈ center ↥J, α b = b * v := ⟨b⁻¹ * α b, hcen b, by group⟩
    obtain ⟨hu, hau⟩ := hu
    obtain ⟨hv, hbv⟩ := hv
    rw [map_commutatorElement, hau, hbv]
    have hu' := Subgroup.mem_center_iff.mp hu
    have hv' := Subgroup.mem_center_iff.mp hv
    simp only [commutatorElement_def]
    calc a * u * (b * v) * (a * u)⁻¹ * (b * v)⁻¹
        = a * u * b * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by
        rw [show a * u * b * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ =
          a * (u * b) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ by group, ← hu' b]
        rw [show a * (b * u) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ =
          a * b * (u * v * u⁻¹) * a⁻¹ * v⁻¹ * b⁻¹ by group]
        rw [show u * v * u⁻¹ = v by rw [hv' u]; group]
        rw [show a * b * v * a⁻¹ * v⁻¹ * b⁻¹ = a * b * (v * a⁻¹) * v⁻¹ * b⁻¹ by group,
          ← hv' a⁻¹]
        group
  have htop : ∀ j : ↥J, α j = j := by
    have hle : ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ ≤
        { carrier := {j | α j = j}
          one_mem' := map_one α
          mul_mem' := fun {x y} hx hy => by
            simp only [Set.mem_ofPred_eq] at hx hy ⊢
            rw [map_mul, hx, hy]
          inv_mem' := fun {x} hx => by
            simp only [Set.mem_ofPred_eq] at hx ⊢
            rw [map_inv, hx] } := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      exact hfix a b
    have hc := Group.isPerfect_def.mp hJ
    rw [commutator_def] at hc
    rw [hc] at hle
    intro j
    exact hle (Subgroup.mem_top j)
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 := htop ⟨j, hj⟩
  have h2 : (n : A) * j * (n : A)⁻¹ = j := congrArg Subtype.val h1
  calc j * n = (n : A) * j * (n : A)⁻¹ * n := by rw [h2]
    _ = n * j := by group

end Act

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
