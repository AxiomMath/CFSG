module

public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.LargeExtraspecial.A2ModBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure ZSHyp (n : ℕ) (q : QuadraticForm (ZMod 2) V) (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) :
    Prop where
  four_le : 4 ≤ n
  finrank_eq : finrank (ZMod 2) V = 2 * n
  a2 : A2Mod.A2Action (DG n) q ρ
  irred : ∀ W : Submodule (ZMod 2) V, (∀ g : PG n, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤

noncomputable abbrev rs (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) : SUid frob n →* (V ≃ₗ[ZMod 2] V) :=
  ρ.comp (QuotientGroup.mk' _)

noncomputable abbrev lineA (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) (x : Fin n → K) :
    Submodule (ZMod 2) V :=
  commSpace (ρ (tq x))

variable {ρ : PG n →* (V ≃ₗ[ZMod 2] V)}

theorem rs_apply (g : SUid frob n) : rs ρ g = ρ (QuotientGroup.mk g) := rfl

theorem rs_tvU (x : Fin n → K) : rs ρ (tvU x) = ρ (tq x) := rfl

theorem add_self_V (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem sub_eq_add_V (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (add_self_V v)]

theorem apply_mem_commSpace_conj' {X : Type*} [Group X] (σ : X →* (V ≃ₗ[ZMod 2] V)) (g : X)
    {a : X} {v : V} (hv : v ∈ commSpace (σ a)) : σ g v ∈ commSpace (σ (g * a * g⁻¹)) := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hv
  refine mem_commSpace.mpr ⟨σ g y, ?_⟩
  have h1 : σ g⁻¹ (σ g y) = y := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one, id]
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, map_sub]

theorem apply_mem_commSpace_of_commute {a b : V ≃ₗ[ZMod 2] V} (hab : a * b = b * a) {v : V}
    (hv : v ∈ commSpace b) : a v ∈ commSpace b := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hv
  refine mem_commSpace.mpr ⟨a y, ?_⟩
  rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hab]

theorem apply_eq_self_of_mem_commSpace {t : V ≃ₗ[ZMod 2] V} (ht : t * t = 1) {v : V}
    (hv : v ∈ commSpace t) : t v = v := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hv
  rw [map_sub, apply_apply_of_mul_self ht, sub_eq_add_V, sub_eq_add_V, add_comm]

theorem lineA_smul {x : Fin n → K} (hx : herm frob x x = 0) {c : K} (hc : c ≠ 0) :
    lineA ρ (c • x) = lineA ρ x := by
  rw [lineA, lineA, tq, tq, tvU_smul_vec hx hc]

theorem apply_mem_lineA (g : SUid frob n) {x : Fin n → K} (hx : herm frob x x = 0) {v : V}
    (hv : v ∈ lineA ρ x) : rs ρ g v ∈ lineA ρ (g • x) := by
  have h := apply_mem_commSpace_conj' ρ (QuotientGroup.mk g) hv
  rwa [conj_tq g hx] at h

theorem map_lineA (g : SUid frob n) {x : Fin n → K} (hx : herm frob x x = 0) :
    (lineA ρ x).map (rs ρ g : V →ₗ[ZMod 2] V) = lineA ρ (g • x) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact apply_mem_lineA g hx hv
  · intro v hv
    have hgx : herm frob (g • x) (g • x) = 0 := by rw [herm_smul_smul, hx]
    have h := apply_mem_lineA g⁻¹ hgx hv
    rw [inv_smul_smul] at h
    refine ⟨rs ρ g⁻¹ v, h, ?_⟩
    change rs ρ g (rs ρ g⁻¹ v) = v
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one, id]

theorem tq_mul_self' {x : Fin n → K} (hx : herm frob x x = 0) :
    ρ (tq x) * ρ (tq x) = 1 := by
  rw [← map_mul, tq_mul_self hx, map_one]

theorem apply_eq_self_of_mem_lineA {x : Fin n → K} (hx : herm frob x x = 0) {v : V}
    (hv : v ∈ lineA ρ x) : ρ (tq x) v = v :=
  apply_eq_self_of_mem_commSpace (tq_mul_self' hx) hv

theorem apply_mem_lineA_of_perp {x y : Fin n → K} (hx : herm frob x x = 0)
    (hy : herm frob y y = 0) (hxy : herm frob x y = 0) {v : V} (hv : v ∈ lineA ρ x) :
    ρ (tq y) v ∈ lineA ρ x := by
  refine apply_mem_commSpace_of_commute ?_ hv
  rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    tvU_commute hy hx (herm_eq_zero_comm frob frob_frob hxy)]

namespace ZSHyp

variable {q : QuadraticForm (ZMod 2) V} (h : ZSHyp n q ρ)
include h

theorem three_le : 3 ≤ n := by have := h.four_le; omega

theorem nondeg : (QuadraticMap.polarBilin q).Nondegenerate := h.a2.nondegenerate

theorem q_apply (g : PG n) (v : V) : q (ρ g v) = q v := h.a2.map_apply g v

theorem polar_apply (g : PG n) (u v : V) : QuadraticMap.polar q (ρ g u) (ρ g v) =
    QuadraticMap.polar q u v := by
  simp only [QuadraticMap.polar, ← map_add, h.q_apply]

theorem isTypeA_tq {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) :
    IsTypeA q (ρ (tq x)) 2 :=
  h.a2.isTypeA (tq_mem_DG hx0 hx)

theorem finrank_lineA {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) :
    finrank (ZMod 2) (lineA ρ x) = 2 :=
  (h.isTypeA_tq hx0 hx).2.2.2.1

theorem lineA_ne_bot {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) :
    lineA ρ x ≠ ⊥ := fun hb => by
  have := h.finrank_lineA hx0 hx
  rw [hb, finrank_bot] at this
  exact absurd this (by norm_num)

theorem ker_rs {g : SUid frob n} (hg : rs ρ g = 1) :
    g ∈ Subgroup.center (SUid frob n) := by
  have h1 : (QuotientGroup.mk g : PG n) = 1 := h.a2.injective (by rw [map_one]; exact hg)
  exact (QuotientGroup.eq_one_iff g).1 h1

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
