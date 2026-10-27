module

public import CFSG.LargeExtraspecial.AS62Conf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions
open scoped IsMulCommutative

namespace AS62

variable {G : Type} [Group G] [Finite G]

theorem perm_eq_klein : ∀ p : Equiv.Perm (Fin 5), p 0 = 0 → p * p = 1 →
    Equiv.Perm.sign p = 1 → p = 1 ∨ p = Equiv.swap 1 2 * Equiv.swap 3 4 ∨
      p = Equiv.swap 1 3 * Equiv.swap 2 4 ∨ p = Equiv.swap 1 4 * Equiv.swap 2 3 := by
  decide +kernel

namespace Label

variable {S : Setting G} {H : Subgroup G} (L : Label S H)

theorem prod_zz (hc : ConfHyp S H) : L.zz 0 * L.zz 1 * L.zz 2 * L.zz 3 * L.zz 4 = 1 := by
  set V := closure (S.zConj H) with hV
  have : IsMulCommutative V :=
    isMulCommutative_closure fun x hx y hy _ => hc.commute_zConj hx hy
  let f : Fin 5 → V := fun i => ⟨L.zz i, subset_closure (L.zz_mem i)⟩
  set w : V := ∏ i, f i with hw
  have hwH : ∀ h : H, (h : G) * (w : G) * (h : G)⁻¹ = w := by
    intro h
    let φ : V →* V :=
      { toFun := fun v => ⟨h * v * (h : G)⁻¹, conj_mem_closure_conjIn h.2 v.2⟩
        map_one' := Subtype.ext (by
          change (h : G) * 1 * (h : G)⁻¹ = 1
          group)
        map_mul' := fun x y => Subtype.ext (by
          change (h : G) * ((x : G) * y) * (h : G)⁻¹ = h * x * (h : G)⁻¹ * (h * y * (h : G)⁻¹)
          group) }
    have h1 : φ w = ∏ i, φ (f i) := map_prod φ _ _
    have h2 : ∀ i, φ (f i) = f (L.σ h i) := fun i => Subtype.ext (L.conj_zz h i)
    have h3 : ∏ i, φ (f i) = ∏ i, f i := by
      simp_rw [h2]
      exact Equiv.prod_comp (L.σ h) f
    exact congrArg Subtype.val (h1.trans h3)
  have hwC : (w : G) ∈ Asc77.centerIn S.z H := by
    refine mem_inf.mpr ⟨w.2, mem_centralizer_iff.mpr fun k hk => ?_⟩
    calc k * (w : G) = k * w * k⁻¹ * k := by group
      _ = w * k := by rw [hwH ⟨k, hk⟩]
  rw [hc.isAFive.2, mem_bot] at hwC
  have hval : (w : G) = L.zz 0 * L.zz 1 * L.zz 2 * L.zz 3 * L.zz 4 := by
    rw [hw, Fin.prod_univ_five]
    rfl
  rw [← hval, hwC]

theorem σ_mem_klein (hc : ConfHyp S H) {q : H} (hq : (q : G) ∈ S.QG) :
    L.σ q = 1 ∨ L.σ q = Equiv.swap 1 2 * Equiv.swap 3 4 ∨
      L.σ q = Equiv.swap 1 3 * Equiv.swap 2 4 ∨ L.σ q = Equiv.swap 1 4 * Equiv.swap 2 3 := by
  refine perm_eq_klein _ ((L.σ_zero_eq_zero_iff q).mpr (S.QG_le_M hq)) ?_
    (L.sign_σ hc.isAFive q)
  rw [← map_mul, L.σ_eq_one_iff hc]
  have hsq := S.sq_eq_one_or_z hq
  rw [pow_two] at hsq
  rcases hsq with h | h
  · rw [Subgroup.coe_mul, h]
    exact one_mem _
  · rw [Subgroup.coe_mul, h]
    exact subset_closure (self_mem_conjIn _ _)

theorem exists_QG_σ_one_eq (hc : ConfHyp S H) {j : Fin 5} (hj : j ≠ 0) :
    ∃ q : H, (q : G) ∈ S.QG ∧ L.σ q 1 = j := by
  obtain ⟨q, hq, hqe⟩ := hc.exists_QG_conj (L.zz_mem 1) (L.zz_ne_z (by decide)) (L.zz_mem j)
    (L.zz_ne_z hj)
  refine ⟨⟨q, hc.QG_le hq⟩, hq, L.zz_injective ?_⟩
  rw [← L.conj_zz]
  exact hqe

theorem exists_σ_eq_klein₁ (hc : ConfHyp S H) :
    ∃ q : H, (q : G) ∈ S.QG ∧ L.σ q = Equiv.swap 1 2 * Equiv.swap 3 4 := by
  obtain ⟨q, hq, h1⟩ := L.exists_QG_σ_one_eq hc (j := 2) (by decide)
  refine ⟨q, hq, ?_⟩
  rcases L.σ_mem_klein hc hq with h | h | h | h <;> rw [h] at h1 ⊢ <;>
    first | rfl | exact absurd h1 (by decide)

theorem exists_σ_eq_klein₂ (hc : ConfHyp S H) :
    ∃ q : H, (q : G) ∈ S.QG ∧ L.σ q = Equiv.swap 1 3 * Equiv.swap 2 4 := by
  obtain ⟨q, hq, h1⟩ := L.exists_QG_σ_one_eq hc (j := 3) (by decide)
  refine ⟨q, hq, ?_⟩
  rcases L.σ_mem_klein hc hq with h | h | h | h <;> rw [h] at h1 ⊢ <;>
    first | rfl | exact absurd h1 (by decide)

end Label

end AS62

end CFSG.LargeExtraspecial
