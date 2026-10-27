module

public import CFSG.GH74.GLS.Bg.Pu5.L295Statements
public import CFSG.GH74.GLS.Bg.Pu5.ZStruct

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G]

theorem IsFour.mul_comm' {U : Subgroup G} (hU : IsFour U) {a b : G} (ha : a ∈ U) (hb : b ∈ U) :
    a * b = b * a := by
  have := hU.1
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥U)).comm (⟨a, ha⟩ : U) ⟨b, hb⟩)

theorem IsFour.mul_self' {U : Subgroup G} (hU : IsFour U) {a : G} (ha : a ∈ U) :
    a * a = 1 := by
  have := hU.1
  rw [← pow_two]
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha

theorem IsFour.orderOf_eq_two {U : Subgroup G} (hU : IsFour U) {a : G} (ha : a ∈ U) (h1 : a ≠ 1) :
    orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hU.mul_self' ha) h1

theorem IsFour.eq_enum {U : Subgroup G} (hU : IsFour U) {z w : G} (hz : z ∈ U) (hw : w ∈ U)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z ≠ w) : ∀ u ∈ U, u = 1 ∨ u = z ∨ u = w ∨ u = z * w := by
  classical
  have hzz := hU.mul_self' hz
  have hww := hU.mul_self' hw
  have h1 : (1 : G) ≠ z := hz1.symm
  have h2 : (1 : G) ≠ w := hw1.symm
  have h3 : (1 : G) ≠ z * w := by
    intro h
    apply hzw
    have : z = w⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hww)
  have h4 : z ≠ z * w := by
    intro h
    apply hw1
    have := mul_left_cancel (a := z) (b := 1) (c := w) (by rw [mul_one]; exact h)
    exact this.symm
  have h5 : w ≠ z * w := by
    intro h
    apply hz1
    exact mul_right_cancel (a := z) (b := w) (c := 1) (by rw [one_mul]; exact h.symm)
  have hsub : ({1, z, w, z * w} : Set G) ⊆ (U : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem U
    · exact hz
    · exact hw
    · exact mul_mem hz hw
  have hcard : ({1, z, w, z * w} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3]),
      Set.ncard_insert_of_notMem (by simp [hzw, h4]),
      Set.ncard_insert_of_notMem (by simp [h5]), Set.ncard_singleton]
  have hU4 : (U : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hU.2
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hU4])
    (Set.finite_of_ncard_ne_zero (by rw [hU4]; norm_num))
  intro u hu
  have : u ∈ ({1, z, w, z * w} : Set G) := by rw [heq]; exact hu
  simpa using this

section Fin

variable [Finite G] {z t : G} {S K U : Subgroup G}

theorem Cfg295.mem_cent_z (h : Cfg295 G z t S K U) {a : G} (ha : a ∈ U) :
    a ∈ centralizer ({z} : Set G) := by
  have h1 := (Subgroup.mem_inf.1 (h.hUle ha)).1
  have h2 := Subgroup.mem_centralizer_iff.1 h1 z (by simp)
  exact Subgroup.mem_centralizer_singleton_iff.2 h2.symm

theorem Cfg295.mem_cent_t (h : Cfg295 G z t S K U) {a : G} (ha : a ∈ U) :
    a ∈ centralizer ({t} : Set G) := by
  have h1 := (Subgroup.mem_inf.1 (h.hUle ha)).1
  have h2 := Subgroup.mem_centralizer_iff.1 h1 t (by simp)
  exact Subgroup.mem_centralizer_singleton_iff.2 h2.symm

theorem Cfg295.mem_cSec (h : Cfg295 G z t S K U) {a : G} (ha : a ∈ U) : a ∈ cSec K :=
  (Subgroup.mem_inf.1 (h.hUle ha)).2

theorem p0_of (hLP : L292LP) (h44 : II4_44) (hquat : II4_4_quat) : P0S := by
  intro G _ _ z t S K U h u hu hu2
  have hG := h.cfg.simple
  have hgen := h.cfg.gen4
  have h3 := h.cfg.rank
  have hz2 : ∃ n : ℕ, z ^ (2 ^ n) = 1 := exists_two_pow_eq_one_of_orderOf h.cfg.hz
  have hzu : z ∈ centralizer ({u} : Set G) := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (h.mem_cent_z hu)
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  obtain ⟨w, hwSK, hw2⟩ := exists_involution_inf hquat hG h.hK h.cfg.sylow
  have hwU : w ∈ U := h.hzi w hwSK hw2
  by_cases hzw : z = w
  · have hzK : z ∈ zStar K := by
      rw [hzw]
      exact mem_zStar_of_involution h44 hG h.hK hwSK.2 hw2
    exact hLP G hG h3 z u K h.hK hu2 (h.mem_cent_z hu) (h.mem_cSec hu) z hzK hz2 hzu
  · have hz1 : z ≠ 1 := fun h1 => by
      have := h.cfg.hz
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    have hw1 : w ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hw2
      exact absurd hw2 (by norm_num)
    have hall : ∀ K'', IsRigidRankOneComp z K'' → u ∈ cSec K'' := by
      intro K'' hK''
      have hz'' : z ∈ cSec K'' :=
        mem_cSec_of_mem_zStar h44 hquat hG hgen (self_mem_zStar_rigidProduct h.cfg.hzK) hz2 hK''
      have hw'' : w ∈ cSec K'' := by
        by_cases hKK : K = K''
        · rw [← hKK]
          exact rr_inv_mem_cSec h44 hG h.hK hwSK.2 hw2
        · exact le_cSec_of_ne (rr_pcomp h.hK) (rr_pcomp hK'') hKK hwSK.2
      rcases h.hU.eq_enum h.hzU hwU hz1 hw1 hzw u hu with h1 | h1 | h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact hz''
      · rw [h1]; exact hw''
      · rw [h1]; exact mul_mem hz'' hw''
    exact lpFull hLP h44 hquat hG hgen h3 hu2 (h.mem_cent_z hu) hall
      (self_mem_zStar_rigidProduct h.cfg.hzK) hz2 hzu

end Fin

end CFSG.GH74.GLS.Bg.Pu5
