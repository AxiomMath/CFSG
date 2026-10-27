module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS1

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

section Abstract

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}
  {R B : Subgroup G} {m : ℕ}

theorem false_of_isZStar_pair (d : Cyc L Q z) (hRD : RootData L z R B m) (hm : 4 ≤ m) {y : G}
    (hy2 : orderOf y = 2) (hyL : y ∈ L) (hyC : y ∈ centralizer (R : Set G))
    (h1 : IsZStar R z) (h2 : IsZStar R (z * y)) : False := by
  obtain ⟨hz1, hc1⟩ := isZStar_iff_mem_center.1 h1
  obtain ⟨hz2, hc2⟩ := isZStar_iff_mem_center.1 h2
  have hzz := d.mul_self
  have hyy : (⟨y, hyC⟩ : ↥(centralizer (R : Set G))) =
      (⟨z, hz1⟩ : ↥(centralizer (R : Set G))) * ⟨z * y, hz2⟩ := by
    apply Subtype.ext
    show y = z * (z * y)
    rw [← mul_assoc, hzz, one_mul]
  have hw : (QuotientGroup.mk ⟨y, hyC⟩ : Sec G R) ∈ center (Sec G R) := by
    rw [hyy, QuotientGroup.mk_mul]
    exact mul_mem hc1 hc2
  have hwB : (QuotientGroup.mk ⟨y, hyC⟩ : Sec G R) ∈ secImage R B := hRD.mk_mem ⟨y, hyC⟩ hyL
  obtain ⟨eB⟩ := hRD.shape.iso
  have hcenter : center ↥(secImage R B) = ⊥ := center_eq_bot_of_alt hm eB
  have hw' : (⟨QuotientGroup.mk ⟨y, hyC⟩, hwB⟩ : ↥(secImage R B)) ∈ center ↥(secImage R B) := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hw a.1
  rw [hcenter, Subgroup.mem_bot] at hw'
  have hw1 : (QuotientGroup.mk ⟨y, hyC⟩ : Sec G R) = 1 := congrArg Subtype.val hw'
  have hO : (⟨y, hyC⟩ : ↥(centralizer (R : Set G))) ∈ CFSG.oddCore ↥(centralizer (R : Set G)) :=
    (QuotientGroup.eq_one_iff _).1 hw1
  have hodd := orderOf_odd_of_mem_oddCore hO
  rw [Subgroup.orderOf_mk, hy2] at hodd
  exact (Nat.not_odd_iff_even.2 even_two) hodd

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem false_of_zstar_common_root (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 12 ≤ n) {y g : G} (hy : y ∈ FusionSet L z)
    (hg : g * z * g⁻¹ = z * y) {S S₁ : Finset (Fin n)} (hS : S.card = 3 ∨ S.card = 4)
    (hyC : y ∈ centralizer (rootGroup e S : Set G))
    (hcomm : rootGroup (G := G) e S = conjSub g (rootGroup e S₁))
    (h1 : IsZStar (rootGroup e S) z) (h2 : IsZStar (rootGroup e S₁) z) : False := by
  have hRD := rootData_of_card_three_or_four h d hQ2 e hS (by omega)
  have h2' : IsZStar (rootGroup (G := G) e S) (z * y) := by
    have := h2.conj g
    rw [← hcomm, hg] at this
    exact this
  exact false_of_isZStar_pair d hRD (by omega) hy.2.1 hy.1 hyC h1 h2'

end Concrete

end CFSG.OddStandard.AltStdSec
