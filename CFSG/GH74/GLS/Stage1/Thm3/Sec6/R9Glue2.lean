module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem510
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9CaseB

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem kconj_step (hlift : II4_ord4_lift) (h : Std4r1 G z S K F) {p u₁ x : G} (hp : p ∈ S ⊓ K)
    (hu₁ : u₁ ∈ S ⊓ K) (hx : x ∈ S ⊓ cSec K) (hpsq : p * p = z) (hu₁sq : u₁ * u₁ = z)
    (hxsq : x * x = z) {t : G} (htpx : t = p * x) (hzt : IsConj z t) : IsConj z (u₁ * x) := by
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  obtain ⟨k, hk, hkp⟩ := hlift G h.simple z h.orderOf_z K h.comp_isPCompIn h.comp_pRank
    h.toStd6r1.z_mem_zStar p hp.2 u₁ hu₁.2 hpsq hu₁sq
  have hKC : K ≤ centralizer ({z} : Set G) := h.comp_isPCompIn.1
  set o := ⁅k, x⁆ with ho
  have hoO : o ∈ pPrimeCoreOf 2 K := hx.2.2.2 k hk
  have hkx : k * x * k⁻¹ = o * x := by rw [ho]; simp only [commutatorElement_def]; group
  have hcomm : u₁ * x = x * u₁ := h.comm_PQ hu₁ hx
  set e := u₁ * x with he
  set t' := k * t * k⁻¹ with ht'
  have he2 : e * e = 1 := by
    calc e * e = u₁ * x * (u₁ * x) := rfl
      _ = u₁ * (x * u₁) * x := by group
      _ = u₁ * (u₁ * x) * x := by rw [← hcomm]
      _ = (u₁ * u₁) * (x * x) := by group
      _ = 1 := by rw [hu₁sq, hxsq, hz2]
  have ht2 : t' * t' = 1 := by
    have htt : t * t = 1 := by
      rw [htpx]
      have hc : p * x = x * p := h.comm_PQ hp hx
      calc p * x * (p * x) = p * (x * p) * x := by group
        _ = p * (p * x) * x := by rw [← hc]
        _ = (p * p) * (x * x) := by group
        _ = 1 := by rw [hpsq, hxsq, hz2]
    calc t' * t' = k * (t * t) * k⁻¹ := by rw [ht']; group
      _ = 1 := by rw [htt]; group
  have ht'eq : t' = u₁ * (o * x) := by
    rw [ht', htpx]
    calc k * (p * x) * k⁻¹ = (k * p * k⁻¹) * (k * x * k⁻¹) := by group
      _ = u₁ * (o * x) := by rw [hkp, hkx]
  have hzcom : ∀ w ∈ K, z * w = w * z := fun w hw =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKC hw)).symm
  have hxS : x ∈ S := hx.1
  have hprod : e * t' = x * o * x⁻¹ := by
    have hzx : z * x = x * z := h.z_cent hxS
    have hoK : o ∈ K := (TwoThin.pPrimeCoreOf_le K) hoO
    have hzo : z * o = o * z := hzcom o hoK
    have hxinv : x⁻¹ = x * z := by
      have : x * (x * z) = 1 := by rw [← mul_assoc, hxsq]; exact hz2
      exact mul_eq_one_iff_inv_eq.1 this
    calc e * t' = (u₁ * x) * (u₁ * (o * x)) := by rw [ht'eq]
      _ = u₁ * (x * u₁) * (o * x) := by group
      _ = u₁ * (u₁ * x) * (o * x) := by rw [← hcomm]
      _ = (u₁ * u₁) * (x * o * x) := by group
      _ = z * (x * o * x) := by rw [hu₁sq]
      _ = x * o * x⁻¹ := by
          rw [hxinv]
          calc z * (x * o * x) = (z * x) * o * x := by group
            _ = (x * z) * o * x := by rw [hzx]
            _ = x * (z * o) * x := by group
            _ = x * (o * z) * x := by rw [hzo]
            _ = x * o * (z * x) := by group
            _ = x * o * (x * z) := by rw [hzx]
  have hodd : Odd (orderOf (e * t')) := by
    rw [hprod]
    have hmem : x * o * x⁻¹ ∈ pPrimeCoreOf 2 K := (mem_normalizer_iff.1 hx.2.2.1 o).1 hoO
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) (Subgroup.orderOf_dvd_natCard _ hmem)
  obtain ⟨m, hm⟩ := R1.conj_of_odd_mul he2 ht2 hodd
  have hzt' : IsConj z t' := hzt.trans (isConj_iff.2 ⟨k, rfl⟩)
  exact hzt'.trans (isConj_iff.2 ⟨m, hm⟩ : IsConj e t').symm

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
