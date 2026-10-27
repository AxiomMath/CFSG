module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2U
public import CFSG.ClassicalInvolution.Q3.TL4S289U3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance

section Cit3


theorem tightZ2TFreeR_proved (n : ℕ) : TightZ2TFreeR 3 n := by
  intro Y _ _ R S t hL _ _ _ hD J J₂ J₃ u v hF htu L hLc hm _
  exfalso
  have ht := hL.datum.isUniqueInvolution_core
  have hB := hF.isElemAbelian hL
  have hm3 := mem_closure_three_left t u v
  have hvu : v ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hF.comm.symm
  have htv1 : t * v ≠ 1 := fun e => hF.ne_tv hL (by
    have h1 : v = t⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [h1, inv_eq_of_mul_eq_one_right ht.sq])
  have htvu : t * v ≠ u := fun e => hF.ne_mul (by
    rw [← e, ← mul_assoc, ht.sq, one_mul])
  have htvB := Subgroup.mul_mem _ hm3.1 hm3.2.2
  have htvC : t * v ∈ Subgroup.centralizer ({u} : Set Y) := Subgroup.mul_mem _ htu hvu
  have hmt := hm _ (oddQuotMk_mem_modOdd hm3.1 htu)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one hm3.1 ht.ne_one
      (hF.ne_tu hL) htu)
  have hmv := hm _ (oddQuotMk_mem_modOdd hm3.2.2 hvu)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one hm3.2.2 hF.invJ₂.ne_one
      hF.ne hvu)
  have hmtv : ∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨v, hvu⟩ * y ≠
      y * (oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨v, hvu⟩) := by
    rw [← map_mul]
    exact hm _ (oddQuotMk_mem_modOdd htvB htvC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one htvB htv1 htvu htvC)
  exact S289.false_of_linkDich_at_u hL hD hF.memJ hF.invJ hF.memJ₂ hF.invJ₂ htu hvu hLc hmt hmv
    hmtv

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
