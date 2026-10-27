module

public import CFSG.Sporadic.SuzOddCore.CTIFirst
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four

section D


theorem suzD_involution_class (hcls : suzClassCheck = true) {x : Equiv.Perm (Fin 42)}
    (hx : x ∈ suzD) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ConjClasses.mk (⟨x, hx⟩ : suzD) = classEquiv 6 := by
  obtain ⟨l, hl⟩ := classFun_surjective (ConjClasses.mk (⟨x, hx⟩ : suzD))
  have hconj := ConjClasses.mk_eq_mk_iff_isConj.1 hl
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hc' : (c : Equiv.Perm (Fin 42)) * repPerm l * (c : Equiv.Perm (Fin 42))⁻¹ = x :=
    congrArg Subtype.val hc
  have hsq : repPerm l * repPerm l = 1 := by
    have h1 : (c : Equiv.Perm (Fin 42)) * (repPerm l * repPerm l) * (c : Equiv.Perm (Fin 42))⁻¹ =
        1 := by
      calc (c : Equiv.Perm (Fin 42)) * (repPerm l * repPerm l) * (c : Equiv.Perm (Fin 42))⁻¹
          = ((c : Equiv.Perm (Fin 42)) * repPerm l * (c : Equiv.Perm (Fin 42))⁻¹) *
            ((c : Equiv.Perm (Fin 42)) * repPerm l * (c : Equiv.Perm (Fin 42))⁻¹) := by group
        _ = 1 := by rw [hc', hx2]
    have h2 := mul_inv_eq_one.1 h1
    exact mul_left_cancel (a := (c : Equiv.Perm (Fin 42))) (by rw [h2, mul_one])
  have hne : repPerm l ≠ 1 := fun h => hx1 (by rw [← hc', h]; group)
  have hl6 : l = 6 := by
    by_contra hne6
    have hl0 : l ≠ 0 := fun h0 => hne (by rw [h0]; exact repPerm_zero)
    have hcheck := List.all_eq_true.1 hcls l.val (List.mem_range.2 l.2)
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hcheck
    rcases hcheck with (h0 | h6) | hneq
    · exact hl0 (Fin.ext h0)
    · exact hne6 (Fin.ext h6)
    · apply hneq
      have h1 := (tabRep_repPerm l.val).comp (tabRep_repPerm l.val)
      rw [hsq] at h1
      exact h1.tab_eq TabRep.idTab
  rw [← hl, hl6]
  rfl

theorem suzD_involutions_conj (hcls : suzClassCheck = true) :
    ∀ x ∈ suzD, ∀ y ∈ suzD, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 →
      ∃ c ∈ suzD, c * x * c⁻¹ = y := by
  intro x hx y hy hx2 hy2 hx1 hy1
  have h3 : ConjClasses.mk (⟨x, hx⟩ : suzD) = ConjClasses.mk (⟨y, hy⟩ : suzD) :=
    (suzD_involution_class hcls hx hx2 hx1).trans (suzD_involution_class hcls hy hy2 hy1).symm
  obtain ⟨c, hc⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 h3)
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem suzD_twoAdic_centralizer (hcls : suzClassCheck = true) {x : Equiv.Perm (Fin 42)}
    (hx : x ∈ suzD) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    twoAdic (suzD ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 42)))) = twoAdic suzD := by
  have h1 := card_centralizer_mul_card_class (⟨x, hx⟩ : suzD)
  rw [suzD_involution_class hcls hx hx2 hx1, card_class 6, card_suzD] at h1
  have h315 : classSizes.getD ((6 : Fin 10) : ℕ) 0 = 315 := by decide
  rw [h315] at h1
  have hcard : Nat.card ↥(centralizer ({(⟨x, hx⟩ : suzD)} : Set suzD)) = 64 := by omega
  have h2 := card_inf_centralizer_eq suzD hx
  unfold twoAdic
  rw [h2, hcard, card_suzD]
  have e64 : (64 : ℕ) = 2 ^ 6 * 1 := by norm_num
  have e20160 : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [e64, e20160, factorization_two_pow_mul 6 one_ne_zero (by norm_num),
    factorization_two_pow_mul 6 (by norm_num) (by norm_num)]

end D

end CFSG.EvenSporadicStandard.Solomon78
