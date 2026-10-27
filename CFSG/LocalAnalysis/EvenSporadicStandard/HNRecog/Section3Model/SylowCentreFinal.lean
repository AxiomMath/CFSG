module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Unique
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SylowCentre

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

section Cert


theorem suborbitFacts_sylow_centre :
    ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
      ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → ∀ T : Subgroup H, T ≤ Gx z → Nat.card T = 2 ^ 11 →
        centerOf T = Subgroup.zpowers a ⊔ Subgroup.zpowers z := by
  intro H _ E h a z b z₁ hf T hTz hT
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ, -⟩ := exists_mulEquiv_p1408_of_isF5Centralizer h
  haveI : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  haveI : Finite H := Finite.of_equiv _ Ψ.symm.toEquiv
  have hsyl : 2 ^ (Nat.card H).factorization 2 = 2 ^ 11 := by
    rw [Nat.card_congr Ψ.toEquiv, hP, two_factorization_card_P1408]
  have h4 : Nat.card ↥(centerOf T) = 4 := by
    have hTm : Nat.card ↥(T.map Ψ.toMonoidHom) = 2 ^ 11 := by
      rw [Subgroup.card_map_of_injective Ψ.injective]
      exact hT
    have h1 := card_centerOf_sylow_P1408 hP (T.map Ψ.toMonoidHom) hTm
    rwa [centerOf_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective T,
      Subgroup.card_map_of_injective Ψ.injective] at h1
  have ha : a ∈ center H := by
    rw [hf.center_eq]
    exact mem_zpowers a
  have haT : a ∈ T :=
    mem_of_orderOf_two_of_le_centralizer (by rw [hT, hsyl]) hf.orderOf_a fun t _ =>
      mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]
        exact (mem_center_iff.mp ha t).symm
  have hzT : z ∈ T := mem_of_orderOf_two_of_le_centralizer (by rw [hT, hsyl]) hf.orderOf_z hTz
  have hle : zpowers a ⊔ zpowers z ≤ centerOf T := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact ⟨haT, mem_centralizer_iff.mpr fun t _ => mem_center_iff.mp ha t⟩
    · rw [zpowers_le]
      exact ⟨hzT, mem_centralizer_iff.mpr fun t ht =>
        (mem_centralizer_iff.mp (hTz ht) z (Set.mem_singleton z)).symm⟩
  have haz : a ≠ z := fun h' => (hf.not_isConj 0 1 (by decide)) (by simpa [h'] using IsConj.refl z)
  have ha1 : a ≠ 1 := fun h' => by
    have := hf.orderOf_a
    rw [h', orderOf_one] at this
    omega
  have hz1 : z ≠ 1 := fun h' => by
    have := hf.orderOf_z
    rw [h', orderOf_one] at this
    omega
  have haa : a * a = 1 := by
    rw [← pow_two, ← hf.orderOf_a]
    exact pow_orderOf_eq_one a
  have haz1 : a * z ≠ 1 := fun h' => haz (mul_left_cancel (h'.trans haa.symm)).symm
  have hane : a ≠ a * z := fun h' =>
    hz1 (mul_left_cancel (a := a) (b := z) (c := 1) (by rw [mul_one]; exact h'.symm))
  have hzne : z ≠ a * z := fun h' =>
    ha1 (mul_right_cancel (a := a) (b := z) (c := 1) (by rw [one_mul]; exact h'.symm))
  have hfour : ({1, a, z, a * z} : Set H).ncard = 4 := by
    have h1 : (1 : H) ∉ ({a, z, a * z} : Set H) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hz1.symm, haz1.symm⟩
    have h2 : a ∉ ({z, a * z} : Set H) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨haz, hane⟩
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair hzne]
  have hsub : ({1, a, z, a * z} : Set H) ⊆ ((zpowers a ⊔ zpowers z : Subgroup H) : Set H) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers a)
    · exact mem_sup_right (mem_zpowers z)
    · exact mul_mem (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers z))
  have hge : Nat.card ↥(centerOf T) ≤ Nat.card ↥(zpowers a ⊔ zpowers z) := by
    have e : Nat.card ↥(zpowers a ⊔ zpowers z) =
        ((zpowers a ⊔ zpowers z : Subgroup H) : Set H).ncard := Nat.card_coe_set_eq _
    rw [e, h4, ← hfour]
    exact Set.ncard_le_ncard hsub
  exact (eq_of_le_of_card_ge hle hge).symm

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3
