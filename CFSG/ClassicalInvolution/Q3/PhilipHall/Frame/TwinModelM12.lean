module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

open CFSG.Blueprint CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section M12


theorem m12_oddCoreIn_top :
    oddCoreIn (⊤ : Subgroup NativeSporadic.M12) = ⊥ := by
  have hs : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have : Finite NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.1
  set S := oddCoreIn (⊤ : Subgroup NativeSporadic.M12) with hS
  have hN : S.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_le_iff.mp (normalizer_oddCoreIn _)
  have hodd : Odd (Nat.card S) := odd_card_oddCoreIn _
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top, CFSG.Sporadic.Schreier.m12_card] at hodd
    exact absurd hodd (by decide)

theorem m12_odd_aut_inner (α : MulAut NativeSporadic.M12) (hα : Odd (orderOf α)) :
    α ∈ innSubgroup NativeSporadic.M12 := by
  have : Finite NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.1
  have hZ := CFSG.Sporadic.Schreier.m12_center_eq_bot'
  have hinj := conj_injective_of_center_eq_bot hZ
  have hcard : Nat.card (MulAut NativeSporadic.M12) ≤ 2 * Nat.card NativeSporadic.M12 :=
    CFSG.Sporadic.Schreier.m12_mulAut_card
  have hinn : inner NativeSporadic.M12 = innSubgroup NativeSporadic.M12 := rfl
  have h1 : Nat.card (innSubgroup NativeSporadic.M12) = Nat.card NativeSporadic.M12 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h2 := (innSubgroup NativeSporadic.M12).card_mul_index
  have hidx : (innSubgroup NativeSporadic.M12).index ≤ 2 := by
    have hpos : 0 < Nat.card NativeSporadic.M12 := Nat.card_pos
    rw [h1] at h2
    nlinarith
  have hpos : 0 < (innSubgroup NativeSporadic.M12).index := by
    rw [Nat.pos_iff_ne_zero]
    exact Subgroup.index_ne_zero_of_finite
  set q : MulAut NativeSporadic.M12 →* Outer NativeSporadic.M12 :=
    QuotientGroup.mk' (inner NativeSporadic.M12) with hq
  have h3 : orderOf (q α) ∣ orderOf α := orderOf_map_dvd q α
  have h4 : orderOf (q α) ∣ (innSubgroup NativeSporadic.M12).index :=
    (orderOf_dvd_natCard (q α))
  have h5 : orderOf (q α) = 1 := by
    have hodd' : Odd (orderOf (q α)) := Odd.of_dvd_nat hα h3
    have hle := Nat.le_of_dvd hpos h4
    rcases (by omega : (innSubgroup NativeSporadic.M12).index = 1 ∨
        (innSubgroup NativeSporadic.M12).index = 2) with h | h
    · rw [h] at h4
      exact Nat.dvd_one.mp h4
    · rw [h] at h4
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h' | h'
      · exact h'
      · rw [h'] at hodd'
        exact absurd hodd' (by decide)
  have h6 : q α = 1 := orderOf_eq_one_iff.mp h5
  exact (QuotientGroup.eq_one_iff α).mp h6

theorem m12_fixedOddFree : FixedOddFree NativeSporadic.M12 := by
  have hZ := CFSG.Sporadic.Schreier.m12_center_eq_bot'
  have : Finite NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.1
  intro σ hσ
  by_cases hin : σ ∈ innSubgroup NativeSporadic.M12
  · obtain ⟨s, rfl⟩ := hin
    have hss : s * s = 1 := by
      apply conj_injective_of_center_eq_bot hZ
      rw [map_mul, map_one]
      exact hσ
    by_cases hs1 : s = 1
    · subst hs1
      have : fixedSubgroup (MulAut.conj (1 : NativeSporadic.M12)) = ⊤ := by
        ext x
        simp [mem_fixedSubgroup_iff]
      rw [this]
      exact m12_oddCoreIn_top
    · have hs2 : orderOf s = 2 := orderOf_eq_prime (by rwa [← sq] at hss) hs1
      rw [fixedSubgroup_conj]
      have h0 := CFSG.Sporadic.Schreier.m12_inner_oddCore s hs2
      show (CFSG.Open.componentClassificationOddCore _).map _ = ⊥
      have : CFSG.Open.componentClassificationOddCore
          ↥(Subgroup.centralizer ({s} : Set NativeSporadic.M12)) = ⊥ := h0
      rw [this, Subgroup.map_bot]
  · have hfix : fixedSubgroup σ = CFSG.Sporadic.Schreier.fixSub σ := rfl
    rw [hfix]
    have h0 := CFSG.Sporadic.Schreier.m12_outer_oddCore σ hσ hin
    show (CFSG.Open.componentClassificationOddCore _).map _ = ⊥
    have : CFSG.Open.componentClassificationOddCore ↥(CFSG.Sporadic.Schreier.fixSub σ) = ⊥ := h0
    rw [this, Subgroup.map_bot]

theorem modelFactM12_of_certs : ModelFactM12 :=
  ⟨CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2,
    have : Finite (NativeSporadic.Carrier .M12) := CFSG.Sporadic.Mathieu.fam_m12_simplicity.1
    autOddFree_of_fixedOddFree CFSG.Sporadic.Schreier.m12_center_eq_bot' m12_odd_aut_inner
      m12_fixedOddFree⟩

end M12

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
