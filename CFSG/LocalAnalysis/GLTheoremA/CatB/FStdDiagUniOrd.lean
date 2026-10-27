module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagLinBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoOrders
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Open.StatedAPI
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU hct_heldSU_eq_statedSU)

theorem fstdUni_block {a m : ℕ} {E : Type} [Field E] [Finite E] (τ' : E ≃+* E)
    (hτ' : ∀ x, τ' (τ' x) = x) (ha : 2 ≤ a) (hτ'm : ∀ x, τ' x = x ^ 2 ^ m)
    (hE : Nat.card E = (2 ^ m) ^ 2)
    (hsmall : Nat.card (↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ')) = 25920 ∨
      Nat.card (↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ')) = 360) :
    Subgroup.center ↥(heldSU a E τ' hτ') = ⊥ ∧
      Nat.card (↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ')) = 25920 := by
  have hm : 1 ≤ m := by
    by_contra hlt
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    rw [hE, show m = 0 by omega] at h1
    simp at h1
  have hH : heldSU a E τ' hτ' = StatedSU a (2 ^ m) E := hct_heldSU_eq_statedSU hτ'm
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  ·
    exfalso
    obtain rfl : a = 2 := by omega
    obtain ⟨k₂, hk₂, hk₂f, hk₂c, ⟨ψ⟩⟩ :=
      Y10GInnUni.exists_quot_heldSU_two_equiv_psl τ' hτ' hτ'm hE
    obtain ⟨h1, h2⟩ := fstdLin_card_psl_ne (b := 2) le_rfl hk₂c
    rw [Nat.card_congr ψ.toEquiv] at hsmall
    rcases hsmall with h | h
    · exact h1 h
    · exact h2 h
  · by_cases h31 : a = 3 ∧ m = 1
    ·
      exfalso
      obtain ⟨rfl, rfl⟩ := h31
      have hcard : Nat.card ↥(heldSU 3 E τ' hτ') = 216 := by
        have hc := CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two
          (F := E) (f := 1) hE
        rw [hH]
        norm_num at hc ⊢
        exact hc
      have hdvd : Nat.card (↥(heldSU 3 E τ' hτ') ⧸ Subgroup.center ↥(heldSU 3 E τ' hτ')) ∣
          216 := by
        rw [← hcard]
        exact Subgroup.card_quotient_dvd_card _
      rcases hsmall with h | h <;> rw [h] at hdvd <;> omega
    · have ham : (a, 2 ^ m) ≠ (3, 2) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      obtain ⟨ψ⟩ := Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
        Y10GInnUni.uniScalar_holds τ' hτ' hτ'm hE ha3 ham
      have hψ := Nat.card_congr ψ.toEquiv
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hm hE ha]
        at hψ
      by_cases h41 : a = 4 ∧ m = 1
      · obtain ⟨rfl, rfl⟩ := h41
        have hq : Nat.card (↥(heldSU 4 E τ' hτ') ⧸ Subgroup.center ↥(heldSU 4 E τ' hτ')) =
            25920 := by
          rw [hψ]
          decide +kernel
        have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 E :=
          ⟨Nat.prime_two, le_rfl, by rw [hE]; norm_num⟩
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : CharP E 2 :=
          (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (Y10GInnUni.two_eq_zero_of_card hE)
        have hSU : Nat.card ↥(heldSU 4 E τ' hτ') = 25920 := by
          have h := CFSG.RankThree.PartOne.KFU.card_statedSU_eq hF (n := 4) (by norm_num)
          have h' : ((Nat.card ↥(StatedSU 4 (2 ^ 1) E) : ℕ) : ℤ) = 25920 := by
            rw [h]
            decide +kernel
          rw [hH]
          exact_mod_cast h'
        have hc1 : Nat.card ↥(Subgroup.center ↥(heldSU 4 E τ' hτ')) = 1 := by
          have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
            (Subgroup.center ↥(heldSU 4 E τ' hτ'))
          rw [hq, hSU] at h
          omega
        exact ⟨Subgroup.eq_bot_of_card_eq _ hc1, hq⟩
      · exfalso
        obtain ⟨-, h2, h3⟩ :=
          CFSG.StandardType.ExcThreeAtTwo.ordPSU_notExcThree ha3 hm h41
        rw [← hψ] at h2 h3
        rcases hsmall with h | h
        · exact h2 h
        · exact h3 h

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
