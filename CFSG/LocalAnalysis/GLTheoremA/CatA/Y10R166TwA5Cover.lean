module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UnitaryCover
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial

theorem isQuasisimple_statedSU_six {n : ℕ} (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    CFSG.IsQuasisimple (StatedSU 6 (2 ^ n) F) :=
  (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := n)
    (F := F) (n := 6) hF (by norm_num) (by simp)).1

theorem center_statedSU_six_eq_scalars {n : ℕ} (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    Subgroup.center (StatedSU 6 (2 ^ n) F) =
      (StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ n) F) :=
  (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := n)
    (F := F) (n := 6) hF (by norm_num) (by simp)).2

theorem card_center_statedSU_six {n : ℕ} (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hodd : Odd n) :
    Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F)) = 3 := by
  have hUD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, hodd.pos, by rw [hF, ← pow_mul]; congr 1; ring⟩
  rw [center_statedSU_six_eq_scalars F hF,
    ← CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hUD (n := 6) (by norm_num),
    CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hUD (n := 6) (by norm_num)]
  have h3dvd : 3 ∣ 2 ^ n + 1 :=
    CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.three_dvd_pow_add_one hodd
  have hqodd : Odd (2 ^ n + 1) := by
    simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one
      (f := 1) (n := n) (by norm_num) hodd.pos
  have h3g : 3 ∣ Nat.gcd 6 (2 ^ n + 1) := Nat.dvd_gcd (by norm_num) h3dvd
  have hg3 : Nat.gcd 6 (2 ^ n + 1) ∣ 3 := by
    have hg6 : Nat.gcd 6 (2 ^ n + 1) ∣ 6 := Nat.gcd_dvd_left _ _
    have hgodd : Odd (Nat.gcd 6 (2 ^ n + 1)) := Odd.of_dvd_nat hqodd (Nat.gcd_dvd_right _ _)
    exact hgodd.coprime_two_right.dvd_of_dvd_mul_left (by simpa using hg6)
  exact Nat.dvd_antisymm hg3 h3g

section Certs


theorem exists_mulEquiv_statedSU_of_label_center_three {K : Type} [Group K] [Finite K]
    {lab : GLALabel} {p : ℕ} (hK : HasLabel K (fun l : GLALabel => l = lab))
    (hfam : i166FamTwA5 lab p (Subgroup.center K = ⊥))
    (h3 : Nat.card (Subgroup.center K) = 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧ Nonempty (K ≃* StatedSU 6 (2 ^ lab.n) F) := by
  obtain ⟨t, r, n⟩ := lab
  simp only [i166FamTwA5] at hfam
  obtain ⟨ht, hr, hn2, hdvd⟩ := hfam
  subst ht
  subst hr
  have hG : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hoddn : Odd n :=
    (unitarySix_mult (n := n) hn2 hK hG (by rw [h3])).1
  obtain ⟨F, hFld, hFin, hChar, C, hCn, hFcard, hCcen, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSU_quot_of_isLabel hG hK (by rfl) hn2
  letI : Field F := hFld
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  letI : C.Normal := hCn
  have hperf : Group.IsPerfect (StatedSU 6 (2 ^ n) F) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := n) (F := F) (n := 6) hFcard
      (by norm_num) (by simp)).1.1
  have hZeq := center_statedSU_six_eq_scalars F hFcard
  have hZcard : Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F)) = 3 :=
    card_center_statedSU_six F hFcard hoddn
  have hC3 : Nat.card C ∣ 3 := by
    rw [← hZcard]
    exact Subgroup.card_dvd_of_le hCcen
  by_cases hCbot : C = ⊥
  · subst hCbot
    exact ⟨F, hFld, hFin, hChar, hFcard, ⟨e.trans QuotientGroup.quotientBot⟩⟩
  · exfalso
    have hC3card : Nat.card C = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hC3 with h1 | h3'
      · exact absurd (Subgroup.card_eq_one.1 h1) hCbot
      · exact h3'
    have hCtop : C = Subgroup.center (StatedSU 6 (2 ^ n) F) :=
      Subgroup.eq_of_le_of_card_ge hCcen (by rw [hZcard, hC3card])
    subst hCtop
    have hZq : Subgroup.center
        (StatedSU 6 (2 ^ n) F ⧸ Subgroup.center (StatedSU 6 (2 ^ n) F)) = ⊥ := by
      haveI : Group.IsPerfect (StatedSU 6 (2 ^ n) F) := hperf
      exact Group.IsPerfect.center_quotient_center_eq_bot (G := StatedSU 6 (2 ^ n) F)
    obtain ⟨e'⟩ : Nonempty (K ≃*
        (StatedSU 6 (2 ^ n) F ⧸ Subgroup.center (StatedSU 6 (2 ^ n) F))) := ⟨e⟩
    have h13 : Nat.card (Subgroup.center K) = 1 :=
      (card_center_congr e').symm.trans (by rw [hZq, Subgroup.card_bot])
    rw [h3] at h13
    exact absurd h13 (by norm_num)

end Certs

@[expose] def TwA5CoverModel : Prop :=
  ∀ (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2],
    Nat.card F = (2 ^ n) ^ 2 → Odd n → 2 ≤ n →
    p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 →
    4 ≤ evenRank (StatedSU 6 (2 ^ n) F) →
    GLATwoLocalRank p (StatedSU 6 (2 ^ n) F) + 1 = evenRank (StatedSU 6 (2 ^ n) F) →
    ∃ (q : ℕ) (B' : Subgroup (StatedSU 6 (2 ^ n) F)) (x' : StatedSU 6 (2 ^ n) F)
      (J : Subgroup (StatedSU 6 (2 ^ n) F)), Concl166S (StatedSU 6 (2 ^ n) F) p q B' x' J



end CFSG.LocalAnalysis.GLTheoremA.Y10F
