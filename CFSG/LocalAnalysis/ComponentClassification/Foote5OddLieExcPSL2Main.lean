module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2E7

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.X10

@[expose] def NoPSLTwoOddCentreComponent (t : StatedLieTag) : Prop :=
  ∀ (M : Type) [Group M] [Finite M], IsPGroup 2 (center M) → ∀ r e : ℕ, r.Prime → r ≠ 2 →
    StatedLieAdmissible t 0 r e → LieModel (M ⧸ center M) t 0 r e →
    ∀ x : M, x * x = 1 → x ∉ center M → ∀ J : Subgroup ↥(centralizer ({x} : Set M)),
      IsPComponent 2 J → ∀ p f : ℕ, p.Prime → 5 ≤ p ^ f →
        ¬ LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f

theorem noPSLTwoOddCentreComponent_of_famInner
    (hO : LieOrderFormulasInput) {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags)
    (hfam : FamInnerNoPSL2 t) : NoPSLTwoOddCentreComponent t :=
  fun _ _ _ hZ2 _ _ hr hr2 hadm hS _ hx hxZ _ hJ _ _ hp h5 hJm =>
    false_of_quasisimple_of_famInner hO ht hfam hZ2 hr hr2 hadm hS hx hxZ hJ hp h5 hJm

theorem noPSLTwoOddCentreComponent_untwisted
    {t : StatedLieTag} (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    NoPSLTwoOddCentreComponent t := by
  have hO : LieOrderFormulasInput := lieOrderFormulasInput
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact noPSLTwoOddCentreComponent_of_famInner hO (by decide) famInnerNoPSL2_G2
  · exact noPSLTwoOddCentreComponent_of_famInner hO (by decide) (famInnerNoPSL2_F4 hO)
  · exact noPSLTwoOddCentreComponent_of_famInner hO (by decide) (famInnerNoPSL2_E6 hO)
  · exact noPSLTwoOddCentreComponent_of_famInner hO (by decide) (famInnerNoPSL2_E7 hO)
  · exact noPSLTwoOddCentreComponent_of_famInner hO (by decide) (famInnerNoPSL2_E8 hO)

theorem three_pow_odd_mod_sixteen {e : ℕ} (he : Odd e) : 3 ^ e % 16 = 3 ∨ 3 ^ e % 16 = 11 := by
  obtain ⟨k, rfl⟩ := he
  induction k with
  | zero => left; rfl
  | succ k ih =>
    have h : 3 ^ (2 * (k + 1) + 1) = 3 ^ (2 * k + 1) * 9 := by ring
    rw [h, Nat.mul_mod]
    rcases ih with h3 | h3 <;> rw [h3] <;> norm_num

theorem not_sixteen_dvd_card_of_lieModel_twistedG2 (hO : LieOrderFormulasInput) {X : Type}
    [Group X] {e : ℕ} (hadm : StatedLieAdmissible .twistedG2 0 3 e)
    (hX : LieModel X .twistedG2 0 3 e) : ¬ 16 ∣ Nat.card X := by
  obtain ⟨-, hc, -⟩ := hO X .twistedG2 0 3 e hadm hX
  have hc' : Nat.card X * 1 = (3 ^ e) ^ 3 * ((3 ^ e) ^ 3 + 1) * (3 ^ e - 1) := hc
  rw [mul_one] at hc'
  have he : Odd e := hadm.2.2.2.2.1
  rw [hc']
  have hq := three_pow_odd_mod_sixteen he
  obtain ⟨a, ha⟩ : ∃ a, 3 ^ e = a + 1 :=
    ⟨3 ^ e - 1, by have := Nat.one_le_pow e 3 (by norm_num); omega⟩
  rw [ha, Nat.add_sub_cancel]
  rw [ha] at hq
  have hP : (a + 1) ^ 3 * ((a + 1) ^ 3 + 1) * a ≡
      (a % 16 + 1) ^ 3 * ((a % 16 + 1) ^ 3 + 1) * (a % 16) [MOD 16] := by
    have h := (Nat.mod_modEq a 16).symm
    exact (((h.add_right 1).pow 3).mul (((h.add_right 1).pow 3).add_right 1)).mul h
  have h8 : (a + 1) ^ 3 * ((a + 1) ^ 3 + 1) * a % 16 = 8 := by
    rw [show (a + 1) ^ 3 * ((a + 1) ^ 3 + 1) * a % 16 =
      (a % 16 + 1) ^ 3 * ((a % 16 + 1) ^ 3 + 1) * (a % 16) % 16 from hP]
    rcases hq with hq | hq
    · norm_num [show a % 16 = 2 by omega]
    · norm_num [show a % 16 = 10 by omega]
  intro h16
  have h0 := Nat.mod_eq_zero_of_dvd h16
  omega

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
