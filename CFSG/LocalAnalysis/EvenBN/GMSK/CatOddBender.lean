module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootGeneric
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssemblyHolds
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
import CFSG.LocalAnalysis.SeitzReduction.CrossChar
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatOdd

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification

namespace OddBender

theorem not_two_pow_six_dvd_card_of_lieModel_PSL_two_two_three {X : Type} [Group X]
    (h : LieModel X .PSL 2 2 3) : ¬ 2 ^ 6 ∣ Nat.card X := by
  rw [SeitzReduction.F4Pilot.card_of_lieModel_PSL_two_two_three h]
  decide

theorem two_pow_dvd_card_of_le_factorization {X : Type} {k : ℕ}
    (hk : k ≤ (Nat.card X).factorization 2) : 2 ^ k ∣ Nat.card X :=
  (pow_dvd_pow 2 hk).trans (Nat.ordProj_dvd _ 2)

end OddBender

open OddBender

theorem not_lieModel_PSL_two_two_three_of_lieModel_PSU3 {X : Type} [Group X] {n : ℕ}
    (h : LieModel X .PSU 3 2 n) : ¬ LieModel X .PSL 2 2 3 := fun hL =>
  not_two_pow_six_dvd_card_of_lieModel_PSL_two_two_three hL
    (two_pow_dvd_card_of_le_factorization (by
      rw [factorization_two_card_of_lieModel_PSU3 h]
      have := two_le_of_lieModel_PSU3 h
      omega))

theorem not_lieModel_PSL_two_two_three_of_lieModel_twistedB2 {X : Type} [Group X] {n : ℕ}
    (h : LieModel X .twistedB2 0 2 n) : ¬ LieModel X .PSL 2 2 3 := fun hL =>
  not_two_pow_six_dvd_card_of_lieModel_PSL_two_two_three hL
    (two_pow_dvd_card_of_le_factorization (by
      rw [factorization_two_card_of_lieModel_twistedB2 h]
      have := three_le_of_lieModel_twistedB2 h
      omega))

section Orders


theorem u3NotOddLie {X : Type} [Group X] {n : ℕ} (h : LieModel X .PSU 3 2 n) :
    ¬ OddLieType X :=
  SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two CatLeafProof.lieOrderFormulasInput h
    (fun h' => absurd h'.1 (by decide)) (fun h' => absurd h'.1 (by decide))
    (fun h' => absurd h'.2.1 (by decide))

end Orders

section GLS3


theorem FixedRootDatumOf.oddLieType_or_exception {T : StdType} {D : Type} [Group D] {n : ℕ}
    {α : MulAut D} {S : Subgroup D} (d : FixedRootDatumOf T D n α S) (hD : OddLieType D)
    [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) :
    OddLieType S ∨ (LieModel D .G2 0 3 1 ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      LieModel S .PSL 2 2 3) := by
  obtain ⟨t, m, p, f, hp, hp2, hadm, hDm⟩ := hD
  set F := α.toMonoidHom.eqLocus (MonoidHom.id D)
  let e : S.subgroupOf F ≃* S := Subgroup.subgroupOfEquivOfLe d.le_fixed
  have : IsSimpleGroup (S.subgroupOf F) := e.isSimpleGroup
  have hnab : ∃ x y : S.subgroupOf F, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hS
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  rcases CatLeafProof.gls3OddLieAutComponentsInput_holds D t m p f hp hp2 hadm hDm α
      d.orderOf_eq (S.subgroupOf F) ⟨hq, d.normal.isSubnormal⟩ with
    ⟨τ', n', f', hadm', hm'⟩ | ⟨-, hG2, hout, hL⟩
  · exact .inl ⟨τ', n', p, f', hp, hp2, hadm', StdType.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)) hm'⟩
  · exact .inr ⟨hG2, hout, StdType.lieModel_of_mulEquiv e hL⟩

theorem fixedRootSelectorOf_oddLieType_U3 :
    FixedRootSelectorOf T_U3 SurvU3 (fun D _ => OddLieType D) := by
  intro D _ _ _ hD n α S d
  have hS : LieModel S .PSU 3 2 n := d.type.2
  have := isSimpleGroup_of_lieModel_PSU3 hS
  rcases d.oddLieType_or_exception hD (exists_mul_ne_of_lieModel_PSU3 hS) with h | ⟨-, -, h⟩
  · exact absurd h (u3NotOddLie hS)
  · exact absurd h (not_lieModel_PSL_two_two_three_of_lieModel_PSU3 hS)

theorem fixedRootSelectorOf_oddLieType_Sz :
    FixedRootSelectorOf T_Sz SurvSz (fun D _ => OddLieType D) := by
  intro D _ _ _ hD n α S d
  have hS : LieModel S .twistedB2 0 2 n := d.type
  have := isSimpleGroup_of_lieModel_twistedB2 hS
  rcases d.oddLieType_or_exception hD (exists_mul_ne_of_lieModel_twistedB2 hS) with
    h | ⟨-, -, h⟩
  · exact absurd h (szNotOddLie hS)
  · exact absurd h (not_lieModel_PSL_two_two_three_of_lieModel_twistedB2 hS)

end GLS3

end CFSG.LocalAnalysis.EvenBN.GMSK
