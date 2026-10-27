module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeExcBase
public import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcE
import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.RankFourTheoremC
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.I294CrossLargeExc

@[expose] def I294CrossLargeIsE6 : TauCeti.LieTypeIndex → Prop
  | .E6 _ => True
  | _ => False

@[expose] def I294CrossLargeIsE7 : TauCeti.LieTypeIndex → Prop
  | .E7 _ => True
  | _ => False

@[expose] def I294CrossLargeIsE8 : TauCeti.LieTypeIndex → Prop
  | .E8 _ => True
  | _ => False

section Adjoint


theorem abelOrRankFour_E6 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : AbelOrRankFour p (adjointGroup Tag.E6 F) := by
  by_cases h7 : 7 ≤ p
  · exact AbelOrRankFour.of_sylow_comm fun S =>
      isMulCommutative_sylow_adjointGroup hp (crossExc_not_dvd_card_weylGroup_E6 hp h7) hpF S
  · obtain rfl : p = 5 := eq_five_of_lt_seven hp h5 (by omega)
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod 5) = e := ⟨_, rfl⟩
    have hd : e ∣ 4 := he ▸ orderOf_natCast_dvd_pred hp hpF
    rcases cases_dvd_four hd with rfl | rfl | rfl
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_one F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_two F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc le_rfl
    · exact AbelOrRankFour.of_sylowTorus (sylowTorus_E6_four F hp he)

theorem abelOrRankFour_E7 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : AbelOrRankFour p (adjointGroup Tag.E7 F) := by
  by_cases h11 : 11 ≤ p
  · exact AbelOrRankFour.of_sylow_comm fun S =>
      isMulCommutative_sylow_adjointGroup hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp (by omega)
          (Or.inr (Or.inl rfl))) hpF S
  by_cases h7 : 7 ≤ p
  · obtain rfl : p = 7 := eq_seven_of_lt_eleven hp h7 (by omega)
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod 7) = e := ⟨_, rfl⟩
    have hd : e ∣ 6 := he ▸ orderOf_natCast_dvd_pred hp hpF
    rcases cases_dvd_six hd with rfl | rfl | rfl | rfl
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_one F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_two F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sylowTorus_E7 F hp
        (le_refl 7) hpF (by rw [he]; decide) (Or.inr (by rw [he]))
      exact AbelOrRankFour.of_sylowTorus hm
    · obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sylowTorus_E7 F hp
        (le_refl 7) hpF (by rw [he]; decide) (Or.inr (by rw [he]; norm_num))
      exact AbelOrRankFour.of_sylowTorus hm
  · obtain rfl : p = 5 := eq_five_of_lt_seven hp h5 (by omega)
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod 5) = e := ⟨_, rfl⟩
    have hd : e ∣ 4 := he ▸ orderOf_natCast_dvd_pred hp hpF
    rcases cases_dvd_four hd with rfl | rfl | rfl
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_one F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_two F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · exact AbelOrRankFour.of_sylowTorus (sylowTorus_E7_four F hp he)

theorem abelOrRankFour_E8 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : AbelOrRankFour p (adjointGroup Tag.E8 F) := by
  by_cases h11 : 11 ≤ p
  · exact AbelOrRankFour.of_sylow_comm fun S =>
      isMulCommutative_sylow_adjointGroup hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp (by omega) (Or.inr (Or.inr rfl)))
        hpF S
  by_cases h7 : 7 ≤ p
  · obtain rfl : p = 7 := eq_seven_of_lt_eleven hp h7 (by omega)
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod 7) = e := ⟨_, rfl⟩
    have hd : e ∣ 6 := he ▸ orderOf_natCast_dvd_pred hp hpF
    rcases cases_dvd_six hd with rfl | rfl | rfl | rfl
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_one F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_two F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_three F hp he
      exact AbelOrRankFour.of_elemAbelian hp hE hc le_rfl
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_six F hp he
      exact AbelOrRankFour.of_elemAbelian hp hE hc le_rfl
  · obtain rfl : p = 5 := eq_five_of_lt_seven hp h5 (by omega)
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod 5) = e := ⟨_, rfl⟩
    have hd : e ∣ 4 := he ▸ orderOf_natCast_dvd_pred hp hpF
    rcases cases_dvd_four hd with rfl | rfl | rfl
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_one F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_two F hp (by norm_num) he
      exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_four F hp he
      exact AbelOrRankFour.of_elemAbelian hp hE hc le_rfl

theorem abelOrRankFour_of_untwisted {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) {q : TauCeti.PrimePower}
    (hv : (c q).Valid) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p)
    (H : ∀ (F : Type) [Field F] [Finite F], ¬ p ∣ Nat.card F →
      AbelOrRankFour p (adjointGroup τ F))
    {L : Type} [Group L] [Finite L] (e : L ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) :
    AbelOrRankFour p L := by
  obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  exact AbelOrRankFour.of_mulEquiv hp (e.trans φ) (H K hpK)

theorem i294CrossLargePrimeOn_E8 : I294CrossLargePrimeOn I294CrossLargeIsE8 := by
  refine i294CrossLargePrimeOn_of_abelOrRankFour ?_
  intro p hp h5 ⟨i, hv⟩ hφ hd L _ _ ⟨e⟩
  cases i with
  | E8 q =>
    have hpq : p ≠ q.p := Ne.symm (by simpa [TauCeti.LieTypeIndex.characteristic_E8] using hd)
    exact abelOrRankFour_of_untwisted
      (CFSG.TauCetiBridge.Even.untwistedBridgeAll_of CFSG.TauCetiBridge.untwistedBridge_E8
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8) hv hp hpq
      (fun F _ _ hpF => abelOrRankFour_E8 F hp h5 hpF) e
  | _ => exact (hφ : False).elim

end Adjoint

section E6E7


theorem i294CrossLargePrimeOn_E6 : I294CrossLargePrimeOn I294CrossLargeIsE6 := by
  refine i294CrossLargePrimeOn_of_abelOrRankFour ?_
  intro p hp h5 ⟨i, hv⟩ hφ hd L _ _ ⟨e⟩
  cases i with
  | E6 q =>
    have hpq : p ≠ q.p := Ne.symm (by simpa [TauCeti.LieTypeIndex.characteristic_E6] using hd)
    exact abelOrRankFour_of_untwisted
      (CFSG.TauCetiBridge.Even.untwistedBridgeAll_of CFSG.TauCetiBridge.untwistedBridge_E6
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6) hv hp hpq
      (fun F _ _ hpF => abelOrRankFour_E6 F hp h5 hpF) e
  | _ => exact (hφ : False).elim

theorem i294CrossLargePrimeOn_E7 : I294CrossLargePrimeOn I294CrossLargeIsE7 := by
  refine i294CrossLargePrimeOn_of_abelOrRankFour ?_
  intro p hp h5 ⟨i, hv⟩ hφ hd L _ _ ⟨e⟩
  cases i with
  | E7 q =>
    have hpq : p ≠ q.p := Ne.symm (by simpa [TauCeti.LieTypeIndex.characteristic_E7] using hd)
    exact abelOrRankFour_of_untwisted
      (CFSG.TauCetiBridge.Even.untwistedBridgeAll_of CFSG.TauCetiBridge.untwistedBridge_E7
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7) hv hp hpq
      (fun F _ _ hpF => abelOrRankFour_E7 F hp h5 hpF) e
  | _ => exact (hφ : False).elim

end E6E7

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
