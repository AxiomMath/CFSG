module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvLie

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Equiv Equiv.Perm Subgroup CFSG.EvenSporadicStandard.HSStd.HOv
  CFSG.ComponentClassification.OuterAutomorphisms

theorem false_of_good_triple_psl_three_five {D : Type} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {a b : D}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (ea : Nonempty (↥(centralizer ({a} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eb : Nonempty (↥(centralizer ({b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eab : Nonempty (↥(centralizer ({a * b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (hL : CFSG.Blueprint.LieModel ↥(commutator D) .PSL 3 5 1) : False := by
  have hM := statedClassicalModel_of_lieModel (by norm_num) hL
  obtain ⟨hcard, -, -, -, hout⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound ↥(commutator D) 3 5 1 hM
  have hcard' : Nat.card ↥(commutator D) = 372000 := by rw [hcard]; decide
  refine false_of_good_triple_of_normal hZ ha hb hab hcomm ea eb eab (commutator D)
    (by rw [hcard']; norm_num) (by rw [hcard']; norm_num)
    (fun E hE => CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_elemAbelian_two_le_four_of_PSL3
      (by norm_num) (by norm_num) hL E hE) 2 ?_ (fun k hk => Nat.le_of_dvd (by norm_num) hk)
  have h := hout le_rfl
  have h2 : 2 * 1 * Nat.gcd 3 (5 ^ 1 - 1) = 2 := by decide
  rwa [h2] at h

theorem false_of_good_triple_psu_three_five {D : Type} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {a b : D}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (ea : Nonempty (↥(centralizer ({a} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eb : Nonempty (↥(centralizer ({b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eab : Nonempty (↥(centralizer ({a * b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (hL : CFSG.Blueprint.LieModel ↥(commutator ↥(commutator D)) .PSU 3 5 1) : False := by
  obtain ⟨H, hHn, ⟨eH⟩⟩ := exists_normal_commutator_commutator D
  have hLH : CFSG.Blueprint.LieModel ↥H .PSU 3 5 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eH hL
  have hM := statedClassicalModel_of_lieModel (by norm_num) hLH
  have hcard := (CFSG.RankThree.Classical.unitary_three_five_model ↥H hM).1
  have hout := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound ↥H 3 5 1
    hM).2.2.1
  have h6 : 2 * 1 * Nat.gcd 3 (5 ^ 1 + 1) = 6 := by decide
  rw [h6] at hout
  refine false_of_good_triple_of_normal hZ ha hb hab hcomm ea eb eab H
    (by rw [hcard]; norm_num) (by rw [hcard]; norm_num) ?_ 6 (by rw [hout]) ?_
  · intro E hE
    obtain ⟨k, hk, hkr⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_le_of_pRank hE
    have := CFSG.Quasithin.H13.KGInsp4316.pRank_two_le_two_of_psu3_odd (by norm_num)
      (by norm_num) hM
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (hkr.trans this) |>.trans (by norm_num)
  · intro k hk
    have h1 : 2 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> norm_num
    · have h2 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
      have h3 := dvd_trans h2 hk
      norm_num at h3

end CFSG.EvenSporadicStandard.HSStd.HFI
