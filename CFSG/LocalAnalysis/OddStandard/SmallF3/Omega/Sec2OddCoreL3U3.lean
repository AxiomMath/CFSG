module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreGL2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreGU2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem odd_of_card_one_or_three {m : ℕ} (h : m = 1 ∨ m = 3) : Odd m := by
  rcases h with rfl | rfl <;> decide

theorem oddCore_centralizer_of_lieModel_psl33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSL 3 3 1) {z : Y} (hz : orderOf z = 2) :
    oddCore ↥(Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
  have hclass : StatedClassicalModel Y .PSL 3 3 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨-, F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hclass
  have hLn : IsLnEps 3 Y 1 (3 ^ 1) := Or.inl ⟨rfl, F, hFfield, hFfin, hFcard, ⟨e⟩⟩
  obtain ⟨F', hF'field, hF'fin, N, hN, hF'card, hNcard, ⟨e'⟩⟩ :=
    ivk_4_1a_L3 Y 3 1 Nat.prime_three (by norm_num) hLn z hz
  have hF3 : Nat.card F' = 3 := by rw [hF'card]; norm_num
  exact oddCore_eq_bot_of_mulEquiv e'.symm
    (oddCore_quotient_eq_bot_of_odd (oddCore_gl2_eq_bot F' hF3) N (odd_of_card_one_or_three hNcard))

theorem oddCore_centralizer_of_lieModel_psu33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSU 3 3 1) {z : Y} (hz : orderOf z = 2) :
    oddCore ↥(Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
  have hclass : StatedClassicalModel Y .PSU 3 3 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨-, F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hclass
  have hLn : IsLnEps 3 Y (-1) (3 ^ 1) := Or.inr ⟨rfl, F, hFfield, hFfin, hFcard, ⟨e⟩⟩
  obtain ⟨F', hF'field, hF'fin, N, hN, hF'card, hNcard, ⟨e'⟩⟩ :=
    ivk_4_1a_U3 Y 3 1 Nat.prime_three (by norm_num) hLn z hz
  have hF9 : Nat.card F' = 9 := by rw [hF'card]; norm_num
  exact oddCore_eq_bot_of_mulEquiv e'.symm
    (oddCore_quotient_eq_bot_of_odd (oddCore_gu2_eq_bot hF9) N (odd_of_card_one_or_three hNcard))

end CFSG.OddStandard.SmallF3.Omega
