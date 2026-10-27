module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeIndex
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSmall
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.Alternating.Multipliers.Small
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub

section Catalog


theorem parabData_g2 (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hd : q.p = 2)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : ParabData Y := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
    (GaloisField q.p q.exponent) hK
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
  have hm : 2 ≤ q.exponent := by
    by_contra hm
    have h1 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hq4 : 4 ≤ q.card := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨2 ^ q.exponent, ?_, fun p hp hp5 hpZ => ?_⟩
  · rw [← hcard, ← hK]
    exact parabCore_g2 (e.trans b.symm) (hK ▸ hq4)
  · have hL : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .G2 0 2 q.exponent :=
      ⟨⟨Nat.prime_two, q.exponent_pos, rfl, by rw [← hcard]; exact hq3⟩,
        Or.inr ⟨rfl, ⟨⟨.G2 q, hv⟩, ⟨hd, rfl⟩, ⟨e⟩⟩⟩⟩
    exact dvd_sq_sub_one_of_dvd_card_center hGA hY (MulEquiv.refl _)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) q.exponent_pos hL hp hp5 hpZ

theorem parabData_of_index (I : ParabInputs) (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) : ParabData Y := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hd] at h
    exact parabData_of_classicalModel I hGA hY (Or.inl rfl) h
  | twistedA r q =>
    change q.p = 2 at hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hd] at h
    exact parabData_of_classicalModel I hGA hY (Or.inr (Or.inl rfl)) h
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact parabData_of_classicalModel I hGA hY (Or.inr (Or.inr (Or.inl rfl))) h
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact parabData_of_classicalModel I hGA hY (Or.inr (Or.inr (Or.inl rfl))) h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact parabData_of_classicalModel I hGA hY (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact parabData_of_classicalModel I hGA hY (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h
  | G2 q =>
    change q.p = 2 at hd
    exact parabData_g2 hGA hY q hv hd e
  | _ => exact hd.elim

end Catalog

section Small

open CFSG.Blueprint.Multiplier

theorem isQuasisimple_of_open {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) :
    CFSG.IsQuasisimple Y := by
  have hnonab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := by
    have : Group.IsPerfect Y := ⟨hY.1⟩
    have : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hnoncomm := Group.IsPerfect.not_isMulCommutative (Y ⧸ Subgroup.center Y)
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm
  exact ⟨⟨hY.1⟩, hY.2, hnonab⟩

theorem not_dvd_of_dvd_six {m p : ℕ} (hm : m ∣ 6) (hp5 : 5 ≤ p) (hp : p.Prime) : ¬ p ∣ m := by
  intro h
  have h6 : p ∣ 6 := h.trans hm
  have hle := Nat.le_of_dvd (by norm_num) h6
  interval_cases p
  · omega
  · exact absurd hp (by norm_num)


theorem card_center_dvd_two_of_psl_seven (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type}
    [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (h : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 7 1) :
    Nat.card (Subgroup.center Y) ∣ 2 := by
  have h1 := card_center_dvd_of_griess hGA hY (MulEquiv.refl _) (t := .PSL) (n := 2) (p := 7)
    (f := 1) ⟨h.1, Or.inl h⟩
  rw [generic, exceptional, Nat.card_prod, Nat.card_prod, card_multiplicative_zmod,
    card_multiplicative_zmod, card_multiplicative_zmod, card_multiplicative_zmod] at h1
  have e1 : genericOrders .PSL 2 7 1 = (2, 1) := by simp [genericOrders]
  have e2 : exceptionalOrders .PSL 2 7 1 = (1, 1) := by simp [exceptionalOrders]
  rw [e1, e2] at h1
  simpa using h1

theorem card_center_dvd_one_of_psu_three_three (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (h : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU 3 3 1) :
    Nat.card (Subgroup.center Y) ∣ 1 := by
  have h1 := card_center_dvd_of_griess hGA hY (MulEquiv.refl _) (t := .PSU) (n := 3) (p := 3)
    (f := 1) ⟨h.1, Or.inl h⟩
  rw [generic, exceptional, Nat.card_prod, Nat.card_prod, card_multiplicative_zmod,
    card_multiplicative_zmod, card_multiplicative_zmod, card_multiplicative_zmod] at h1
  have e1 : genericOrders .PSU 3 3 1 = (1, 1) := by simp [genericOrders]
  have e2 : exceptionalOrders .PSU 3 3 1 = (1, 1) := by simp [exceptionalOrders]
  rw [e1, e2] at h1
  simpa using h1

theorem not_dvd_card_center_alt {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {n : ℕ} (hn : n = 5 ∨ n = 6) (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin n)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card (Subgroup.center Y) := by
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier (isQuasisimple_of_open hY) e
  rcases hn with rfl | rfl
  · rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2] at h
    exact not_dvd_of_dvd_six (h.trans (by norm_num)) hp5 hp
  · rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2] at h
    exact not_dvd_of_dvd_six h hp5 hp

end Small

section Combined


theorem parabData_of_isClassicalTwoOrG2 (I : ParabInputs)
    (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (h : IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y)) :
    ParabData Y := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact parabData_of_index I hGA hY d hd e
  · rcases hn with rfl | rfl | rfl
    · exact ⟨2, parabCore_small (Or.inl ⟨5, Or.inl rfl, ⟨e⟩⟩), fun p hp hp5 hpZ =>
        absurd hpZ (not_dvd_card_center_alt hY (Or.inl rfl) e hp hp5)⟩
    · exact ⟨2, parabCore_small (Or.inl ⟨6, Or.inr rfl, ⟨e⟩⟩), fun p hp hp5 hpZ =>
        absurd hpZ (not_dvd_card_center_alt hY (Or.inr rfl) e hp hp5)⟩
    · have hL : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSL 4 2 1 :=
        (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2 ⟨e⟩
      rcases hL with ⟨-, h⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
      · exact parabData_of_classicalModel I hGA hY (Or.inl rfl) h
      all_goals exact absurd hn (by norm_num)
  · refine ⟨2, parabCore_small (Or.inr ⟨d, hd, ⟨e⟩⟩), fun p hp hp5 hpZ => ?_⟩
    exfalso
    rcases hd with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hd
      subst hd
      obtain ⟨hp7, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp7, hf] at h
      have := Nat.le_of_dvd (by norm_num) (hpZ.trans (card_center_dvd_two_of_psl_seven hGA hY h))
      omega
    · obtain ⟨dd, hv⟩ := d
      simp only at hd
      subst hd
      obtain ⟨hp3, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp3, hf] at h
      have := Nat.le_of_dvd (by norm_num)
        (hpZ.trans (card_center_dvd_one_of_psu_three_three hGA hY h))
      omega

end Combined

end CFSG.AGLEmbedding.ParabPrime
