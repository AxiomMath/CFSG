module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthogonalRank
public import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint.Multiplier

theorem card_multPair (a b : ℕ) :
    Nat.card (Multiplicative (ZMod a) × Multiplicative (ZMod b)) = a * b := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, Nat.card_zmod]

theorem exceptionalOrders_two_one_dvd (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) :
    (exceptionalOrders t n 2 1).1 * (exceptionalOrders t n 2 1).2 ∣ 4 := by
  unfold exceptionalOrders
  split <;> simp_all

theorem genericOrders_two_one_dvd {t : CFSG.Assembly.LowTwoRank.StatedLieTag} (n : ℕ)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    (genericOrders t n 2 1).1 * (genericOrders t n 2 1).2 ∣ 12 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · simp [genericOrders]
  · simp only [genericOrders]
    simp
    exact (Nat.gcd_dvd_right _ _).trans (by norm_num)
  · simp [genericOrders]
  · simp [genericOrders]
  · simp only [genericOrders]
    simp
    exact (Nat.gcd_dvd_left _ _).trans (by norm_num)

theorem card_multiplier_dvd_of_lieModel_two (hG : GriessAllModelsStatement) {Y : Type} [Group Y]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hY : CFSG.Models.LieModel Y t n 2 1) :
    Nat.card (griessHopfMultiplier Y) ∣ 48 := by
  obtain ⟨-, ⟨e⟩⟩ := hG Y t n 2 1 hY
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have h1 : Nat.card (generic t n 2 1) =
      (genericOrders t n 2 1).1 * (genericOrders t n 2 1).2 := card_multPair _ _
  have h2 : Nat.card (exceptional t n 2 1) =
      (exceptionalOrders t n 2 1).1 * (exceptionalOrders t n 2 1).2 := card_multPair _ _
  rw [h1, h2]
  have := genericOrders_two_one_dvd (t := t) n ht
  have := exceptionalOrders_two_one_dvd t n
  exact (mul_dvd_mul (genericOrders_two_one_dvd (t := t) n ht)
    (exceptionalOrders_two_one_dvd t n)).trans (by norm_num)

theorem not_nine_dvd_multiplier_of_classicalIndexTwo (hG : GriessAllModelsStatement) {Y : Type}
    [Group Y] (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2IndexTwo d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : ¬ 9 ∣ Nat.card (griessHopfMultiplier Y) := by
  intro h9
  obtain ⟨d1, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d1 with
  | A r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_of_lieModel_two hG (t := .PSL) (n := r + 1) (Or.inl rfl)
      ⟨h.1, Or.inl h⟩
    have := h9.trans this
    omega
  | twistedA r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_of_lieModel_two hG (t := .PSU) (n := r + 1)
      (Or.inr (Or.inl rfl)) ⟨h.1, Or.inl h⟩
    have := h9.trans this
    omega
  | B r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have hr3 : 3 ≤ r := by
      have h2 := hrange.1
      have h3 : r ≠ 2 := fun h => hrange.2 ⟨h, hd⟩
      omega
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3 e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_of_lieModel_two hG (t := .PSp) (n := r)
      (Or.inr (Or.inr (Or.inl rfl))) ⟨h.1, Or.inl h⟩
    have := h9.trans this
    omega
  | D r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_of_lieModel_two hG (t := .POmegaPlus) (n := r)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ⟨h.1, Or.inl h⟩
    have := h9.trans this
    omega
  | twistedD r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_of_lieModel_two hG (t := .POmegaMinus) (n := r)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) ⟨h.1, Or.inl h⟩
    have := h9.trans this
    omega
  | G2 q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    have := hrange
    omega
  | _ => exact hd.elim

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
