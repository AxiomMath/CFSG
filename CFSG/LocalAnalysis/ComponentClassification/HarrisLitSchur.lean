module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPSLCover
import CFSG.Models.Blueprint

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup Assembly.LowTwoRank

theorem models_lieModel_of_lieModel_of_ne_zero {Y : Type} [Group Y] {τ : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (hm : Blueprint.LieModel Y τ n p f) : Models.LieModel Y τ n p f :=
  CFSG.Models.LieModel.of_blueprint_of_ne_zero hn hm

theorem card_griessHopfMultiplier_eq (hGA : TBLit.GriessMultipliersAllModels) {Y : Type}
    [Group Y] {τ : StatedLieTag} {n p f : ℕ} (hm : Models.LieModel Y τ n p f) :
    Nat.card (Open.griessHopfMultiplier Y) =
      (Blueprint.Multiplier.genericOrders τ n p f).1 *
        (Blueprint.Multiplier.genericOrders τ n p f).2 *
        ((Blueprint.Multiplier.exceptionalOrders τ n p f).1 *
          (Blueprint.Multiplier.exceptionalOrders τ n p f).2) := by
  obtain ⟨e⟩ := (hGA Y τ n p f hm).2
  rw [Nat.card_congr e.toEquiv]
  simp only [Blueprint.Multiplier.generic, Blueprint.Multiplier.exceptional, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod]

theorem card_griessHopfMultiplier_eq_odd (hGA : TBLit.GriessMultipliersOdd) {Y : Type}
    [Group Y] {τ : StatedLieTag} {n p f : ℕ} (hm : Models.LieModel Y τ n p f) (hp2 : p ≠ 2)
    (hrow : τ = .PSL ∨ (τ = .PSU ∧ Even n)) :
    Nat.card (Open.griessHopfMultiplier Y) =
      (Blueprint.Multiplier.genericOrders τ n p f).1 *
        (Blueprint.Multiplier.genericOrders τ n p f).2 *
        ((Blueprint.Multiplier.exceptionalOrders τ n p f).1 *
          (Blueprint.Multiplier.exceptionalOrders τ n p f).2) := by
  obtain ⟨e⟩ := (hGA Y τ n p f hm hp2 hrow).2
  rw [Nat.card_congr e.toEquiv]
  simp only [Blueprint.Multiplier.generic, Blueprint.Multiplier.exceptional, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod]

theorem odd_exceptionalOrders_psl {m p f : ℕ} (hp2 : p ≠ 2) :
    Odd ((Blueprint.Multiplier.exceptionalOrders .PSL m p f).1 *
      (Blueprint.Multiplier.exceptionalOrders .PSL m p f).2) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> first | decide | simp_all

theorem odd_exceptionalOrders_psu {m p f : ℕ} (hp2 : p ≠ 2) :
    Odd ((Blueprint.Multiplier.exceptionalOrders .PSU m p f).1 *
      (Blueprint.Multiplier.exceptionalOrders .PSU m p f).2) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> first | decide | simp_all

theorem factorization_two_mul_odd {a b : ℕ} (ha : a ≠ 0) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  rw [Nat.factorization_mul ha hb.pos.ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (fun h =>
      (Nat.not_even_iff_odd.mpr hb) (even_iff_two_dvd.mpr h)), add_zero]

theorem factorization_card_griessHopfMultiplier_psl (hGA : TBLit.GriessMultipliersOdd)
    {Y : Type} [Group Y] {m p f : ℕ} (hp2 : p ≠ 2) (hm : m ≠ 0)
    (hL : Blueprint.LieModel Y .PSL m p f) :
    (Nat.card (Open.griessHopfMultiplier Y)).factorization 2 =
      (Nat.gcd m (p ^ f - 1)).factorization 2 := by
  rw [card_griessHopfMultiplier_eq_odd hGA (models_lieModel_of_lieModel_of_ne_zero hm hL) hp2
    (Or.inl rfl)]
  rw [show Blueprint.Multiplier.genericOrders .PSL m p f = (Nat.gcd m (p ^ f - 1), 1) from rfl,
    mul_one]
  exact factorization_two_mul_odd (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hm)).ne'
    (odd_exceptionalOrders_psl hp2)

theorem factorization_card_griessHopfMultiplier_psu (hGA : TBLit.GriessMultipliersOdd)
    {Y : Type} [Group Y] {m p f : ℕ} (hp2 : p ≠ 2) (hm : m ≠ 0) (hme : Even m)
    (hL : Blueprint.LieModel Y .PSU m p f) :
    (Nat.card (Open.griessHopfMultiplier Y)).factorization 2 =
      (Nat.gcd m (p ^ f + 1)).factorization 2 := by
  rw [card_griessHopfMultiplier_eq_odd hGA (models_lieModel_of_lieModel_of_ne_zero hm hL) hp2
    (Or.inr ⟨rfl, hme⟩)]
  rw [show Blueprint.Multiplier.genericOrders .PSU m p f = (Nat.gcd m (p ^ f + 1), 1) from rfl,
    mul_one]
  exact factorization_two_mul_odd (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hm)).ne'
    (odd_exceptionalOrders_psu hp2)

theorem ordProj_card_griessHopfMultiplier_psl_two (hGA : TBLit.GriessMultipliersOdd)
    {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : Blueprint.LieModel Y .PSL 2 p f) :
    ordProj[2] (Nat.card (Open.griessHopfMultiplier Y)) = 2 := by
  rw [factorization_card_griessHopfMultiplier_psl hGA hp2 two_ne_zero hL]
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨k, hk⟩ := hodd
  rw [hk, Nat.add_sub_cancel, Nat.gcd_eq_left (dvd_mul_right 2 k),
    Nat.Prime.factorization_self Nat.prime_two, pow_one]

theorem card_sylow_two_center_le_two_of_psl_two (hGA : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (Q ⧸ center Q) .PSL 2 p f) (S : Sylow 2 ↥(center Q)) :
    Nat.card S ≤ 2 := by
  have hm' := TBLit.models_lieModel_of_lieModel_psl_two hm
  have hS2 := TBLit.sylow_two_card_griessHopfMultiplier_psl_two hGA hp hp2 hm'
  exact (hGC (Q ⧸ center Q) .PSL 2 p f hm').1 (fun S => (hS2 S).le) Q hQ ⟨MulEquiv.refl _⟩ S

theorem card_center_eq_two_of_psl_two (hGA : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 ↥(center Q)) (hZ1 : center Q ≠ ⊥) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : Blueprint.LieModel (Q ⧸ center Q) .PSL 2 p f) :
    Nat.card ↥(center Q) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(center Q)) := inferInstance
  have hle := card_sylow_two_center_le_two_of_psl_two hGA hGC hQ hp hp2 hm S
  have hSZ : Nat.card S = Nat.card ↥(center Q) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
    rw [Sylow.card_eq_multiplicity, hk, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  have h1 : 1 < Nat.card ↥(center Q) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    exact hZ1
  omega

theorem fusionZStar_eq_center_of_pPrimeCore_eq_bot {B : Type*} [Group B]
    (hO : pPrimeCore 2 B = ⊥) : Open.fusionZStar B = center B := by
  ext l
  rw [GSThmB.OddQuot.mem_fusionZStar_iff, hO, mem_center_iff]
  constructor
  · intro h m
    have := h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  · intro h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (h m).symm

theorem card_fusionZStar_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker) :
    Nat.card ↥(Open.fusionZStar A) = Nat.card f.ker * Nat.card ↥(Open.fusionZStar B) := by
  have hZ := GSThmB.OddQuot.comap_fusionZStar_of_surjective f hf hker
  have hs := f.subgroupComap_surjective (Open.fusionZStar B) hf
  have h1 := Subgroup.card_ker_mul_card_range (f.subgroupComap (Open.fusionZStar B))
  rw [MonoidHom.range_eq_top_of_surjective _ hs, card_top] at h1
  have h2 : Nat.card (f.subgroupComap (Open.fusionZStar B)).ker = Nat.card f.ker := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨(x : (Open.fusionZStar B).comap f),
      MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp x.2))⟩)
      ⟨fun x y h => ?_, fun y => ?_⟩)
    · exact Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : A)) h))
    · refine ⟨⟨⟨y, ?_⟩, ?_⟩, rfl⟩
      · rw [mem_comap, MonoidHom.mem_ker.mp y.2]
        exact one_mem _
      · exact Subtype.ext (MonoidHom.mem_ker.mp y.2)
  rw [← hZ, ← h1, h2]

theorem isMTypeSchur_of_surjective (hGA : TBLit.GriessMultipliersOdd) {A B : Type}
    [Group A] [Group B] [Finite A] [Finite B] {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker)
    (hA : Group.IsPerfect A) (hB : IsQuasisimple B) (hO : pPrimeCore 2 B = ⊥)
    (hZ : Nat.card ↥(center B) = 2) (hm : Blueprint.LieModel (B ⧸ center B) .PSL 2 p k) :
    IsMTypeSchur p A := by
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective f hf hker
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective f hf hker
  have hZB := fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  have eC : A ⧸ Open.fusionZStar A ≃* B ⧸ center B :=
    eZ.trans (QuotientGroup.quotientMulEquivOfEq hZB)
  have hmA : Blueprint.LieModel (A ⧸ Open.fusionZStar A) .PSL 2 p k :=
    GSThmB.OddQuot.lieModel_of_equiv eC.symm hm
  have hcard : Nat.card ↥(Open.fusionZStar A) = Nat.card f.ker * 2 := by
    rw [card_fusionZStar_of_surjective f hf hker, hZB, hZ]
  have hkodd : Odd (Nat.card f.ker) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hker)
  have hord : ordProj[2] (Nat.card ↥(Open.fusionZStar A)) = 2 := by
    rw [hcard, mul_comm, factorization_two_mul_odd two_ne_zero hkodd,
      Nat.Prime.factorization_self Nat.prime_two, pow_one]
  have hBq : IsQuasisimple (B ⧸ pPrimeCore 2 B) :=
    LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO.symm)) hB
  refine .inl ⟨⟨hA, LocalCores.isQuasisimple_of_mulEquiv eO.symm hBq⟩, ⟨.PSL, 2, k, hmA⟩, ?_,
    fun n r _ _ _ => ?_⟩
  · rw [hcard]
    exact Nat.even_mul.mpr (Or.inr even_two)
  · rw [hord, ordProj_card_griessHopfMultiplier_psl_two hGA hp hp2 hmA]

end CFSG.ComponentClassification.HarrisLit
