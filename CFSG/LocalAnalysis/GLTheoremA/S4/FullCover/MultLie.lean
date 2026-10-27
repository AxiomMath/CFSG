module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultBound
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

noncomputable def centralIso {Q S : Type} [Group Q] [Group S] (π : Q →* S)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center Q) :
    Q ⧸ Subgroup.center Q ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)

theorem card_center_dvd_of_table (hGA : CFSG.Open.GriessAllModelsStatement)
    {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q) {t : StatedLieTag}
    {n p f a b c d : ℕ} (hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) t n p f)
    (hg : genericOrders t n p f = (a, b)) (he : exceptionalOrders t n p f = (c, d))
    (hne : a * b * (c * d) ≠ 0) : Nat.card (Subgroup.center Q) ∣ a * b * (c * d) := by
  have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_table hGA
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff Q).2.2.1.2 hQ) hm (by rw [hg, he]; exact hne)
  rwa [hg, he] at h


theorem primePower_eq_of_card_eq {q : TauCeti.PrimePower} {r s : ℕ} (hr : r.Prime) (hs : 0 < s)
    (h : q.card = r ^ s) : q.p = r ∧ q.exponent = s := by
  rw [TauCeti.PrimePower.card_def] at h
  obtain ⟨m, hm⟩ : ∃ m, q.exponent = m + 1 := ⟨q.exponent - 1, by have := q.exponent_pos; omega⟩
  obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [hm, hk] at h
  obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj q.prime_p hr h
  exact ⟨h1, by omega⟩

theorem false_of_pGroup_dvd {p m : ℕ} (hp : p.Prime) {Z : Type} [Group Z] [Finite Z]
    (hZ : IsPGroup p Z) [hnt : Nontrivial Z] (hd : Nat.card Z ∣ m) (hpm : ¬ p ∣ m) : False :=
  hpm (pGroup_card_of_dvd hp hZ hnt hd).1

section Cases

open TauCeti

theorem lieCase_A_one (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A 1 q).Valid) : ListedMultiplierBoundAt p (.lie ⟨.A 1 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, -⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  have hm := CFSG.Models.lieModel_A 1 q hv e
  have hdup := ((LieTypeIndex.valid_iff _).1 hv).2
  have hc4 : q.card ≠ 4 := fun h =>
    hdup ((LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inl ⟨rfl, Or.inl h⟩))
  have hc9 : q.card ≠ 9 := fun h =>
    hdup ((LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inl ⟨rfl, Or.inr (Or.inr h)⟩))
  have hn1 : ¬ (q.p = 2 ∧ q.exponent = 2) := fun ⟨h1, h2⟩ => hc4 (by
    rw [PrimePower.card_def, h1, h2]; norm_num)
  have hn2 : ¬ (q.p = 3 ∧ q.exponent = 2) := fun ⟨h1, h2⟩ => hc9 (by
    rw [PrimePower.card_def, h1, h2]; norm_num)
  have he : exceptionalOrders .PSL (1 + 1) q.p q.exponent = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : genericOrders .PSL (1 + 1) q.p q.exponent =
      (Nat.gcd (1 + 1) (q.p ^ q.exponent - 1), 1) := rfl
  have hdvd := card_center_dvd_of_table hGA hQ hm hg he
    (by simpa using Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 1 + 1))
  exact (false_of_pGroup_dvd Nat.prime_three hZ
    (hdvd.trans (by simpa using Nat.gcd_dvd_left (1 + 1) _)) (by norm_num)).elim


theorem lieCase_A_two (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A 2 q).Valid) : ListedMultiplierBoundAt p (.lie ⟨.A 2 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  have hm := CFSG.Models.lieModel_A 2 q hv e
  have hdup := ((LieTypeIndex.valid_iff _).1 hv).2
  have hc2 : q.card ≠ 2 := fun h =>
    hdup ((LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inr (Or.inl ⟨rfl, h⟩)))
  have hn1 : ¬ (q.p = 2 ∧ q.exponent = 1) := fun ⟨h1, h2⟩ => hc2 (by
    rw [PrimePower.card_def, h1, h2]; norm_num)
  have hg : genericOrders .PSL (2 + 1) q.p q.exponent =
      (Nat.gcd (2 + 1) (q.p ^ q.exponent - 1), 1) := rfl
  have hgd : Nat.gcd (2 + 1) (q.p ^ q.exponent - 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have hgpos : 0 < Nat.gcd (2 + 1) (q.p ^ q.exponent - 1) :=
    Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdvd48 : Nat.card (Subgroup.center Q) ∣ 48 := by
    by_cases h : q.p = 2 ∧ q.exponent = 2
    · obtain ⟨h1, h2⟩ := h
      have he : exceptionalOrders .PSL (2 + 1) q.p q.exponent = (4, 4) := by
        rw [h1, h2]; rfl
      have := card_center_dvd_of_table hGA hQ hm hg he (by simpa using hgpos.ne')
      refine this.trans ?_
      simpa using (Nat.mul_dvd_mul_right hgd 16).trans (by norm_num : 3 * 16 ∣ 48)
    · have he : exceptionalOrders .PSL (2 + 1) q.p q.exponent = (1, 1) := by
        unfold exceptionalOrders
        split <;> simp_all
      have := card_center_dvd_of_table hGA hQ hm hg he (by simpa using hgpos.ne')
      refine this.trans ?_
      simpa using hgd.trans (by norm_num : 3 ∣ 48)
  rcases hi with (⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩
  · exact ⟨rfl, (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd48).2 (by norm_num),
      trivial⟩
  · exact (false_of_pGroup_dvd (by norm_num) hZ hdvd48 (by norm_num)).elim
  · exact ⟨rfl, (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd48).2 (by norm_num),
      trivial⟩

theorem lieModel_twistedA' {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    CFSG.Models.LieModel G .PSU (r + 1) q.p q.exponent := by
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  have h := CFSG.Models.lieModel_twistedA r q hv e
  rwa [hc, hf] at h

theorem lieCase_twistedA_two (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    ListedMultiplierBoundAt p (.lie ⟨.twistedA 2 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  have hm := lieModel_twistedA' 2 q hv e
  have hg : genericOrders .PSU (2 + 1) q.p q.exponent =
      (Nat.gcd (2 + 1) (q.p ^ q.exponent + 1), 1) := rfl
  have he : exceptionalOrders .PSU (2 + 1) q.p q.exponent = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hdvd := card_center_dvd_of_table hGA hQ hm hg he
    (by simpa using Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 2 + 1))
  have hdvd3 : Nat.card (Subgroup.center Q) ∣ 3 :=
    hdvd.trans (by simpa using Nat.gcd_dvd_left (2 + 1) (q.p ^ q.exponent + 1))
  rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨rfl, (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd3).2 (by norm_num),
      trivial⟩
  · exact ⟨rfl, (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd3).2 (by norm_num),
      trivial⟩


theorem lieCase_twistedA_three (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 3 q).Valid) :
    ListedMultiplierBoundAt p (.lie ⟨.twistedA 3 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, hq8⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq8.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1)
    (by decide) (by decide) (by norm_num)
  exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim

theorem lieCase_twistedA_four (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 4 q).Valid) :
    ListedMultiplierBoundAt p (.lie ⟨.twistedA 4 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, hq2⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := lieModel_twistedA' 4 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1)
    (by decide) (by decide) (by norm_num)
  exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim

theorem lieCase_twistedA_five (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 5 q).Valid) :
    ListedMultiplierBoundAt p (.lie ⟨.twistedA 5 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, hq2⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := lieModel_twistedA' 5 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 3) (b := 1) (c := 2) (d := 2)
    (by decide) (by decide) (by norm_num)
  exact ⟨rfl, (pGroup_card_of_dvd Nat.prime_three hZ inferInstance hdvd).2 (by norm_num), hq2⟩


theorem lieCase_B_two (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B 2 q).Valid) : ListedMultiplierBoundAt p (.lie ⟨.B 2 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, hq8⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq8.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 2 q hv e with hm | hm
  · rw [h1, h2] at hm
    have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1)
      (by decide) (by decide) (by norm_num)
    exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim
  · rw [h1, h2] at hm
    have hdvd := card_center_dvd_of_table hGA hQ hm (a := 2) (b := 1) (c := 1) (d := 1)
      (by decide) (by decide) (by norm_num)
    exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim

theorem lieCase_B_three (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B 3 q).Valid) : ListedMultiplierBoundAt p (.lie ⟨.B 3 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, hq2⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
  · rw [h1, h2] at hm
    have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 2) (d := 1)
      (by decide) (by decide) (by norm_num)
    exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim
  · rw [h1, h2] at hm
    have hdvd := card_center_dvd_of_table hGA hQ hm (a := 2) (b := 1) (c := 1) (d := 1)
      (by decide) (by decide) (by norm_num)
    exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim

theorem lieCase_D_four (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D 4 q).Valid) : ListedMultiplierBoundAt p (.lie ⟨.D 4 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, hq2⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := CFSG.Models.lieModel_D 4 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 2) (d := 2)
    (by decide) (by decide) (by norm_num)
  exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim

theorem lieCase_G2 (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) : ListedMultiplierBoundAt p (.lie ⟨.G2 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, hq8⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq8.trans (by norm_num))
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .G2 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag (t := .G2) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl, hq ▸ hr⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1)
    (by decide) (by decide) (by norm_num)
  exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim

theorem lieCase_trialityD4 (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) :
    ListedMultiplierBoundAt p (.lie ⟨.trialityD4 q, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, -⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .trialityD4 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1)
    rfl rfl (by norm_num)
  exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim

theorem lieCase_suzuki (hGA : CFSG.Open.GriessAllModelsStatement) (p m : ℕ)
    (hv : (LieTypeIndex.suzuki m).Valid) : ListedMultiplierBoundAt p (.lie ⟨.suzuki m, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  rcases hi with ⟨rfl, rfl⟩ | ⟨-, h⟩
  swap
  · exact h.elim
  have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .twistedB2 0 2 (2 * 2 + 1) :=
    CFSG.Models.lieModel_of_namesTag (t := .twistedB2) (p := 2) (f := 2 * 2 + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one 2, by omega⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1)
    (by decide) (by decide) (by norm_num)
  exact (false_of_pGroup_dvd (by norm_num) hZ hdvd (by norm_num)).elim

theorem lieCase_reeF4 (hGA : CFSG.Open.GriessAllModelsStatement) (p m : ℕ)
    (hv : (LieTypeIndex.reeF4 m).Valid) : ListedMultiplierBoundAt p (.lie ⟨.reeF4 m, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .twistedF4 0 2 (2 * m + 1) :=
    CFSG.Models.lieModel_of_namesTag (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1)
    rfl rfl (by norm_num)
  rcases hi with (⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨-, h⟩
  · exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim
  · exact (false_of_pGroup_dvd (by norm_num) hZ hdvd (by norm_num)).elim
  · exact h.elim

theorem lieCase_tits (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ)
    (hv : LieTypeIndex.tits.Valid) : ListedMultiplierBoundAt p (.lie ⟨.tits, hv⟩) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have e := centralIso π hπ hker
  have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .Tits 0 2 1 :=
    CFSG.Models.lieModel_of_namesTag (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1)
    rfl rfl (by norm_num)
  rcases hi with (⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨-, h⟩
  · exact (false_of_pGroup_dvd Nat.prime_three hZ hdvd (by norm_num)).elim
  · exact (false_of_pGroup_dvd (by norm_num) hZ hdvd (by norm_num)).elim
  · exact h.elim


end Cases

theorem listedMultiplierBoundAt_lie (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ)
    (j : TauCeti.ValidLieTypeIndex) : ListedMultiplierBoundAt p (.lie j) := by
  obtain ⟨d, hv⟩ := j
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | r
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact lieCase_A_one hGA p q hv
    · exact lieCase_A_two hGA p q hv
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact lieCase_twistedA_two hGA p q hv
    · exact lieCase_twistedA_three hGA p q hv
    · exact lieCase_twistedA_four hGA p q hv
    · exact lieCase_twistedA_five hGA p q hv
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | B r q =>
    rcases r with _ | _ | _ | _ | r
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact lieCase_B_two hGA p q hv
    · exact lieCase_B_three hGA p q hv
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | C r q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | D r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact lieCase_D_four hGA p q hv
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | twistedD r q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | E6 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | E7 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | E8 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | F4 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | G2 q => exact lieCase_G2 hGA p q hv
  | twistedE6 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | trialityD4 q => exact lieCase_trialityD4 hGA p q hv
  | suzuki m => exact lieCase_suzuki hGA p m hv
  | reeG2 m => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | reeF4 m => exact lieCase_reeF4 hGA p m hv
  | tits => exact lieCase_tits hGA p hv

end CFSG.LocalAnalysis.GLTheoremA
