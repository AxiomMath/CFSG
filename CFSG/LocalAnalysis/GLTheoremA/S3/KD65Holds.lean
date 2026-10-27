module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverLie
public import CFSG.LocalAnalysis.AGLEmbedding.FixedThreeOutSmallFree
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.LieType.Multipliers.U43
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.OutU43Order
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Models CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  (center_dvd_table lieModel_of_classical lieModel_lie lieModel_typeA)

private theorem kd65h_card_outer_congr {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Outer G) = Nat.card (Outer H) :=
  Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv

private theorem kd65h_inner_of_pow {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer G)) (α : MulAut G) (hα : α ^ p = 1) : α ∈ inner G := by
  let π : MulAut G →* Outer G := QuotientGroup.mk' (inner G)
  have hp' : π α ^ p = 1 := by
    rw [← map_pow, hα, map_one]
  have hord : orderOf (π α) ∣ p := orderOf_dvd_of_pow_eq_one hp'
  have hdvd : orderOf (π α) ∣ Nat.card (Outer G) := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime hp).1 hord with h1 | h1
  · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
  · exact absurd (h1 ▸ hdvd) h

private theorem kd65h_generic_coprime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : StatedLieTag)
    (n f : ℕ) (hf : 1 ≤ f) :
    Nat.Coprime p (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 ∧
      Nat.Coprime p (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 := by
  have hpp : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have h4 : Nat.Coprime p 4 := by
    have := Nat.Coprime.pow_right 2 hpp
    simpa using this
  have hq1 : Nat.Coprime p (p ^ f - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
    intro h
    have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)
  have hq2 : Nat.Coprime p (p ^ f + 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
    intro h
    have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have := Nat.dvd_sub h h1
    rw [Nat.add_sub_cancel_left] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)
  have key : ∀ g : ℕ, (g ∣ 4 ∨ g ∣ p ^ f - 1 ∨ g ∣ p ^ f + 1) → Nat.Coprime p g := by
    intro g hg
    rcases hg with h | h | h
    · exact Nat.Coprime.coprime_dvd_right h h4
    · exact Nat.Coprime.coprime_dvd_right h hq1
    · exact Nat.Coprime.coprime_dvd_right h hq2
  have one : Nat.Coprime p 1 := Nat.coprime_one_right _
  unfold CFSG.Blueprint.Multiplier.genericOrders
  cases t
  · exact ⟨key _ (Or.inr (Or.inl (Nat.gcd_dvd_right _ _))), one⟩
  · exact ⟨key _ (Or.inr (Or.inr (Nat.gcd_dvd_right _ _))), one⟩
  · exact ⟨key _ (Or.inl ((Nat.gcd_dvd_left _ _).trans (by norm_num))), one⟩
  · exact ⟨key _ (Or.inl (by norm_num)), one⟩
  · dsimp only
    split_ifs
    · exact ⟨one, one⟩
    · exact ⟨key _ (Or.inl (by norm_num)), key _ (Or.inl (by norm_num))⟩
    · exact ⟨key _ (Or.inl (Nat.gcd_dvd_left _ _)), one⟩
  · exact ⟨key _ (Or.inl (Nat.gcd_dvd_left _ _)), one⟩
  all_goals first
    | exact ⟨key _ (Or.inr (Or.inl (Nat.gcd_dvd_right _ _))), one⟩
    | exact ⟨key _ (Or.inr (Or.inr (Nat.gcd_dvd_right _ _))), one⟩
    | exact ⟨key _ (Or.inl ((Nat.gcd_dvd_left _ _).trans (by norm_num))), one⟩
    | exact ⟨one, one⟩

private theorem kd65h_exc_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : StatedLieTag)
    (n f : ℕ)
    (h : p ∣ (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) :
    (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders at h
  split at h
  all_goals first
    | exact absurd rfl hp2
    | decide
    | (exfalso
       have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) h
       have := hp.one_lt
       omega)

private theorem kd65h_table_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : StatedLieTag)
    (n f : ℕ) (hf : 1 ≤ f)
    (h : p ∣ (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2)) :
    (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  obtain ⟨g1, g2⟩ := kd65h_generic_coprime hp hp2 t n f hf
  have hnd : ∀ g : ℕ, Nat.Coprime p g → ¬ p ∣ g := fun g hg hd =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hg hd)
  rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
  · rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
    · exact absurd h'' (hnd _ g1)
    · exact absurd h'' (hnd _ g2)
  · exact kd65h_exc_three hp hp2 t n f h'


private theorem kd65h_lieModel_char (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (hp : d.1.characteristic = p) :
    ∃ (t : StatedLieTag) (n f : ℕ), LieModel (TauCeti.CFSGIndex.lie d).Group t n p f := by
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_A] at hp
    subst hp
    exact ⟨_, _, _, lieModel_typeA r q hv⟩
  | twistedA r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at hp
    subst hp
    exact ⟨_, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _))⟩
  | B r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_B] at hp
    subst hp
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ⟨_, _, _, lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _))⟩
    · by_cases hp : q.p = 2
      · exact ⟨_, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3
            (MulEquiv.refl _))⟩
      · exact ⟨_, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3
            (MulEquiv.refl _))⟩
  | C r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_C] at hp
    subst hp
    exact ⟨_, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _))⟩
  | D r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_D] at hp
    subst hp
    exact ⟨_, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _))⟩
  | twistedD r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedD] at hp
    subst hp
    exact ⟨_, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _))⟩
  | E6 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E6] at hp
    subst hp
    exact ⟨_, _, _, lieModel_lie (t := .E6) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | E7 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E7] at hp
    subst hp
    exact ⟨_, _, _, lieModel_lie (t := .E7) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | E8 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E8] at hp
    subst hp
    exact ⟨_, _, _, lieModel_lie (t := .E8) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | F4 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_F4] at hp
    subst hp
    exact ⟨_, _, _, lieModel_lie (t := .F4) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | G2 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_G2] at hp
    subst hp
    have h3q : 3 ≤ q.p ^ q.exponent := by
      simpa only [TauCeti.PrimePower.card_def] using hrange
    exact ⟨_, _, _, lieModel_lie (t := .G2) ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | twistedE6 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedE6] at hp
    subst hp
    exact ⟨_, _, _, lieModel_lie (t := .twistedE6) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩⟩
  | trialityD4 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_trialityD4] at hp
    subst hp
    exact ⟨_, _, _, lieModel_lie (t := .trialityD4) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩⟩
  | suzuki m =>
    simp only [TauCeti.LieTypeIndex.characteristic_suzuki] at hp
    subst hp
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, lieModel_lie (t := .twistedB2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩ ⟨rfl, rfl⟩⟩
  | reeG2 m =>
    simp only [TauCeti.LieTypeIndex.characteristic_reeG2] at hp
    subst hp
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, lieModel_lie (t := .twistedG2) (f := 2 * m + 1)
      ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩ ⟨rfl, rfl⟩⟩
  | reeF4 m =>
    simp only [TauCeti.LieTypeIndex.characteristic_reeF4] at hp
    subst hp
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, lieModel_lie (t := .twistedF4) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩ ⟨rfl, rfl⟩⟩
  | tits =>
    simp only [TauCeti.LieTypeIndex.characteristic_tits] at hp
    subst hp
    exact ⟨_, _, _, lieModel_lie (t := .Tits) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩⟩


theorem kd65_of_outer_facts (hGA : GriessAllModelsStatement)
    (hL2 : ∀ (X : Type) [Group X], LieModel X .PSL 2 3 2 → ¬ 3 ∣ Nat.card (Outer X))
    (hO7 : ∀ (X : Type) [Group X], LieModel X .POmegaOdd 3 3 1 → ¬ 3 ∣ Nat.card (Outer X))
    (hG2 : ∀ (X : Type) [Group X], LieModel X .G2 0 3 1 → ¬ 3 ∣ Nat.card (Outer X))
    (hU4 : ∀ (X : Type) [Group X], LieModel X .PSU 4 3 1 → ¬ 3 ∣ Nat.card (Outer X))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KD65 p := by
  intro S _ _ hS hnab hChev ⟨α, hαp, hαinn⟩ E _ _ hqE hZp ⟨e⟩
  by_contra hZne
  have hqE' : CFSG.IsQuasisimple E :=
    CFSG.AGLEmbedding.KFactProofs.ThreeCover.isQuasisimple_of_open hqE
  have hpZ : p ∣ Nat.card (Subgroup.center E) := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hZne
    · rw [hk]; exact dvd_pow_self p (Nat.succ_ne_zero k)
  have hnot : ¬ p ∣ Nat.card (Outer S) := by
    rcases hChev with ⟨i, hi, ⟨eS⟩⟩ | ⟨i, hi, ⟨eS⟩⟩
    · cases i with
      | cyclic q hq => simp only [onLie] at hi
      | alternating n hn => simp only [onLie] at hi
      | sporadic s => simp only [onLie] at hi
      | lie d =>
        have hd : d.1.characteristic = p := hi
        obtain ⟨t, n, f, hm⟩ := kd65h_lieModel_char d p hd
        have eE : E ⧸ Subgroup.center E ≃* (TauCeti.CFSGIndex.lie d).Group := e.trans eS
        have hdvd := center_dvd_table hGA hqE' eE hm
        have hT := kd65h_table_three hp hp2 t n f hm.1.2.1 (hpZ.trans hdvd)
        rw [kd65h_card_outer_congr eS]
        rcases hT with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩
        · exact hL2 _ hm
        · exact hO7 _ hm
        · exact hG2 _ hm
        · exact hU4 _ hm
    · cases i with
      | cyclic q hq => simp only [ambiguousChev] at hi
      | sporadic s => simp only [ambiguousChev] at hi
      | alternating n hn =>
        simp only [ambiguousChev] at hi
        rw [kd65h_card_outer_congr eS]
        rcases hi with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd rfl hp2
        · exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup 5 (by norm_num) 5
            (by norm_num) (by norm_num)
        · exact absurd rfl hp2
        · exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup 6 (by norm_num) 3
            (by norm_num) (by norm_num)
        · exact absurd rfl hp2
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        cases d1 with
        | A r q =>
          rcases r with _ | _ | r
          · simp only [ambiguousChev] at hi
          · simp only [ambiguousChev] at hi
            rcases hi with ⟨-, h2⟩ | ⟨hq8, rfl⟩
            · exact absurd h2 hp2
            · exfalso
              have hq := TauCeti.PrimePower.card_def q
              have hdiv : q.p ∣ 2 ^ 3 := by
                have h := dvd_pow_self q.p (show q.exponent ≠ 0 by have := q.exponent_pos; omega)
                rw [← hq, hq8] at h
                norm_num
                exact h
              have hq2 : q.p = 2 :=
                (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
                  (Nat.Prime.dvd_of_dvd_pow q.prime_p hdiv)
              have hq3 : q.exponent = 3 := by
                have h8 : q.p ^ q.exponent = 2 ^ 3 := by
                  rw [← hq, hq8]; norm_num
                rw [hq2] at h8
                exact Nat.pow_right_injective le_rfl h8
              have hm := lieModel_typeA 1 q hv
              rw [hq2, hq3] at hm
              have hdvd := center_dvd_table hGA hqE' (e.trans eS) hm
              have hprod : (CFSG.Blueprint.Multiplier.genericOrders .PSL (1 + 1) 2 3).1 *
                  (CFSG.Blueprint.Multiplier.genericOrders .PSL (1 + 1) 2 3).2 *
                  ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSL (1 + 1) 2 3).1 *
                    (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL (1 + 1) 2 3).2) = 1 := by
                norm_num [CFSG.Blueprint.Multiplier.genericOrders,
                  CFSG.Blueprint.Multiplier.exceptionalOrders]
              rw [hprod, Nat.dvd_one] at hdvd
              rw [hdvd] at hpZ
              norm_num at hpZ
          · simp only [ambiguousChev] at hi
        | twistedA r q =>
          rcases r with _ | _ | _ | _ | r
          · simp only [ambiguousChev] at hi
          · simp only [ambiguousChev] at hi
          · simp only [ambiguousChev] at hi
            exact absurd hi.2 hp2
          · simp only [ambiguousChev] at hi
            rcases hi with ⟨hq2card, rfl⟩
            exfalso
            have hq := TauCeti.PrimePower.card_def q
            have hdiv : q.p ∣ 2 := by
              have h := dvd_pow_self q.p (show q.exponent ≠ 0 by have := q.exponent_pos; omega)
              rw [← hq, hq2card] at h
              exact h
            have hq2 : q.p = 2 :=
              (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdiv
            have hq1 : q.exponent = 1 := by
              have h2 : q.p ^ q.exponent = 2 ^ 1 := by
                rw [← hq, hq2card]; norm_num
              rw [hq2] at h2
              exact Nat.pow_right_injective le_rfl h2
            have hm := lieModel_of_classical
              (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _))
            rw [hq2, hq1] at hm
            have hdvd := center_dvd_table hGA hqE' (e.trans eS) hm
            have hprod : (CFSG.Blueprint.Multiplier.genericOrders .PSU (3 + 1) 2 1).1 *
                (CFSG.Blueprint.Multiplier.genericOrders .PSU (3 + 1) 2 1).2 *
                ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSU (3 + 1) 2 1).1 *
                  (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU (3 + 1) 2 1).2) = 2 := by
              norm_num [CFSG.Blueprint.Multiplier.genericOrders,
                CFSG.Blueprint.Multiplier.exceptionalOrders]
            rw [hprod] at hdvd
            have h32 := hpZ.trans hdvd
            norm_num at h32
          · simp only [ambiguousChev] at hi
        | B r q => simp only [ambiguousChev] at hi
        | C r q => simp only [ambiguousChev] at hi
        | D r q => simp only [ambiguousChev] at hi
        | twistedD r q => simp only [ambiguousChev] at hi
        | E6 q => simp only [ambiguousChev] at hi
        | E7 q => simp only [ambiguousChev] at hi
        | E8 q => simp only [ambiguousChev] at hi
        | F4 q => simp only [ambiguousChev] at hi
        | G2 q => simp only [ambiguousChev] at hi
        | twistedE6 q => simp only [ambiguousChev] at hi
        | trialityD4 q => simp only [ambiguousChev] at hi
        | suzuki m => simp only [ambiguousChev] at hi
        | reeG2 m => simp only [ambiguousChev] at hi
        | reeF4 m => simp only [ambiguousChev] at hi
        | tits => simp only [ambiguousChev] at hi
  exact hαinn (kd65h_inner_of_pow hp hnot α hαp)


private theorem kd65h_not_dvd_omega7 (X : Type) [Group X]
    (hm : LieModel X .POmegaOdd 3 3 1) : ¬ 3 ∣ Nat.card (Outer X) := by
  rcases hm.2 with h | ⟨h0, -⟩
  · exact CFSG.AGLEmbedding.FixedThree.not_dvd_card_outer_POmegaOdd (by norm_num) (by norm_num)
      h (by norm_num)
  · exact absurd h0 (by norm_num)

private theorem kd65h_not_dvd_psl2_3 (X : Type) [Group X] (hm : LieModel X .PSL 2 3 2) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  rcases hm.2 with h | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
    obtain ⟨eA⟩ :=
      CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine hK9
    have eP := projectiveSpecialLinearGroupEquivStatedProj 2 K
    rw [kd65h_card_outer_congr ((e.trans eP.symm).trans eA)]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup 6 (by norm_num) 3
      (by norm_num) (by norm_num)
  · exact absurd h0 (by norm_num)

private theorem kd65h_not_dvd_psu4_3 (X : Type) [Group X] (hm : LieModel X .PSU 4 3 1) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  have hB : CFSG.Blueprint.LieModel X .PSU 4 3 1 := by
    rcases hm.2 with h | ⟨h0, -⟩
    · exact Or.inl ⟨by decide, h⟩
    · exact absurd h0 (by norm_num)
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hB
  rw [kd65h_card_outer_congr e, CFSG.EvenSporadicStandard.RuStd.S2.card_outer_u43]
  norm_num

section Certified


theorem kd65_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KD65 p := by
  have hG2 : ∀ (X : Type) [Group X], LieModel X .G2 0 3 1 → ¬ 3 ∣ Nat.card (Outer X) := by
    intro X _ hm
    rcases hm.2 with h | ⟨-, d, hd, ⟨eX⟩⟩
    · exact (h.2 : False).elim
    · obtain ⟨d1, hv⟩ := d
      cases d1 with
      | G2 q =>
        have hq : q.p = 3 ∧ q.exponent = 1 := hd
        have hCh :=
          CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_three q hv hq.1 hq.2
        have hX := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eX hCh
        rw [CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.card_outer_G2_three X hX]
        norm_num
      | _ => exact (show False from hd).elim
  exact kd65_of_outer_facts CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    kd65h_not_dvd_psl2_3 kd65h_not_dvd_omega7 hG2 kd65h_not_dvd_psu4_3 hp hp2

end Certified

end CFSG.LocalAnalysis.GLTheoremA
