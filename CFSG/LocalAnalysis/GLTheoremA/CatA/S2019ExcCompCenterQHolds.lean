module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcComp
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cInspF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem not_dvd_genericOrders {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    ¬ p ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 := by
  have hq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hm : ¬ p ∣ p ^ f - 1 := fun h => by
    have h1 := Nat.dvd_sub hq h
    rw [show p ^ f - (p ^ f - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one h1)
  have hpl : ¬ p ∣ p ^ f + 1 := fun h => by
    have h1 := (Nat.dvd_add_right hq).1 h
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one h1)
  have h4 : ¬ p ∣ 4 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h))
    exact hp2 this
  have h2 : ¬ p ∣ 2 := fun h => h4 (h.trans (by norm_num))
  have hdvd : ∀ {a b : ℕ}, a ∣ b → ¬ p ∣ b → ¬ p ∣ a := fun hab hb ha => hb (ha.trans hab)
  have hmul : ∀ {a b : ℕ}, ¬ p ∣ a → ¬ p ∣ b → ¬ p ∣ a * b := fun ha hb h =>
    (hp.dvd_mul.1 h).elim ha hb
  have h1 : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_one h)
  cases t <;> simp only [genericOrders]
  · exact hmul (hdvd (Nat.gcd_dvd_right _ _) hm) h1
  · exact hmul (hdvd (Nat.gcd_dvd_right _ _) hpl) h1
  · exact hmul (hdvd (Nat.gcd_dvd_left _ _) h2) h1
  · exact hmul h2 h1
  · split_ifs
    · exact hmul h1 h1
    · exact hmul h2 h2
    · exact hmul (hdvd (Nat.gcd_dvd_left _ _) h4) h1
  · exact hmul (hdvd (Nat.gcd_dvd_left _ _) h4) h1
  all_goals first
    | exact hmul h1 h1
    | exact hmul (hdvd (Nat.gcd_dvd_right _ _) hm) h1
    | exact hmul (hdvd (Nat.gcd_dvd_right _ _) hpl) h1
    | exact hmul (hdvd (Nat.gcd_dvd_left _ _) h2) h1

private theorem eq_of_dvd_exceptionalOrders {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : p ∣ (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) :
    (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  have h1 : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_one h)
  unfold exceptionalOrders at h
  split at h <;> simp_all

private theorem eq_of_dvd_card_center
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) {t : StatedLieTag} {n q f : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hmodel : CFSG.Models.LieModel (J ⧸ Subgroup.center J) t n q f)
    (hqZ : q ∣ Nat.card (Subgroup.center J)) :
    (t = .PSL ∧ n = 2 ∧ q = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ q = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ q = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ q = 3 ∧ f = 1) := by
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds _ t n q f hmodel
  have h := CFSG.RankThree.PartTwo.KFacts.KS44.card_center_dvd_card_hopfMultiplier hJ
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr eM.toEquiv] at h
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod] at h
  have hf : 1 ≤ f := hmodel.1.2.1
  rcases hq.dvd_mul.1 (hqZ.trans h) with hg | he
  · exact absurd hg (not_dvd_genericOrders hq hq2 hf)
  · exact eq_of_dvd_exceptionalOrders hq hq2 he

section Holds


theorem s2019ExcCompCenterQ_holds : S2019ExcCompCenterQ := by
  intro p q hp hp2 hq hq2 hqp K _ _ hKs hKna hK β hβp hβ1 J hJ hqZ
  obtain ⟨i, hi, ⟨eK⟩⟩ := hK
  rcases i with _ | _ | idx | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hJcomp, hchev⟩ := isComponentOf_and_isChevSimple hp hp2 hqp hKs hKna hi.1 eK hβp hβ1 hJ
  rcases hchev with hlie | hamb
  swap
  · exact .inr hamb
  left
  obtain ⟨i', hi', ⟨e'⟩⟩ := hlie
  rcases i' with _ | _ | ⟨⟨d', hv'⟩⟩ | _
  · exact absurd hi' id
  · exact absurd hi' id
  swap
  · exact absurd hi' id
  change d'.characteristic = q at hi'
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJcomp.2.2
  haveI := hJq.2
  have hperfQ : commutator (↥J ⧸ Subgroup.center ↥J) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥J))) hJq.1
    rwa [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      ← _root_.commutator_def] at h
  have hJQ : CFSG.IsQuasisimple ↥J := ⟨Group.isPerfect_def.2 hJq.1, hJq.2,
    CFSG.LocalAnalysis.GLTheoremA.H1431c.exists_ne_comm_of_simple_perfect hperfQ⟩
  have hcen := fun {t : StatedLieTag} {n f : ℕ}
      (hm : CFSG.Models.LieModel (↥J ⧸ Subgroup.center ↥J) t n q f) =>
    eq_of_dvd_card_center hJQ hq hq2 hm hqZ
  have hQ3 : ∀ Q : PrimePower, Q.p = 3 → Q.exponent = 1 → Q.card = 3 := fun Q h3 h1 => by
    rw [PrimePower.card_def, h3, h1, pow_one]
  cases d' with
  | A r Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_A] at hi'
    have hm := CFSG.Models.lieModel_A r Q hv' e'
    rw [hQp] at hm
    rcases hcen hm with ⟨-, hr, h3, hf⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exfalso
      apply ((LieTypeIndex.valid_iff _).1 hv').2
      rw [LieTypeIndex.isDuplicateRepresentative_iff]
      refine Or.inl ⟨by omega, Or.inr (Or.inr ?_)⟩
      rw [PrimePower.card_def, hQp, h3, hf]
      norm_num
    all_goals cases h
  | twistedA r Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_twistedA] at hi'
    have hm := CFSG.Models.lieModel_twistedA r Q hv' e'
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r Q, hv'⟩ = q := hi'
    have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA r Q, hv'⟩ = Q.exponent :=
      LieTypeIndex.fieldExponent_twistedA r Q
    rw [hc, hfe] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h3, hf⟩
    · cases h
    · cases h
    · cases h
    refine ⟨h3, .lie ⟨_, hv'⟩, ⟨hi'.trans h3, ?_⟩, ⟨e'⟩⟩
    change (LieTypeIndex.twistedA r Q).fieldOrder = 3
    rw [LieTypeIndex.fieldOrder_twistedA]
    exact hQ3 Q (hQp.trans h3) hf
  | B r Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_B] at hi'
    rcases CFSG.Models.lieModel_B r Q hv' e' with hm | hm
    · rw [hQp] at hm
      rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
    · rw [hQp] at hm
      rcases hcen hm with ⟨h, -⟩ | ⟨-, -, h3, hf⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · cases h
      · refine ⟨h3, .lie ⟨_, hv'⟩, ⟨hi'.trans h3, ?_⟩, ⟨e'⟩⟩
        change (LieTypeIndex.B r Q).fieldOrder = 3
        rw [LieTypeIndex.fieldOrder_B]
        exact hQ3 Q (hQp.trans h3) hf
      · cases h
      · cases h
  | C r Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_C] at hi'
    have hm := CFSG.Models.lieModel_C r Q hv' e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | D r Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_D] at hi'
    have hm := CFSG.Models.lieModel_D r Q hv' e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | twistedD r Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_twistedD] at hi'
    have hm := CFSG.Models.lieModel_twistedD r Q hv' e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | G2 Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_G2] at hi'
    have hr : 3 ≤ Q.card :=
      (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv').1
    have hm := CFSG.Models.lieModel_of_namesTag (t := .G2) (p := Q.p) (f := Q.exponent)
      ⟨Q.prime_p, Q.exponent_pos, rfl, by rw [← PrimePower.card_def]; exact hr⟩ ⟨_, hv'⟩
      ⟨rfl, rfl⟩ e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h3, hf⟩ | ⟨h, -⟩
    · cases h
    · cases h
    · refine ⟨h3, .lie ⟨_, hv'⟩, ⟨hi'.trans h3, ?_⟩, ⟨e'⟩⟩
      change (LieTypeIndex.G2 Q).fieldOrder = 3
      rw [LieTypeIndex.fieldOrder_G2]
      exact hQ3 Q (hQp.trans h3) hf
    · cases h
  | E6 Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_E6] at hi'
    have hm := CFSG.Models.lieModel_of_namesTag (t := .E6) (p := Q.p) (f := Q.exponent)
      ⟨Q.prime_p, Q.exponent_pos, rfl⟩ ⟨_, hv'⟩ ⟨rfl, rfl⟩ e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | E7 Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_E7] at hi'
    have hm := CFSG.Models.lieModel_of_namesTag (t := .E7) (p := Q.p) (f := Q.exponent)
      ⟨Q.prime_p, Q.exponent_pos, rfl⟩ ⟨_, hv'⟩ ⟨rfl, rfl⟩ e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | E8 Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_E8] at hi'
    have hm := CFSG.Models.lieModel_of_namesTag (t := .E8) (p := Q.p) (f := Q.exponent)
      ⟨Q.prime_p, Q.exponent_pos, rfl⟩ ⟨_, hv'⟩ ⟨rfl, rfl⟩ e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | F4 Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_F4] at hi'
    have hm := CFSG.Models.lieModel_of_namesTag (t := .F4) (p := Q.p) (f := Q.exponent)
      ⟨Q.prime_p, Q.exponent_pos, rfl⟩ ⟨_, hv'⟩ ⟨rfl, rfl⟩ e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | twistedE6 Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_twistedE6] at hi'
    have hm := CFSG.Models.lieModel_of_namesTag (t := .twistedE6) (p := Q.p) (f := Q.exponent)
      ⟨Q.prime_p, Q.exponent_pos, rfl⟩ ⟨_, hv'⟩ ⟨rfl, rfl⟩ e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | trialityD4 Q =>
    have hQp : Q.p = q := by rwa [LieTypeIndex.characteristic_trialityD4] at hi'
    have hm := CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := Q.p)
      (f := Q.exponent) ⟨Q.prime_p, Q.exponent_pos, rfl⟩ ⟨_, hv'⟩ ⟨rfl, rfl⟩ e'
    rw [hQp] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | suzuki m =>
    rw [LieTypeIndex.characteristic_suzuki] at hi'
    exact absurd hi'.symm hq2
  | reeG2 m =>
    rw [LieTypeIndex.characteristic_reeG2] at hi'
    have hm1 : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv').1
    have hm := CFSG.Models.lieModel_of_namesTag (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨Nat.prime_three, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩ ⟨_, hv'⟩
      ⟨rfl, rfl⟩ e'
    rw [hi'] at hm
    rcases hcen hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | reeF4 m =>
    rw [LieTypeIndex.characteristic_reeF4] at hi'
    exact absurd hi'.symm hq2
  | tits =>
    rw [LieTypeIndex.characteristic_tits] at hi'
    exact absurd hi'.symm hq2

end Holds

end CFSG.LocalAnalysis.GLTheoremA.S2019
