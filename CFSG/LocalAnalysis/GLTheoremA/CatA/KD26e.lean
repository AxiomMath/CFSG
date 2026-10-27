module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.LocalAnalysis.AGLEmbedding.FixedThreeOutSmallFree
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
import CFSG.Adapters.TauCetiLieModels
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem kd26e_dvd_card_outer {K : Type} [Group K] [Group.IsPerfect K] {p : ℕ} (hp : p.Prime)
    {α : MulAut K} (hα : α ^ p = 1) (hαn : α ∉ inner K) :
    p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
  have : Fact p.Prime := ⟨hp⟩
  set ᾱ : MulAut (K ⧸ Subgroup.center K) := centerQuotientHom K α with hᾱ
  have hᾱp : ᾱ ^ p = 1 := by rw [hᾱ, ← map_pow, hα, map_one]
  have hᾱn : ᾱ ∉ inner (K ⧸ Subgroup.center K) := fun h =>
    hαn (mem_inner_of_centerQuotientHom_mem h)
  set a : Outer (K ⧸ Subgroup.center K) :=
    QuotientGroup.mk' (inner (K ⧸ Subgroup.center K)) ᾱ with ha
  have hap : a ^ p = 1 := by rw [ha, ← map_pow, hᾱp, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [ha, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hᾱn h
  rw [← orderOf_eq_prime hap ha1]
  exact orderOf_dvd_natCard a

theorem kd26e_exceptional_cases (t : StatedLieTag) (n P f : ℕ) :
    (t = .PSL ∧ n = 2 ∧ P = 3 ∧ f = 2) ∨ (t = .PSU ∧ n = 4 ∧ P = 3 ∧ f = 1) ∨
    (t = .POmegaOdd ∧ n = 3 ∧ P = 3 ∧ f = 1) ∨ (t = .G2 ∧ n = 0 ∧ P = 3 ∧ f = 1) ∨
    ∃ j : ℕ, (exceptionalOrders t n P f).1 * (exceptionalOrders t n P f).2 = 2 ^ j := by
  unfold exceptionalOrders
  split
  all_goals first
    | exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    | exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨4, rfl⟩)))

theorem kd26e_generic_cases (t : StatedLieTag) (n P f : ℕ) :
    (t = .PSL ∧ (genericOrders t n P f).1 * (genericOrders t n P f).2 = Nat.gcd n (P ^ f - 1)) ∨
    (t = .PSU ∧ (genericOrders t n P f).1 * (genericOrders t n P f).2 = Nat.gcd n (P ^ f + 1)) ∨
    (t = .E6 ∧ (genericOrders t n P f).1 * (genericOrders t n P f).2 = Nat.gcd 3 (P ^ f - 1)) ∨
    (t = .twistedE6 ∧
      (genericOrders t n P f).1 * (genericOrders t n P f).2 = Nat.gcd 3 (P ^ f + 1)) ∨
    (genericOrders t n P f).1 * (genericOrders t n P f).2 ∣ 4 := by
  cases t <;> simp [genericOrders]
  all_goals first
    | exact (Nat.gcd_dvd_left 2 _).trans (by norm_num)
    | exact Nat.gcd_dvd_left 4 _
    | (split_ifs <;> simp [Nat.gcd_dvd_left])

theorem kd26e_exceptional_pos (t : StatedLieTag) (n P f : ℕ) :
    0 < (exceptionalOrders t n P f).1 * (exceptionalOrders t n P f).2 := by
  unfold exceptionalOrders
  split <;> norm_num

theorem kd26e_table_ne_zero {t : StatedLieTag} {n P f : ℕ} (h : StatedLieAdmissible t n P f) :
    ((genericOrders t n P f).1 * (genericOrders t n P f).2) *
      ((exceptionalOrders t n P f).1 * (exceptionalOrders t n P f).2) ≠ 0 := by
  refine Nat.mul_ne_zero ?_ (kd26e_exceptional_pos t n P f).ne'
  rcases kd26e_generic_cases t n P f with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | h1
  · rw [h1]
    exact (Nat.gcd_pos_of_pos_left _ (by have := h.2.2.1; omega)).ne'
  · rw [h1]
    exact (Nat.gcd_pos_of_pos_left _ (by have := h.2.2.1; omega)).ne'
  · rw [h1]
    exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  · rw [h1]
    exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  · exact (Nat.pos_of_dvd_of_pos h1 (by norm_num)).ne'

theorem kd26e_tag {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : ∃ k : ℕ, m = p ^ k) (hpm : p ∣ m)
    (t : StatedLieTag) (n P f : ℕ)
    (h : m ∣ ((genericOrders t n P f).1 * (genericOrders t n P f).2) *
      ((exceptionalOrders t n P f).1 * (exceptionalOrders t n P f).2)) :
    (t = .PSL ∧ m ∣ Nat.gcd n (P ^ f - 1)) ∨ (t = .PSU ∧ m ∣ Nat.gcd n (P ^ f + 1)) ∨
    (t = .E6 ∧ m ∣ Nat.gcd 3 (P ^ f - 1)) ∨ (t = .twistedE6 ∧ m ∣ Nat.gcd 3 (P ^ f + 1)) ∨
    (p = 3 ∧ t = .PSL ∧ n = 2 ∧ P = 3 ∧ f = 2) ∨ (p = 3 ∧ t = .PSU ∧ n = 4 ∧ P = 3 ∧ f = 1) ∨
    (p = 3 ∧ t = .POmegaOdd ∧ n = 3 ∧ P = 3 ∧ f = 1) ∨
    (p = 3 ∧ t = .G2 ∧ n = 0 ∧ P = 3 ∧ f = 1) := by
  have hp3 : p ∣ 36 → p = 3 := fun hd => by
    have h4 : p ∣ 4 * 9 := by simpa using hd
    rcases (Nat.Prime.dvd_mul hp).1 h4 with h4 | h9
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4))) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        (hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h9))
  have hpd : p ∣ ((genericOrders t n P f).1 * (genericOrders t n P f).2) *
      ((exceptionalOrders t n P f).1 * (exceptionalOrders t n P f).2) := hpm.trans h
  obtain ⟨k, rfl⟩ := hm
  rcases kd26e_exceptional_cases t n P f with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨j, hj⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp3 (hpd.trans (by decide)), rfl, rfl, rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp3 (hpd.trans (by decide)), rfl, rfl, rfl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp3 (hpd.trans (by decide)), rfl, rfl, rfl, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hp3 (hpd.trans (by decide)), rfl, rfl, rfl, rfl⟩))))))
  · rw [hj] at h
    have hcop : Nat.Coprime (p ^ k) (2 ^ j) :=
      Nat.Coprime.pow k j ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hdvd := hcop.dvd_of_dvd_mul_right h
    rcases kd26e_generic_cases t n P f with ⟨rfl, hG⟩ | ⟨rfl, hG⟩ | ⟨rfl, hG⟩ | ⟨rfl, hG⟩ | hG
    · exact Or.inl ⟨rfl, hG ▸ hdvd⟩
    · exact Or.inr (Or.inl ⟨rfl, hG ▸ hdvd⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hG ▸ hdvd⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hG ▸ hdvd⟩)))
    · exfalso
      have h4 : p ∣ 2 ^ 2 := by simpa using hpm.trans (hdvd.trans hG)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))

private theorem qEps_true_card (q : TauCeti.PrimePower) :
    qEps true q.card = q.p ^ q.exponent - 1 := by
  simp [qEps, TauCeti.PrimePower.card_def]

private theorem qEps_false_card (q : TauCeti.PrimePower) :
    qEps false q.card = q.p ^ q.exponent + 1 := by
  simp [qEps, TauCeti.PrimePower.card_def]

private theorem kd26e_lieModel_twistedA {G : Type} [Group G] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    CFSG.Models.LieModel G .PSU (r + 1) q.p q.exponent := by
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA r q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA r q
  have h := CFSG.Models.lieModel_twistedA r q hv e
  rwa [hc, hf] at h

theorem kd26e_lie (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSmall : CFSG.AGLEmbedding.FixedThree.OutSmallLie)
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : IsPGroup p (Subgroup.center K)) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hout : p ∣ Nat.card (Outer (K ⧸ Subgroup.center K))) (d : TauCeti.ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    (∃ (n q : ℕ) (lin : Bool), IsLnEps (K ⧸ Subgroup.center K) n q lin ∧
        p ∣ Nat.gcd n (qEps lin q) ∧ Nat.card (Subgroup.center K) ∣ Nat.gcd n (qEps lin q)) ∨
    (∃ (q : ℕ) (lin : Bool), IsE6Eps (K ⧸ Subgroup.center K) q lin ∧ p = 3 ∧ 3 ∣ qEps lin q ∧
        Nat.card (Subgroup.center K) ∣ 3) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK
  have key : ∀ {t : StatedLieTag} {n P f : ℕ},
      CFSG.Models.LieModel (K ⧸ Subgroup.center K) t n P f →
      (t = .PSL ∧ Nat.card (Subgroup.center K) ∣ Nat.gcd n (P ^ f - 1)) ∨
      (t = .PSU ∧ Nat.card (Subgroup.center K) ∣ Nat.gcd n (P ^ f + 1)) ∨
      (t = .E6 ∧ Nat.card (Subgroup.center K) ∣ Nat.gcd 3 (P ^ f - 1)) ∨
      (t = .twistedE6 ∧ Nat.card (Subgroup.center K) ∣ Nat.gcd 3 (P ^ f + 1)) ∨
      (p = 3 ∧ t = .PSL ∧ n = 2 ∧ P = 3 ∧ f = 2) ∨ (p = 3 ∧ t = .PSU ∧ n = 4 ∧ P = 3 ∧ f = 1) ∨
      (p = 3 ∧ t = .POmegaOdd ∧ n = 3 ∧ P = 3 ∧ f = 1) ∨
      (p = 3 ∧ t = .G2 ∧ n = 0 ∧ P = 3 ∧ f = 1) := fun {t n P f} hmod =>
    kd26e_tag hp hp2 ⟨k, hk⟩ hpZ t n P f
      (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_table hGA hQ' hmod
        (kd26e_table_ne_zero hmod.1))
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    have hmod := CFSG.Models.lieModel_A r q hv e
    rcases key hmod with ⟨-, hd⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hn, hP, hf⟩ | ⟨-, h, -⟩ |
      ⟨-, h, -⟩ | ⟨-, h, -⟩
    · refine Or.inl ⟨r + 1, q.card, true, ⟨.lie ⟨.A r q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩, ?_, ?_⟩
      · rw [qEps_true_card]
        exact hpZ.trans hd
      · rw [qEps_true_card]
        exact hd
    · cases h
    · cases h
    · cases h
    · exfalso
      obtain rfl : r = 1 := by omega
      exact ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
        ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2
          (Or.inl ⟨rfl, Or.inr (Or.inr (by
            rw [TauCeti.PrimePower.card_def, hP, hf]; norm_num))⟩))
    · cases h
    · cases h
    · cases h
  | twistedA r q =>
    have hmod := kd26e_lieModel_twistedA r q hv e
    rcases key hmod with ⟨h, -⟩ | ⟨-, hd⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ |
      ⟨hp3, -, hn, hP, hf⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · cases h
    · refine Or.inl ⟨r + 1, q.card, false, ⟨.lie ⟨.twistedA r q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩, ?_, ?_⟩
      · rw [qEps_false_card]
        exact hpZ.trans hd
      · rw [qEps_false_card]
        exact hd
    · cases h
    · cases h
    · cases h
    · exfalso
      obtain rfl : r = 3 := by omega
      have hq3 : q.card = 3 := by rw [TauCeti.PrimePower.card_def, hP, hf]; norm_num
      exact hSmall.twistedA _ q hv hq3 ⟨e⟩ (hp3 ▸ hout)
    · cases h
    · cases h
  | B r q =>
    rcases CFSG.Models.lieModel_B r q hv e with hmod | hmod
    · exact absurd (key hmod) (by simp)
    · rcases key hmod with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
        ⟨hp3, -, hn, hP, hf⟩ | ⟨-, h, -⟩
      · cases h
      · cases h
      · cases h
      · cases h
      · cases h
      · cases h
      · exfalso
        obtain rfl : r = 3 := by omega
        have hq3 : q.card = 3 := by rw [TauCeti.PrimePower.card_def, hP, hf]; norm_num
        exact hSmall.b _ q hv hq3 ⟨e⟩ (hp3 ▸ hout)
      · cases h
  | C r q => exact absurd (key (CFSG.Models.lieModel_C r q hv e)) (by simp)
  | D r q => exact absurd (key (CFSG.Models.lieModel_D r q hv e)) (by simp)
  | twistedD r q => exact absurd (key (CFSG.Models.lieModel_twistedD r q hv e)) (by simp)
  | E6 q =>
    have hmod : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .E6 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩ e
    rcases key hmod with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hd⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
      ⟨-, h, -⟩ | ⟨-, h, -⟩
    · cases h
    · cases h
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        (hpZ.trans (hd.trans (Nat.gcd_dvd_left _ _)))
      have h3m : 3 ∣ Nat.card (Subgroup.center K) := hp3 ▸ hpZ
      refine Or.inr ⟨q.card, true, ⟨.lie ⟨.E6 q, hv⟩, rfl, ⟨e⟩⟩, hp3, ?_,
        hd.trans (Nat.gcd_dvd_left _ _)⟩
      rw [qEps_true_card]
      exact (Nat.dvd_gcd_iff.1 (h3m.trans hd)).2
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
  | E7 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .E7) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | E8 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .E8) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | F4 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .F4) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | G2 q =>
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hmod : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .G2 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag (t := .G2) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl, by rw [← TauCeti.PrimePower.card_def]; exact hq3⟩
        ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩ e
    rcases key hmod with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
      ⟨-, h, -⟩ | ⟨hp3, -, -, hP, hf⟩
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · exfalso
      have hq3' : q.card = 3 := by rw [TauCeti.PrimePower.card_def, hP, hf]; norm_num
      exact hSmall.g _ q hv hq3' ⟨e⟩ (hp3 ▸ hout)
  | twistedE6 q =>
    have hmod : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.twistedE6 q, hv⟩
        ⟨rfl, rfl⟩ e
    rcases key hmod with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hd⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
      ⟨-, h, -⟩ | ⟨-, h, -⟩
    · cases h
    · cases h
    · cases h
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        (hpZ.trans (hd.trans (Nat.gcd_dvd_left _ _)))
      have h3m : 3 ∣ Nat.card (Subgroup.center K) := hp3 ▸ hpZ
      refine Or.inr ⟨q.card, false, ⟨.lie ⟨.twistedE6 q, hv⟩, rfl, ⟨e⟩⟩, hp3, ?_,
        hd.trans (Nat.gcd_dvd_left _ _)⟩
      rw [qEps_false_card]
      exact (Nat.dvd_gcd_iff.1 (h3m.trans hd)).2
    · cases h
    · cases h
    · cases h
    · cases h
  | trialityD4 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := q.p)
      (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩ e))
      (by simp)
  | suzuki m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .twistedB2) (p := 2)
      (f := 2 * m + 1) ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩
      ⟨rfl, rfl⟩ e)) (by simp)
  | reeG2 m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .twistedG2) (p := 3)
      (f := 2 * m + 1) ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩
      ⟨rfl, rfl⟩ e)) (by simp)
  | reeF4 m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .twistedF4) (p := 2)
      (f := 2 * m + 1) ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩
      ⟨rfl, rfl⟩ e)) (by simp)
  | tits =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)

theorem kd26e_of_inputs (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpor : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hSmall : CFSG.AGLEmbedding.FixedThree.OutSmallLie) : KD26e := by
  intro K _ _ hK p hp hp2 hZ hpZ ⟨α, hα, hαn⟩
  have hperf : Group.IsPerfect K := ⟨hK.1.1⟩
  have hout : p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := kd26e_dvd_card_outer hp hα hαn
  obtain ⟨i, ⟨e⟩⟩ := hK.2
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exfalso
    have h1 : p ∣ Nat.card (Outer (alternatingGroup (Fin n))) := by
      rw [← Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact hout
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn p hp hp2 h1
  | sporadic s =>
    exfalso
    have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
    have h2 := hSpor (K ⧸ Subgroup.center K) hK.1.2 hnab s ⟨e⟩
    have hpos : 0 < Nat.card (Outer (K ⧸ Subgroup.center K)) := Nat.card_pos
    have h3 := Nat.le_of_dvd hpos hout
    have h4 := hp.two_le
    omega
  | lie d => exact kd26e_lie hGA hSmall hK.1 hp hp2 hZ hpZ hout d e

section Certificates

set_option linter.unusedSectionVars false


theorem kd26e_holds : KD26e :=
  kd26e_of_inputs CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.AGLEmbedding.FixedThree.outSmallLie_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA
