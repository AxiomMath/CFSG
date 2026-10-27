module

public import CFSG.HardMathSupport.Dickson.Bal207.Rank
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.Assembly.LowTwoRank
  CFSG.Blueprint.Multiplier CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem centerAux_exceptional_two (t : StatedLieTag) (n f : ℕ) :
    (exceptionalOrders t n 2 f).1 ∣ 4 ∧ (exceptionalOrders t n 2 f).2 ∣ 4 := by
  unfold exceptionalOrders
  split <;> first | omega | (norm_num; done) | simp_all

theorem centerAux_torsBound_eq_one {r : ℕ} {t : StatedLieTag} {n f : ℕ} (hr : r = 3 ∨ r = 5)
    (hg : ¬ r ∣ (genericOrders t n 2 f).1) : torsBound r t n 2 f = 1 := by
  have h2 := genericOrders_snd_le t n 2 f
  have he := centerAux_exceptional_two t n f
  have hnd : ∀ x, x ∣ 4 → ¬ r ∣ x := by
    intro x hx hrx
    have h1 := Nat.dvd_trans hrx hx
    rcases hr with rfl | rfl <;> omega
  have hg2 : ¬ r ∣ (genericOrders t n 2 f).2 := by
    intro h
    have h1 := Nat.le_of_dvd h2.1 h
    rcases hr with rfl | rfl <;> omega
  unfold torsBound
  rw [tors_of_not_dvd hg, tors_of_not_dvd hg2, tors_of_not_dvd (hnd _ he.1),
    tors_of_not_dvd (hnd _ he.2)]

theorem centerAux_coprime_of_card_le_one {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : Nat.card {z : Subgroup.center K // z ^ p = 1} ≤ 1) :
    Nat.Coprime p (Nat.card (Subgroup.center K)) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  haveI := Fact.mk hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have h1 : 1 < Nat.card {z : Subgroup.center K // z ^ p = 1} := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨⟨z, hz ▸ pow_orderOf_eq_one z⟩, ⟨1, one_pow p⟩,
      fun h2 => hz1 (congrArg Subtype.val h2)⟩⟩
  omega

theorem centerAux_not_three_dvd_gcd {a x : ℕ} (ha : a = 2 ∨ a = 4) : ¬ 3 ∣ Nat.gcd a x := by
  intro h
  have h1 := Nat.dvd_trans h (Nat.gcd_dvd_left a x)
  rcases ha with rfl | rfl <;> omega

theorem bal207RankCenter_of_griess (hGA : GriessAllModelsStatement) : Bal207RankCenter := by
  intro p K _ _ hp hq hK hU
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  have key : ∃ (t : StatedLieTag) (n f : ℕ),
      CFSG.Models.LieModel (TauCeti.CFSGIndex.lie d).Group t n 2 f ∧ (p = 3 ∨ p = 5) ∧
        ¬ p ∣ (genericOrders t n 2 f).1 := by
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | B r q =>
      obtain ⟨rfl, h⟩ := hd
      have hp2 : q.p = 2 := by rcases h with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
      rcases CFSG.Models.lieModel_B r q hv (MulEquiv.refl _) with hL | hL
      · rw [hp2] at hL
        refine ⟨.PSp, r, q.exponent, hL, Or.inl rfl, ?_⟩
        simp only [genericOrders]
        exact centerAux_not_three_dvd_gcd (Or.inl rfl)
      · rw [hp2] at hL
        exact absurd hL.1.2.2.2 (by simp)
    | twistedA r q =>
      obtain ⟨rfl, h⟩ := hd
      rcases h with ⟨hq, h3⟩ | ⟨hq, hr⟩
      · have hp2 : q.p = 2 := by rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
        have hL := CFSG.Models.lieModel_twistedA r q hv (MulEquiv.refl _)
        have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := by
          rw [← hp2]
          exact TauCeti.LieTypeIndex.characteristic_twistedA r q
        rw [hc] at hL
        refine ⟨.PSU, r + 1, _, hL, Or.inl rfl, ?_⟩
        simp only [genericOrders]
        intro h
        exact h3 (Nat.dvd_trans h (Nat.gcd_dvd_left _ _))
      · exact absurd ⟨rfl, ⟨⟨.twistedA r q, hv⟩, ⟨hr, hq⟩, ⟨e⟩⟩⟩ hU
    | D r q =>
      obtain ⟨rfl, h⟩ := hd
      have hp2 : q.p = 2 := by
        rcases h with ⟨⟨h, -⟩ | ⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
      have hL := CFSG.Models.lieModel_D r q hv (MulEquiv.refl _)
      rw [hp2] at hL
      refine ⟨.POmegaPlus, r, q.exponent, hL, Or.inl rfl, ?_⟩
      have heven : Even (2 ^ q.exponent) := (Nat.even_pow' q.exponent_pos.ne').mpr even_two
      simp only [genericOrders, if_pos heven]
      norm_num
    | twistedD r q =>
      obtain ⟨rfl, h, -⟩ := hd
      have hp2 : q.p = 2 := by rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
      have hL := CFSG.Models.lieModel_twistedD r q hv (MulEquiv.refl _)
      rw [hp2] at hL
      refine ⟨.POmegaMinus, r, q.exponent, hL, Or.inl rfl, ?_⟩
      simp only [genericOrders]
      exact centerAux_not_three_dvd_gcd (Or.inr rfl)
    | trialityD4 q =>
      obtain ⟨rfl, hp2, -⟩ := hd
      have hL := lieModel_lie (t := .trialityD4) ⟨q.prime_p, q.exponent_pos, rfl⟩
        ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩
      rw [hp2] at hL
      exact ⟨_, _, _, hL, Or.inl rfl, by simp [genericOrders]⟩
    | G2 q =>
      obtain ⟨rfl, hp2, hf⟩ := hd
      have h3q : 3 ≤ q.p ^ q.exponent := by rw [hp2, hf]; norm_num
      have hL := lieModel_lie (t := .G2) ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩
        ⟨rfl, rfl⟩
      rw [hp2] at hL
      exact ⟨_, _, _, hL, Or.inl rfl, by simp [genericOrders]⟩
    | F4 q =>
      obtain ⟨rfl, hp2, -⟩ := hd
      have hL := lieModel_lie (t := .F4) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩
        ⟨rfl, rfl⟩
      rw [hp2] at hL
      exact ⟨_, _, _, hL, Or.inl rfl, by simp [genericOrders]⟩
    | tits =>
      have hL := lieModel_lie (t := .Tits) (p := 2) (f := 1)
        ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩
      refine ⟨_, _, _, hL, hd, ?_⟩
      simp only [genericOrders]
      exact hp.not_dvd_one
    | suzuki m =>
      obtain ⟨rfl, rfl⟩ := hd
      have hL := lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * 2 + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨2, rfl⟩, by omega⟩ ⟨.suzuki 2, hv⟩ ⟨rfl, rfl⟩
      exact ⟨_, _, _, hL, Or.inr rfl, by simp [genericOrders]⟩
    | reeF4 m =>
      obtain ⟨rfl, rfl⟩ := hd
      have hL := lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * 2 + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨2, rfl⟩, by omega⟩ ⟨.reeF4 2, hv⟩ ⟨rfl, rfl⟩
      exact ⟨_, _, _, hL, Or.inr rfl, by simp [genericOrders]⟩
    | A r q => exact absurd hd (by simp [Bal207Index])
    | C r q => exact absurd hd (by simp [Bal207Index])
    | E6 q => exact absurd hd (by simp [Bal207Index])
    | E7 q => exact absurd hd (by simp [Bal207Index])
    | E8 q => exact absurd hd (by simp [Bal207Index])
    | twistedE6 q => exact absurd hd (by simp [Bal207Index])
    | reeG2 m => exact absurd hd (by simp [Bal207Index])
  obtain ⟨t, n, f, hm, hp35, hg⟩ := key
  exact centerAux_coprime_of_card_le_one hp
    ((center_torsion_le hGA hq e hm hp).trans (centerAux_torsBound_eq_one hp35 hg).le)

theorem bal207Rank_of_griess (hGA : GriessAllModelsStatement) (hSyl : Bal207RankSyl)
    (hU : Bal207RankU62) : Bal207Rank :=
  bal207Rank_of_parts hSyl (bal207RankCenter_of_griess hGA) hU

end CFSG.HardMathSupport.Dickson.Bal207
