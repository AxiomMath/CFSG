module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcBorelQuot
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcTwE6Facts
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.RankThree.PartOne.KLC.EigTwE6
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.PartOne.KD4T.Certs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LieType.Steinberg.TwistedE6
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup


namespace TwE6

theorem not_dvd_card_units_of_pRank_le_one {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .twistedE6 2 f) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1) : ¬ p ∣ Nat.card kˣ := by
  intro hdvd
  obtain ⟨-, hf, -⟩ := hm.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hm
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hcard : Nat.card kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, hk]
    have h := Nat.sq_sub_sq (2 ^ f) 1
    rwa [one_pow] at h
  rw [hcard] at hdvd
  have hsec : ∃ e : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) ∧
      (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi e).eval ((2 ^ f : ℕ) : ℤ) := by
    rcases hp.dvd_mul.1 hdvd with h | h
    · refine ⟨2, Or.inr (Or.inl rfl), ?_⟩
      have e2 : (CFSG.RankThree.Chevalley.exhaustionPhi 2).eval ((2 ^ f : ℕ) : ℤ) =
          ((2 ^ f + 1 : ℕ) : ℤ) := by
        simp [CFSG.RankThree.Chevalley.exhaustionPhi]
      rw [e2]
      exact Int.natCast_dvd_natCast.2 h
    · refine ⟨1, Or.inl rfl, ?_⟩
      have e1 : (CFSG.RankThree.Chevalley.exhaustionPhi 1).eval ((2 ^ f : ℕ) : ℤ) =
          ((2 ^ f - 1 : ℕ) : ℤ) := by
        simp [CFSG.RankThree.Chevalley.exhaustionPhi, Nat.cast_sub hq1]
      rw [e1]
      exact Int.natCast_dvd_natCast.2 h
  obtain ⟨s, hs, hphi⟩ := hsec
  have h2 := CFSG.RankThree.PartOne.KLC.two_le_pRank_twistedE6_of_sector Nat.prime_two hf K hK σ
    hσ hp hp5 (by omega) hs hphi
  haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Finite.of_equiv S e.toEquiv
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e] at hrank
  exact absurd (h2.trans hrank) (by norm_num)

end TwE6

theorem leviSubAt_twistedE6 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .twistedE6 2 f) : LeviSubAt S := by
  obtain ⟨⟨-, hf, -⟩, k, _, _, hk, θ, hθq, ⟨e⟩⟩ := id hm
  have hk2 : Nat.card k = (2 ^ f) ^ 2 := hk
  haveI : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 2 * f) (by rw [hk2, ← pow_mul, mul_comm])
  have hθ : ∀ c, θ (θ c) = c :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.involutive_of_card hk2 hθq
  have h2f : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have hq : 2 ^ f = 2 ∨ 4 ≤ 2 ^ f := by
    rcases Nat.lt_or_ge f 2 with h | h
    · left
      obtain rfl : f = 1 := by omega
      rfl
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
  have h4 : 4 ≤ Nat.card k := by
    rw [hk2]
    nlinarith
  haveI : Finite (Module.End k (Fin CFSG.LieType.Steinberg.Minuscule.e6Data.d →₀ k)) :=
    Module.finite_of_finite k
  haveI : Finite ↥(fixedGroup k θ) := inferInstance
  have h := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e6tw hθ h4
    hk2 hθq e
  exact BQ.leviSubAt_of_borelQuotient h rfl (twistedDatum_bruhatExtras θ)
    (twistedDatum_rootGroupCommutators θ) (TwE6.commute_rankOne_of_cartan_eq_zero θ hθ)
    (fun p hp hp5 hr => TwE6.not_dvd_card_units_of_pRank_le_one hm hk2 hp hp5 hr)
    (fun C hC _ hA p hp hp5 _ hdvd =>
      TwE6.isPerfect_levi_twistedE6 θ hθ hk2 hθq hq C hC hA hp hp5 hdvd)
    Nat.prime_three (by decide) (by decide)
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank.two_le_pRank_three_twistedE6 hθ h4 e)
    (TwE6.three_dvd_card_rankOne θ hθ) (TwE6.center_rankOne_eq_bot θ hθ)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc
