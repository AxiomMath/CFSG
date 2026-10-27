module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift
public import CFSG.LieType.CurtisTits.Unitary
public import CFSG.LieType.CurtisTits.Spin
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.CurtisTits.Exceptional
public import CFSG.Timmesfeld.RankTwo.Presentation

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.LieType CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

theorem modelClauseZero_of_eq {t : StatedLieTag} {n p e : ℕ} {hp : p.Prime} {U : LieUniversal}
    (h : modelUniv t n p e hp = U)
    (hU : CFSG.IsQuasisimple U.K ∧
      CFSG.Blueprint.LieModel (U.K ⧸ Subgroup.center U.K) t n p e) :
    CFSG.Open.IsQuasisimple (modelUniv t n p e hp).K ∧
      CFSG.Blueprint.LieModel
        ((modelUniv t n p e hp).K ⧸ Subgroup.center (modelUniv t n p e hp).K) t n p e := by
  subst h
  exact ⟨open_isQuasisimple hU.1, hU.2⟩

theorem modelClauseZero : ModelClauseZero := by
  intro t n p e hp hFT hadm
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    by_cases hm : m = 1
    · subst hm
      exact modelClauseZero_sl2 p e hp hadm
    · have hm2 : 2 ≤ m := by have := hadm.2.2.1; omega
      exact modelClauseZero_of_eq rfl
        ⟨SpecialLinear.isQuasisimple m (GaloisField p e) hm2,
          Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
            SpecialLinear.statedClassicalModel_center_quotient m (GaloisField p e) hadm hcard⟩⟩
  | PSU =>
    have hcard2 : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e he
    have h : modelUniv .PSU n p e hp =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * e)) p e) n,
          Unitary.rootDatum hcard2 n⟩ := by
      simp only [modelUniv, lieUniversal, he, ↓reduceDIte]
    exact modelClauseZero_of_eq h (curtisTitsConclusion_unitary.{0} hadm hcard2).1.2
  | PSp =>
    exact modelClauseZero_of_eq rfl
      ⟨Symplectic.isQuasisimple_of_admissible n (GaloisField p e) hadm hcard,
        Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
          Symplectic.statedClassicalModel_center_quotient n (GaloisField p e) hadm hcard⟩⟩
  | POmegaOdd =>
    exact modelClauseZero_of_eq rfl (curtisTitsConclusion_spinOdd.{0} hadm hcard).1.2
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    have h : modelUniv .POmegaPlus n p e hp =
        ⟨spinGroup (quadPlus n (GaloisField p e)), plusDatum n (GaloisField p e) hn⟩ := by
      simp only [modelUniv, lieUniversal, hn, ↓reduceDIte]
    exact modelClauseZero_of_eq h (curtisTitsConclusion_spinPlus.{0} hadm hcard hn).1.2
  | POmegaMinus =>
    exact modelClauseZero_of_eq rfl (curtisTitsConclusion_spinMinus.{0} (minusCoeffs_irr p e) hadm hcard).1.2
  | G2 =>
    obtain ⟨-, -, hn0, hq⟩ := hadm
    subst hn0
    exact modelClauseZero_of_eq rfl
      ⟨Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (GaloisField p e) (hcard ▸ hq),
        Timmesfeld.lieModel_G2_quotient hp he hq hcard⟩
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact modelClauseZero_of_eq rfl (curtisTitsConclusion_f4.{0} p e hadm).1.2
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact modelClauseZero_of_eq rfl (curtisTitsConclusion_e6.{0} p e hadm).1.2
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact modelClauseZero_of_eq rfl (curtisTitsConclusion_e7.{0} p e hadm).1.2
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact modelClauseZero_of_eq rfl (curtisTitsConclusion_e8.{0} p e hadm).1.2
  | twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact modelClauseZero_of_eq rfl (curtisTitsConclusion_twistedE6.{0} p e hadm).1.2
  | trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
      rw [GaloisField.card p (3 * e) (by omega), pow_mul']
    have hσq : ∀ c : GaloisField p (3 * e), iterateFrobenius (GaloisField p (3 * e)) p e c =
        c ^ p ^ e := fun c => iterateFrobenius_def p e c
    have hq2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    exact modelClauseZero_of_eq rfl
      ⟨Steinberg.TwistedD4.twistedGroup_isQuasisimple_of_card hq2 hK hσq,
        Timmesfeld.lieModel_twistedD4_quotient hp he hK _ hσq⟩
  | twistedB2 => exact hFT.elim
  | twistedG2 => exact hFT.elim
  | twistedF4 => exact hFT.elim
  | Tits => exact hFT.elim

end CFSG.ClassicalInvolution.ModelFacts
