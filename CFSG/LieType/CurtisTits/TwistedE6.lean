module

public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.CurtisTits.ExceptionalModel
public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public section

namespace CFSG.LieType.CurtisTits

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

universe w

variable (p f : ℕ) [Fact p.Prime]

private theorem card_galoisField_two_mul (hf : 1 ≤ f) :
    Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
  rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]

theorem isQuasisimple_twistedE6 (hf : 1 ≤ f) : IsQuasisimple (twistedE6Group p f) := by
  have hcard := card_galoisField_two_mul p f hf
  refine fixedGroup_isQuasisimple_of_four_le_card (frobQ p f) (frobQ_frobQ p f hf) ?_
  rw [hcard]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have : 2 ≤ p ^ f := le_trans hp (Nat.le_self_pow (by omega) p)
  nlinarith

theorem curtisTitsConclusion_twistedE6_of_surjective (hadm : StatedLieAdmissible .twistedE6 0 p f)
    (φ : twistedE6Group p f →*
      ↥⁅twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f),
        twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f)⁆)
    (hφ : Function.Surjective φ) (hφ1 : ∃ x, φ x ≠ 1) :
    CurtisTitsConclusion.{w} (twistedE6Datum p f) .twistedE6 0 p f :=
  have hf : 1 ≤ f := hadm.2.1
  curtisTitsConclusion_of
    (twistedDatum_isCTGroupDatum (frobQ p f) (frobQ_frobQ p f hf)
      (iSup_twistedDatum_rootGroup (frobQ p f) (frobQ_frobQ p f hf)))
    (twistedDatum_steinbergExtras (frobQ p f) (frobQ_frobQ p f hf))
    (by change 0 < 4; norm_num) (isQuasisimple_twistedE6 p f hf)
    (Or.inr (Or.inl ⟨rfl, by decide, hadm,
      twistedChevalleyModel_of_surjective (isQuasisimple_twistedE6 p f hf)
        (card_galoisField_two_mul p f hf) (frobQ p f) (frobQ_apply p f) φ hφ hφ1
        (MulEquiv.refl _)⟩))

end CFSG.LieType.CurtisTits
