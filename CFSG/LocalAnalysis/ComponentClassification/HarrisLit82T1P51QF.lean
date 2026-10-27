module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QMain

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def FamF (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (n p f : ℕ), p.Prime → p ≠ 2 →
    Blueprint.LieModel X t n p f → p ^ f ≠ 3 → ∀ z : X, orderOf z = 2 →
    ∀ P : Subgroup X, P ≤ centralizer ({z} : Set X) → z ∈ P → Nat.card P = 8 →
      (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
        ∀ k ∈ K, ∀ g ∈ P, (k : X) * g = g * k) →
      ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧ ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = z) ∧
        ¬ ∀ q ∈ P, q * q = 1

theorem famQuat_of_famF {t : StatedLieTag} (h : FamF t) : FamQuat t :=
  fun X _ _ _ n p f hp hp2 hX hq z hz Q hQC hzQ hnc huniq h8 hK =>
    (h X n p f hp hp2 hX hq z hz Q hQC hzQ h8 hK).1 ⟨hnc, huniq⟩

theorem famF_of_char_two {t : StatedLieTag}
    (ht : ∀ (X : Type) [Group X] (n p f : ℕ), Blueprint.LieModel X t n p f → p = 2) :
    FamF t :=
  fun X _ _ _ n p f _ hp2 hX => absurd (ht X n p f hX) hp2

theorem harris82Lemma51Quat_of_famF (hPSL : FamF .PSL) (hPSU : FamF .PSU) (hPSp : FamF .PSp)
    (hOdd : FamF .POmegaOdd) (hPlus : FamF .POmegaPlus) (hMinus : FamF .POmegaMinus)
    (hG2 : FamF .G2) (hF4 : FamF .F4) (hE6 : FamF .E6) (hE7 : FamF .E7) (hE8 : FamF .E8)
    (hTE6 : FamF .twistedE6) (hD4 : FamF .trialityD4) (hTG2 : FamF .twistedG2) :
    Harris82Lemma51Quat :=
  harris82Lemma51Quat_of_famQuat (famQuat_of_famF hPSL) (famQuat_of_famF hPSU)
    (famQuat_of_famF hPSp) (famQuat_of_famF hOdd) (famQuat_of_famF hPlus)
    (famQuat_of_famF hMinus) (famQuat_of_famF hG2) (famQuat_of_famF hF4) (famQuat_of_famF hE6)
    (famQuat_of_famF hE7) (famQuat_of_famF hE8) (famQuat_of_famF hTE6) (famQuat_of_famF hD4)
    (famQuat_of_famF hTG2)

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
