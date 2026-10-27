module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Witness

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def DichLieDefAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f → ℓ = 3 →
      3 ∣ Nat.card K → DichThreeLieAt K

@[expose] def DichLieCrossAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f → ℓ ≠ 3 →
      3 ∣ Nat.card K → DichThreeLieAt K

@[expose] def HeisDichLieCrossAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f → ℓ ≠ 3 →
      3 ∣ Nat.card K → HeisDichAt K

theorem DichLieCrossAt.heis {t : StatedLieTag} (h : DichLieCrossAt t) : HeisDichLieCrossAt t :=
  fun K _ _ hs hnab n ℓ f hadm hmodel hℓ h3 => (h K hs hnab n ℓ f hadm hmodel hℓ h3).2

theorem dichThreeLieAt_of_tags (hDef : ∀ t, DichLieDefAt t) (hCross : ∀ t, DichLieCrossAt t)
    (K : Type) [Group K] [Finite K] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (t : StatedLieTag) (n ℓ f : ℕ) (hadm : StatedLieAdmissible t n ℓ f)
    (hmodel : LieModel K t n ℓ f) (h3 : 3 ∣ Nat.card K) : DichThreeLieAt K := by
  by_cases hℓ : ℓ = 3
  · exact hDef t K hs hnab n ℓ f hadm hmodel hℓ h3
  · exact hCross t K hs hnab n ℓ f hadm hmodel hℓ h3

theorem dichThreeLie_of_tags (hDef : ∀ t, DichLieDefAt t) (hCross : ∀ t, DichLieCrossAt t) :
    DichThreeLie := by
  intro K _ _ hs hnab t n ℓ f hadm hmodel h3
  exact (dichThreeLieAt_of_tags hDef hCross K hs hnab t n ℓ f hadm hmodel h3).dichThreeAt

theorem heisDichThreeLie_of_tags (hDef : ∀ t, DichLieDefAt t)
    (hCross : ∀ t, HeisDichLieCrossAt t) : HeisDichThreeLie := by
  intro K _ _ hs hnab t n ℓ f hadm hmodel h3
  by_cases hℓ : ℓ = 3
  · exact (hDef t K hs hnab n ℓ f hadm hmodel hℓ h3).2
  · exact hCross t K hs hnab n ℓ f hadm hmodel hℓ h3

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
