module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.MainBAssembly
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelMap
public import CFSG.ClassicalInvolution.Phan.PhanDn.SpinModel
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

@[expose] def QTwoOmegaModelsD : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] [Algebra (GaloisField 2 1) K]
    (E : QuadExt (GaloisField 2 1) K (unitaryInvolution K 2 1)), Nat.card K = 4 →
    ∀ m : ℕ, 3 ≤ m → Nonempty (QTwoModelD K (m + 1)
      ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))

private theorem exists_omegaModel (h : QTwoOmegaModelsD) (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK4 : Nat.card K = 4) {m : ℕ} (hm : 4 ≤ m) :
    ∃ (A : Algebra (GaloisField 2 1) K),
      letI := A
      ∃ E : QuadExt (GaloisField 2 1) K (unitaryInvolution K 2 1),
        Nonempty (QTwoModelD K m
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E m))) := by
  have hF : Nat.card (GaloisField 2 1) = 2 ^ 1 := by
    simpa using GaloisField.card 2 1 one_ne_zero
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK4
  let A : Algebra (GaloisField 2 1) K := Classical.choice (Aniso.nonempty_algebra hF hK)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact
    letI := A
    let E : QuadExt (GaloisField 2 1) K (unitaryInvolution K 2 1) :=
      quadExt_of_card_of_char_two 1 hF hK
    ⟨A, E, h K E hK4 k (by omega)⟩

theorem qTwoSpinModelsD_of_omegaModels (h : QTwoOmegaModelsD) : QTwoSpinModelsD := by
  constructor
  · intro K _ _ _ hK4 m hm he
    obtain ⟨A, E, ⟨d⟩⟩ := exists_omegaModel h K hK4 hm
    exact
      letI := A
      ⟨d.map (omegaEquivSpinPlus E he (by omega))⟩
  · intro K _ _ _ hK4 m hm ho b c hirr
    obtain ⟨A, E, ⟨d⟩⟩ := exists_omegaModel h K hK4 hm
    exact
      letI := A
      ⟨d.map (omegaEquivSpinMinus E ho hm hirr)⟩

theorem ghnsMainBQTwo_of_omegaModels (h : QTwoOmegaModelsD) : GHNSMainBQTwo :=
  ghnsMainBQTwo_of_spinModels (qTwoSpinModelsD_of_omegaModels h)

end CFSG.ClassicalInvolution.PhanDn.QTwo
