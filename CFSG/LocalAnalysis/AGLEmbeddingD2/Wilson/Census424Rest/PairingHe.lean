module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeKFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.McL

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21
  Subgroup Equiv
open CFSG.AGLEmbeddingD2.Wilson.Census219


theorem he_dichotomy {X : Type} [Group X] [Finite X] (e : X ≃* heP)
    (c : X) (hc3 : orderOf c = 3) :
    CFSG.IsQuasisimple (centralizer ({c} : Set X)) ∨ Nat.card (centralizer ({c} : Set X)) = 504 := by
  have hord : orderOf ((e c : heP) : Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc3]
  rcases three_conj_cases (e c).2 hord with ⟨c', hc', hcx⟩ | ⟨c', hc', hcx⟩
  · left
    let φ : X ≃* heP := e.trans (MulAut.conj (⟨c', hc'⟩ : heP)⁻¹)
    have hφ : φ c = heY := by
      apply Subtype.ext
      show c'⁻¹ * ((e c : heP) : Perm (Fin 8330)) * c' = bOf heThreeWordsA
      rw [hcx]
      group
    obtain ⟨-, ⟨e'⟩, -⟩ := he_layer
    have hq : CFSG.IsQuasisimple ↥(centralizer ({heY} : Set heP)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm heTc_spec.2.1
    let ε : centralizer ({c} : Set X) ≃* centralizer ({heY} : Set heP) :=
      (centralizerEquivOfMulEquiv φ c).trans (MulEquiv.subgroupCongr (by rw [hφ]))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ε.symm hq
  · right
    let φ : X ≃* heP := e.trans (MulAut.conj (⟨c', hc'⟩ : heP)⁻¹)
    have hφ : (φ c : Perm (Fin 8330)) = bOf heThreeWordsB := by
      show c'⁻¹ * ((e c : heP) : Perm (Fin 8330)) * c' = bOf heThreeWordsB
      rw [hcx]
      group
    calc Nat.card ↥(centralizer ({c} : Set X))
        = Nat.card ↥((centralizer ({c} : Set X)).map φ.toMonoidHom) :=
          (Subgroup.card_map_of_injective φ.injective).symm
      _ = Nat.card ↥(centralizer ({φ c} : Set heP)) := by
          rw [Proving.centralizer_map_mulEquiv_wilson φ c]
      _ = Nat.card ↥(centralizerIn heP (φ c : Perm (Fin 8330))) := card_centralizer_heP _
      _ = 504 := by rw [hφ]; exact card_cent_B

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
