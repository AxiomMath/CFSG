module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D25
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4H1
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L28
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain
public import CFSG.LocalAnalysis.ComponentClassification.Asc76HallDihedral
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D16
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D24

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

theorem thm5Flat_of_inputs (h22 : Asc76Lemma22) (h27 : L26.Asc76Lemma27) (h1 : Asc76Theorem1)
    (hBF : Asc76X.BenderFacts) (hgold : CFSG.Goldschmidt.TopStatement)
    (hHall : HallDihedralFusion) (hB3 : B3Conclusion) : Thm5Flat := by
  apply thm5Flat_of
  intro G _ _ Ω S hM
  by_cases hconn : ∀ K ∈ Ω, ∀ J ∈ Ω, J ∈ dStarComp Ω K
  ·
    have hdis := hM.not_connected_commGraph h22 hconn
    have hZ2 : ∀ S' : Subgroup G, IsSylowOf 2 S' ⊤ →
        ∀ x, IsZInv Ω x → x ∈ normalizer (sec4W Ω S' : Set G) → x ∈ sec4W Ω S' :=
      fun S' hS' x hx hxN => (hM.of_sylow hS').mem_sec4W_of_isZInv_of_not_connected h22
        ((hM.of_sylow hS').not_connected_commGraph h22 hconn) hx hxN
    exact hM.not_stronglyClosed hgold (hM.sec4W_stronglyClosed h22 hdis
      fun v hv g hvg => hM.omegaOne_stronglyClosed h22 hB3 hconn hZ2 hv hvg)
  ·
    push Not at hconn
    exact hM.false_of_not_conn h22 h27 h1 hBF hHall hconn

theorem thm5Flat_of_hall_of_b3
    (hHall : HallDihedralFusion) (hB3 : B3Conclusion) : Thm5Flat :=
  thm5Flat_of_inputs (Asc76.asc76Lemma22 AschbacherTheorem3.theorem_3_holds) L26.asc76Lemma27
    (Asc76X.asc76Theorem1_of_lemma28 Asc76.asc76Lemma28) Asc76X.benderFacts
    CFSG.Goldschmidt.topStatement hHall hB3

theorem thm5Flat_of_b3
    (hB3 : B3Conclusion) : Thm5Flat :=
  thm5Flat_of_hall_of_b3 Asc76X.HallDihedral.hallDihedralFusion hB3

end CFSG.ComponentClassification.Asc76.Sec4
