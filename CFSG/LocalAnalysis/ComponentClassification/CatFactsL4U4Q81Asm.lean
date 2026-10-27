module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step8b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46g
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitQI46

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

theorem harris47Q81Input_of
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hKG : AutPSL2SylowInput) (hKF : AutPSL2FusionInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h219 : Harris82Lemma219Input) (hSD : Harris46SemidihedralInput)
    (hGO : TBLit.GriessMultipliersOdd) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hT1 : Harris82Theorem1KProper) (h34 : Harris81Lemma34Input)
    (hC3 : L4U4InvolutionCentralizerFact) (hCI : GSLit.ClassicalInvolutionInput)
    (hP2 : Harris81Lemma33Simple) (hT2 : Harris82Theorem2SLTwo) (hF : L4U4ThreeInvolutionFacts) :
    Harris47Q81Input := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs hp hf i' j' J hJ htype
  subst hp hf
  have hQI := harris46Quaternion_of_classical hSch hFC hKC hCI
  have hQ : ∀ a b : ℕ, IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ a * z ^ b))) →
      (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ a * z ^ b))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ a * z ^ b)))) .PSL 4 3 1 ∨
        Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ a * z ^ b))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ a * z ^ b)))) .PSU 4 3 1) →
      hs.setup.Q81Data a b := fun a b hE hm =>
    hs.setup.q81Data_of hnonab hK hcat hSch hFC hKC hKG hGO hT1 hC3 a b
      (harris46c_of hFC hKC hSch h219 hSD X hnonab hK hcat t L 3 4 S w z V i j hs a b)
      (harris46d_of hFC hKC hSch h219 hSD hGO hGC hCI h34 X hnonab hK hcat t L 3 4 S w z V i j
        hs a b)
      (harris46eOdd_of hFC hKC hSch h219 hSD hGO hGC hCI h34 X hnonab hK hcat t L 3 4 S w z V
        i j hs a b)
      (harris46g_of hFC hKC hSch hQI X hnonab hK hcat t L 3 4 S w z V i j hs a b) hE hm
  obtain ⟨hE, hm, -⟩ := Standing.Setup42.Lemma47.layer_of_isPComponent_four
    (by norm_num : (3 : ℕ) ≠ 2) (harris46d_of hFC hKC hSch h219 hSD hGO hGC hCI h34 X hnonab hK
      hcat t L 3 4 S w z V i j hs i' j') hJ htype
  exact hs.false_of_q81Data hnonab hK hcat hCI h219 hP2 hGO hGC hT2 hF hFC hKC hKG hKF hQ
    (hQ i' j' hE hm) (fun c => Standing.not_conj_t_of_isOfType hs.standing htype c)

end CFSG.ComponentClassification.HarrisLit
