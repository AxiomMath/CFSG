module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStatement412

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem harris412_of (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (h46c : Harris46cInput) (h46d : Harris46dInput) (h46e : Harris46eOddInput)
    (h46g : Harris46gInput) : Harris412Statement := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs
  have hd := h46d X hnonab hK hcat t L p f S w z V i j hs i j
  have hg := h46g X hnonab hK hcat t L p f S w z V i j hs i j
  exact
    { layerIn_centralizer := hs.lemma46a.1
      layerIn_layer_centralizer := hs.lemma46a.2
      betaBar_mem := hs.lemma46b.1
      sylow_centralizer := hs.lemma46b.2
      lemma46c := h46c X hnonab hK hcat t L p f S w z V i j hs i j
      layer_eq_commutator := hs.layer_eq_commutator hd hg
      lemma46d := hd
      oddCore_KBar := h46e X hnonab hK hcat t L p f S w z V i j hs i j
      commutator_conj_ne_bot := hs.lemma46e
      pCore_sup_le := hs.lemma46f.1
      pCore_inf_centralizer := hs.pCore_inf_centralizer_tBar
      pCore_eq := ⟨hg.1, hg.2.1⟩
      pCore_shape := hg.2.2.1
      pCore_sup_shape := hs.lemma46f.2.1
      oddGenerated_le := hg.2.2.2
      KBar_lt_layer := hs.KBar_lt_layer hg
      of_semidihedral := hs.of_semidihedral hFC hKC hg
      of_dihedral := hs.of_dihedral hFC hKC }

end CFSG.ComponentClassification.HarrisLit
