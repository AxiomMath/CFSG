module

public import Certificates.Certificate8044

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M23

open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.KC.Census

theorem m23_check :
    ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP),
    m23CheckW2 sG roots nodes cS wcs pfs = true :=
  Certificates.certificate8044

theorem m23_yCensus_cert :
    YCensus17 (⊤ : Subgroup ↥Blueprint.NativeSporadic.M23) (fun _ => False) := by
  obtain ⟨_, _, _, _, _, _, h⟩ := m23_check
  exact census_of_m23CheckW2 h

theorem sporadicCaseOdd_M23_of (hi : OuterAutomorphisms.inner ↥Blueprint.NativeSporadic.M23 = ⊤)
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .M23 :=
  sporadicCaseOdd_of_yCensus17 h32 h33 (m23AutModel_of hi) le_top yCensus_top_le_top
    m23_yCensus_cert

end CFSG.ComponentClassification.RankTwoSporadic.M23
