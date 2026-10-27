module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.S3Kit
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F16
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F17
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F18a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F18b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F18c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F18d
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F19
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F110

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem facts_of_model
    (m : G23Model G) : (frameOf m).Facts m.L := by
  obtain ⟨X⟩ := g23lctx_exists m
  obtain ⟨h11, h12, h13, h14, h15⟩ := s3_facts m
  exact ⟨h11, h12, h13, h14, h15, X.fact16, X.fact17,
    ⟨X.fact18_1, X.fact18_2, X.fact18_3 h14, X.fact18_4, X.fact18_5⟩, X.fact19 h11 h14,
    X.fact110⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
