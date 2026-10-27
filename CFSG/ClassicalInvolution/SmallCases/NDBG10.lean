module

public import CFSG.ClassicalInvolution.SmallCases.NDBG9Main
public import CFSG.ClassicalInvolution.SmallCases.NDBS1Exo
public import CFSG.ClassicalInvolution.SmallCases.NDBS1Main
import CFSG.ClassicalInvolution.Asc77.AscBSD4
import CFSG.ClassicalInvolution.Asc77.AscBSD10
import CFSG.ClassicalInvolution.Asc77.AscBSE8
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

theorem bootNoTripleD_of_coverXW (hcov : BootShapeCoverX p f)
    (hexo : Asc77.FrameExistsOnE p f (ExoticNoTwinPred p f)) : Disconnected.BootNoTripleD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  refine S1.exact_p1_of_frames hnab hp2 hq hz hBelow hconn fun L hL w hw hnot => ?_
  have e := conjClass_eq_of_mem hL
  rw [← e] at hconn hdata hT hnot ⊢
  rcases hcov G hnab hp2 hq L w hw hBelow hconn hdata hT with hs | hs | hs | hs
  · exact chainFrames_noTriple G hnab hp2 hq L w hw hBelow hconn ⟨hs, hT⟩
  · exact twinFrames_weak G hnab hp2 hq L w hw hBelow hconn hs
  · exact absurd hs hnot
  · exact hexo G hnab hp2 hq L w hw hBelow hconn hs

end CFSG.ClassicalInvolution.NDB
