module

public import CFSG.LieType.Chevalley.RootOps.Cert.E7Tab
public import CFSG.LieType.Chevalley.RootOps.Cert.E7Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.E7Conj0
public import CFSG.LieType.Chevalley.RootOps.Cert.E7Conj42
public import CFSG.LieType.Chevalley.RootOps.Cert.E7Conj84
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem e7_conjRange_all : conjRange .E7 0 126 = true := by
  have h0 : conjRange .E7 0 2 = true := e7_conjRange_0_2
  have h1 : conjRange .E7 0 4 = true :=
    conjRange_trans (by norm_num) (by norm_num) h0 e7_conjRange_2_4
  have h2 : conjRange .E7 0 6 = true :=
    conjRange_trans (by norm_num) (by norm_num) h1 e7_conjRange_4_6
  have h3 : conjRange .E7 0 8 = true :=
    conjRange_trans (by norm_num) (by norm_num) h2 e7_conjRange_6_8
  have h4 : conjRange .E7 0 10 = true :=
    conjRange_trans (by norm_num) (by norm_num) h3 e7_conjRange_8_10
  have h5 : conjRange .E7 0 12 = true :=
    conjRange_trans (by norm_num) (by norm_num) h4 e7_conjRange_10_12
  have h6 : conjRange .E7 0 14 = true :=
    conjRange_trans (by norm_num) (by norm_num) h5 e7_conjRange_12_14
  have h7 : conjRange .E7 0 16 = true :=
    conjRange_trans (by norm_num) (by norm_num) h6 e7_conjRange_14_16
  have h8 : conjRange .E7 0 18 = true :=
    conjRange_trans (by norm_num) (by norm_num) h7 e7_conjRange_16_18
  have h9 : conjRange .E7 0 20 = true :=
    conjRange_trans (by norm_num) (by norm_num) h8 e7_conjRange_18_20
  have h10 : conjRange .E7 0 22 = true :=
    conjRange_trans (by norm_num) (by norm_num) h9 e7_conjRange_20_22
  have h11 : conjRange .E7 0 24 = true :=
    conjRange_trans (by norm_num) (by norm_num) h10 e7_conjRange_22_24
  have h12 : conjRange .E7 0 26 = true :=
    conjRange_trans (by norm_num) (by norm_num) h11 e7_conjRange_24_26
  have h13 : conjRange .E7 0 28 = true :=
    conjRange_trans (by norm_num) (by norm_num) h12 e7_conjRange_26_28
  have h14 : conjRange .E7 0 30 = true :=
    conjRange_trans (by norm_num) (by norm_num) h13 e7_conjRange_28_30
  have h15 : conjRange .E7 0 32 = true :=
    conjRange_trans (by norm_num) (by norm_num) h14 e7_conjRange_30_32
  have h16 : conjRange .E7 0 34 = true :=
    conjRange_trans (by norm_num) (by norm_num) h15 e7_conjRange_32_34
  have h17 : conjRange .E7 0 36 = true :=
    conjRange_trans (by norm_num) (by norm_num) h16 e7_conjRange_34_36
  have h18 : conjRange .E7 0 38 = true :=
    conjRange_trans (by norm_num) (by norm_num) h17 e7_conjRange_36_38
  have h19 : conjRange .E7 0 40 = true :=
    conjRange_trans (by norm_num) (by norm_num) h18 e7_conjRange_38_40
  have h20 : conjRange .E7 0 42 = true :=
    conjRange_trans (by norm_num) (by norm_num) h19 e7_conjRange_40_42
  have h21 : conjRange .E7 0 44 = true :=
    conjRange_trans (by norm_num) (by norm_num) h20 e7_conjRange_42_44
  have h22 : conjRange .E7 0 46 = true :=
    conjRange_trans (by norm_num) (by norm_num) h21 e7_conjRange_44_46
  have h23 : conjRange .E7 0 48 = true :=
    conjRange_trans (by norm_num) (by norm_num) h22 e7_conjRange_46_48
  have h24 : conjRange .E7 0 50 = true :=
    conjRange_trans (by norm_num) (by norm_num) h23 e7_conjRange_48_50
  have h25 : conjRange .E7 0 52 = true :=
    conjRange_trans (by norm_num) (by norm_num) h24 e7_conjRange_50_52
  have h26 : conjRange .E7 0 54 = true :=
    conjRange_trans (by norm_num) (by norm_num) h25 e7_conjRange_52_54
  have h27 : conjRange .E7 0 56 = true :=
    conjRange_trans (by norm_num) (by norm_num) h26 e7_conjRange_54_56
  have h28 : conjRange .E7 0 58 = true :=
    conjRange_trans (by norm_num) (by norm_num) h27 e7_conjRange_56_58
  have h29 : conjRange .E7 0 60 = true :=
    conjRange_trans (by norm_num) (by norm_num) h28 e7_conjRange_58_60
  have h30 : conjRange .E7 0 62 = true :=
    conjRange_trans (by norm_num) (by norm_num) h29 e7_conjRange_60_62
  have h31 : conjRange .E7 0 64 = true :=
    conjRange_trans (by norm_num) (by norm_num) h30 e7_conjRange_62_64
  have h32 : conjRange .E7 0 66 = true :=
    conjRange_trans (by norm_num) (by norm_num) h31 e7_conjRange_64_66
  have h33 : conjRange .E7 0 68 = true :=
    conjRange_trans (by norm_num) (by norm_num) h32 e7_conjRange_66_68
  have h34 : conjRange .E7 0 70 = true :=
    conjRange_trans (by norm_num) (by norm_num) h33 e7_conjRange_68_70
  have h35 : conjRange .E7 0 72 = true :=
    conjRange_trans (by norm_num) (by norm_num) h34 e7_conjRange_70_72
  have h36 : conjRange .E7 0 74 = true :=
    conjRange_trans (by norm_num) (by norm_num) h35 e7_conjRange_72_74
  have h37 : conjRange .E7 0 76 = true :=
    conjRange_trans (by norm_num) (by norm_num) h36 e7_conjRange_74_76
  have h38 : conjRange .E7 0 78 = true :=
    conjRange_trans (by norm_num) (by norm_num) h37 e7_conjRange_76_78
  have h39 : conjRange .E7 0 80 = true :=
    conjRange_trans (by norm_num) (by norm_num) h38 e7_conjRange_78_80
  have h40 : conjRange .E7 0 82 = true :=
    conjRange_trans (by norm_num) (by norm_num) h39 e7_conjRange_80_82
  have h41 : conjRange .E7 0 84 = true :=
    conjRange_trans (by norm_num) (by norm_num) h40 e7_conjRange_82_84
  have h42 : conjRange .E7 0 86 = true :=
    conjRange_trans (by norm_num) (by norm_num) h41 e7_conjRange_84_86
  have h43 : conjRange .E7 0 88 = true :=
    conjRange_trans (by norm_num) (by norm_num) h42 e7_conjRange_86_88
  have h44 : conjRange .E7 0 90 = true :=
    conjRange_trans (by norm_num) (by norm_num) h43 e7_conjRange_88_90
  have h45 : conjRange .E7 0 92 = true :=
    conjRange_trans (by norm_num) (by norm_num) h44 e7_conjRange_90_92
  have h46 : conjRange .E7 0 94 = true :=
    conjRange_trans (by norm_num) (by norm_num) h45 e7_conjRange_92_94
  have h47 : conjRange .E7 0 96 = true :=
    conjRange_trans (by norm_num) (by norm_num) h46 e7_conjRange_94_96
  have h48 : conjRange .E7 0 98 = true :=
    conjRange_trans (by norm_num) (by norm_num) h47 e7_conjRange_96_98
  have h49 : conjRange .E7 0 100 = true :=
    conjRange_trans (by norm_num) (by norm_num) h48 e7_conjRange_98_100
  have h50 : conjRange .E7 0 102 = true :=
    conjRange_trans (by norm_num) (by norm_num) h49 e7_conjRange_100_102
  have h51 : conjRange .E7 0 104 = true :=
    conjRange_trans (by norm_num) (by norm_num) h50 e7_conjRange_102_104
  have h52 : conjRange .E7 0 106 = true :=
    conjRange_trans (by norm_num) (by norm_num) h51 e7_conjRange_104_106
  have h53 : conjRange .E7 0 108 = true :=
    conjRange_trans (by norm_num) (by norm_num) h52 e7_conjRange_106_108
  have h54 : conjRange .E7 0 110 = true :=
    conjRange_trans (by norm_num) (by norm_num) h53 e7_conjRange_108_110
  have h55 : conjRange .E7 0 112 = true :=
    conjRange_trans (by norm_num) (by norm_num) h54 e7_conjRange_110_112
  have h56 : conjRange .E7 0 114 = true :=
    conjRange_trans (by norm_num) (by norm_num) h55 e7_conjRange_112_114
  have h57 : conjRange .E7 0 116 = true :=
    conjRange_trans (by norm_num) (by norm_num) h56 e7_conjRange_114_116
  have h58 : conjRange .E7 0 118 = true :=
    conjRange_trans (by norm_num) (by norm_num) h57 e7_conjRange_116_118
  have h59 : conjRange .E7 0 120 = true :=
    conjRange_trans (by norm_num) (by norm_num) h58 e7_conjRange_118_120
  have h60 : conjRange .E7 0 122 = true :=
    conjRange_trans (by norm_num) (by norm_num) h59 e7_conjRange_120_122
  have h61 : conjRange .E7 0 124 = true :=
    conjRange_trans (by norm_num) (by norm_num) h60 e7_conjRange_122_124
  have h62 : conjRange .E7 0 126 = true :=
    conjRange_trans (by norm_num) (by norm_num) h61 e7_conjRange_124_126
  exact h62

theorem dataChecks_E7 : DataChecks .E7 := by
  refine dataChecks_of e7_tabCheck e7_allValid ?_ fun j => ?_
  · rw [Tag.rootCertificate_length]
    exact e7_conjRange_all
  · fin_cases j
    · exact e7_simpleRow_0
    · exact e7_simpleRow_1
    · exact e7_simpleRow_2
    · exact e7_simpleRow_3
    · exact e7_simpleRow_4
    · exact e7_simpleRow_5
    · exact e7_simpleRow_6

end CFSG.LieType.Chevalley.RootOps
