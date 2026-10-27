module

public import CFSG.LieType.Chevalley.RootOps.Cert.E8Tab
public import CFSG.LieType.Chevalley.RootOps.Cert.E8Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.E8Conj0
public import CFSG.LieType.Chevalley.RootOps.Cert.E8Conj40
public import CFSG.LieType.Chevalley.RootOps.Cert.E8Conj80
public import CFSG.LieType.Chevalley.RootOps.Cert.E8Conj120
public import CFSG.LieType.Chevalley.RootOps.Cert.E8Conj160
public import CFSG.LieType.Chevalley.RootOps.Cert.E8Conj200
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem e8_conjRange_all : conjRange .E8 0 240 = true := by
  have h0 : conjRange .E8 0 1 = true := e8_conjRange_0_1
  have h1 : conjRange .E8 0 2 = true :=
    conjRange_trans (by norm_num) (by norm_num) h0 e8_conjRange_1_2
  have h2 : conjRange .E8 0 3 = true :=
    conjRange_trans (by norm_num) (by norm_num) h1 e8_conjRange_2_3
  have h3 : conjRange .E8 0 4 = true :=
    conjRange_trans (by norm_num) (by norm_num) h2 e8_conjRange_3_4
  have h4 : conjRange .E8 0 5 = true :=
    conjRange_trans (by norm_num) (by norm_num) h3 e8_conjRange_4_5
  have h5 : conjRange .E8 0 6 = true :=
    conjRange_trans (by norm_num) (by norm_num) h4 e8_conjRange_5_6
  have h6 : conjRange .E8 0 7 = true :=
    conjRange_trans (by norm_num) (by norm_num) h5 e8_conjRange_6_7
  have h7 : conjRange .E8 0 8 = true :=
    conjRange_trans (by norm_num) (by norm_num) h6 e8_conjRange_7_8
  have h8 : conjRange .E8 0 9 = true :=
    conjRange_trans (by norm_num) (by norm_num) h7 e8_conjRange_8_9
  have h9 : conjRange .E8 0 10 = true :=
    conjRange_trans (by norm_num) (by norm_num) h8 e8_conjRange_9_10
  have h10 : conjRange .E8 0 11 = true :=
    conjRange_trans (by norm_num) (by norm_num) h9 e8_conjRange_10_11
  have h11 : conjRange .E8 0 12 = true :=
    conjRange_trans (by norm_num) (by norm_num) h10 e8_conjRange_11_12
  have h12 : conjRange .E8 0 13 = true :=
    conjRange_trans (by norm_num) (by norm_num) h11 e8_conjRange_12_13
  have h13 : conjRange .E8 0 14 = true :=
    conjRange_trans (by norm_num) (by norm_num) h12 e8_conjRange_13_14
  have h14 : conjRange .E8 0 15 = true :=
    conjRange_trans (by norm_num) (by norm_num) h13 e8_conjRange_14_15
  have h15 : conjRange .E8 0 16 = true :=
    conjRange_trans (by norm_num) (by norm_num) h14 e8_conjRange_15_16
  have h16 : conjRange .E8 0 17 = true :=
    conjRange_trans (by norm_num) (by norm_num) h15 e8_conjRange_16_17
  have h17 : conjRange .E8 0 18 = true :=
    conjRange_trans (by norm_num) (by norm_num) h16 e8_conjRange_17_18
  have h18 : conjRange .E8 0 19 = true :=
    conjRange_trans (by norm_num) (by norm_num) h17 e8_conjRange_18_19
  have h19 : conjRange .E8 0 20 = true :=
    conjRange_trans (by norm_num) (by norm_num) h18 e8_conjRange_19_20
  have h20 : conjRange .E8 0 21 = true :=
    conjRange_trans (by norm_num) (by norm_num) h19 e8_conjRange_20_21
  have h21 : conjRange .E8 0 22 = true :=
    conjRange_trans (by norm_num) (by norm_num) h20 e8_conjRange_21_22
  have h22 : conjRange .E8 0 23 = true :=
    conjRange_trans (by norm_num) (by norm_num) h21 e8_conjRange_22_23
  have h23 : conjRange .E8 0 24 = true :=
    conjRange_trans (by norm_num) (by norm_num) h22 e8_conjRange_23_24
  have h24 : conjRange .E8 0 25 = true :=
    conjRange_trans (by norm_num) (by norm_num) h23 e8_conjRange_24_25
  have h25 : conjRange .E8 0 26 = true :=
    conjRange_trans (by norm_num) (by norm_num) h24 e8_conjRange_25_26
  have h26 : conjRange .E8 0 27 = true :=
    conjRange_trans (by norm_num) (by norm_num) h25 e8_conjRange_26_27
  have h27 : conjRange .E8 0 28 = true :=
    conjRange_trans (by norm_num) (by norm_num) h26 e8_conjRange_27_28
  have h28 : conjRange .E8 0 29 = true :=
    conjRange_trans (by norm_num) (by norm_num) h27 e8_conjRange_28_29
  have h29 : conjRange .E8 0 30 = true :=
    conjRange_trans (by norm_num) (by norm_num) h28 e8_conjRange_29_30
  have h30 : conjRange .E8 0 31 = true :=
    conjRange_trans (by norm_num) (by norm_num) h29 e8_conjRange_30_31
  have h31 : conjRange .E8 0 32 = true :=
    conjRange_trans (by norm_num) (by norm_num) h30 e8_conjRange_31_32
  have h32 : conjRange .E8 0 33 = true :=
    conjRange_trans (by norm_num) (by norm_num) h31 e8_conjRange_32_33
  have h33 : conjRange .E8 0 34 = true :=
    conjRange_trans (by norm_num) (by norm_num) h32 e8_conjRange_33_34
  have h34 : conjRange .E8 0 35 = true :=
    conjRange_trans (by norm_num) (by norm_num) h33 e8_conjRange_34_35
  have h35 : conjRange .E8 0 36 = true :=
    conjRange_trans (by norm_num) (by norm_num) h34 e8_conjRange_35_36
  have h36 : conjRange .E8 0 37 = true :=
    conjRange_trans (by norm_num) (by norm_num) h35 e8_conjRange_36_37
  have h37 : conjRange .E8 0 38 = true :=
    conjRange_trans (by norm_num) (by norm_num) h36 e8_conjRange_37_38
  have h38 : conjRange .E8 0 39 = true :=
    conjRange_trans (by norm_num) (by norm_num) h37 e8_conjRange_38_39
  have h39 : conjRange .E8 0 40 = true :=
    conjRange_trans (by norm_num) (by norm_num) h38 e8_conjRange_39_40
  have h40 : conjRange .E8 0 41 = true :=
    conjRange_trans (by norm_num) (by norm_num) h39 e8_conjRange_40_41
  have h41 : conjRange .E8 0 42 = true :=
    conjRange_trans (by norm_num) (by norm_num) h40 e8_conjRange_41_42
  have h42 : conjRange .E8 0 43 = true :=
    conjRange_trans (by norm_num) (by norm_num) h41 e8_conjRange_42_43
  have h43 : conjRange .E8 0 44 = true :=
    conjRange_trans (by norm_num) (by norm_num) h42 e8_conjRange_43_44
  have h44 : conjRange .E8 0 45 = true :=
    conjRange_trans (by norm_num) (by norm_num) h43 e8_conjRange_44_45
  have h45 : conjRange .E8 0 46 = true :=
    conjRange_trans (by norm_num) (by norm_num) h44 e8_conjRange_45_46
  have h46 : conjRange .E8 0 47 = true :=
    conjRange_trans (by norm_num) (by norm_num) h45 e8_conjRange_46_47
  have h47 : conjRange .E8 0 48 = true :=
    conjRange_trans (by norm_num) (by norm_num) h46 e8_conjRange_47_48
  have h48 : conjRange .E8 0 49 = true :=
    conjRange_trans (by norm_num) (by norm_num) h47 e8_conjRange_48_49
  have h49 : conjRange .E8 0 50 = true :=
    conjRange_trans (by norm_num) (by norm_num) h48 e8_conjRange_49_50
  have h50 : conjRange .E8 0 51 = true :=
    conjRange_trans (by norm_num) (by norm_num) h49 e8_conjRange_50_51
  have h51 : conjRange .E8 0 52 = true :=
    conjRange_trans (by norm_num) (by norm_num) h50 e8_conjRange_51_52
  have h52 : conjRange .E8 0 53 = true :=
    conjRange_trans (by norm_num) (by norm_num) h51 e8_conjRange_52_53
  have h53 : conjRange .E8 0 54 = true :=
    conjRange_trans (by norm_num) (by norm_num) h52 e8_conjRange_53_54
  have h54 : conjRange .E8 0 55 = true :=
    conjRange_trans (by norm_num) (by norm_num) h53 e8_conjRange_54_55
  have h55 : conjRange .E8 0 56 = true :=
    conjRange_trans (by norm_num) (by norm_num) h54 e8_conjRange_55_56
  have h56 : conjRange .E8 0 57 = true :=
    conjRange_trans (by norm_num) (by norm_num) h55 e8_conjRange_56_57
  have h57 : conjRange .E8 0 58 = true :=
    conjRange_trans (by norm_num) (by norm_num) h56 e8_conjRange_57_58
  have h58 : conjRange .E8 0 59 = true :=
    conjRange_trans (by norm_num) (by norm_num) h57 e8_conjRange_58_59
  have h59 : conjRange .E8 0 60 = true :=
    conjRange_trans (by norm_num) (by norm_num) h58 e8_conjRange_59_60
  have h60 : conjRange .E8 0 61 = true :=
    conjRange_trans (by norm_num) (by norm_num) h59 e8_conjRange_60_61
  have h61 : conjRange .E8 0 62 = true :=
    conjRange_trans (by norm_num) (by norm_num) h60 e8_conjRange_61_62
  have h62 : conjRange .E8 0 63 = true :=
    conjRange_trans (by norm_num) (by norm_num) h61 e8_conjRange_62_63
  have h63 : conjRange .E8 0 64 = true :=
    conjRange_trans (by norm_num) (by norm_num) h62 e8_conjRange_63_64
  have h64 : conjRange .E8 0 65 = true :=
    conjRange_trans (by norm_num) (by norm_num) h63 e8_conjRange_64_65
  have h65 : conjRange .E8 0 66 = true :=
    conjRange_trans (by norm_num) (by norm_num) h64 e8_conjRange_65_66
  have h66 : conjRange .E8 0 67 = true :=
    conjRange_trans (by norm_num) (by norm_num) h65 e8_conjRange_66_67
  have h67 : conjRange .E8 0 68 = true :=
    conjRange_trans (by norm_num) (by norm_num) h66 e8_conjRange_67_68
  have h68 : conjRange .E8 0 69 = true :=
    conjRange_trans (by norm_num) (by norm_num) h67 e8_conjRange_68_69
  have h69 : conjRange .E8 0 70 = true :=
    conjRange_trans (by norm_num) (by norm_num) h68 e8_conjRange_69_70
  have h70 : conjRange .E8 0 71 = true :=
    conjRange_trans (by norm_num) (by norm_num) h69 e8_conjRange_70_71
  have h71 : conjRange .E8 0 72 = true :=
    conjRange_trans (by norm_num) (by norm_num) h70 e8_conjRange_71_72
  have h72 : conjRange .E8 0 73 = true :=
    conjRange_trans (by norm_num) (by norm_num) h71 e8_conjRange_72_73
  have h73 : conjRange .E8 0 74 = true :=
    conjRange_trans (by norm_num) (by norm_num) h72 e8_conjRange_73_74
  have h74 : conjRange .E8 0 75 = true :=
    conjRange_trans (by norm_num) (by norm_num) h73 e8_conjRange_74_75
  have h75 : conjRange .E8 0 76 = true :=
    conjRange_trans (by norm_num) (by norm_num) h74 e8_conjRange_75_76
  have h76 : conjRange .E8 0 77 = true :=
    conjRange_trans (by norm_num) (by norm_num) h75 e8_conjRange_76_77
  have h77 : conjRange .E8 0 78 = true :=
    conjRange_trans (by norm_num) (by norm_num) h76 e8_conjRange_77_78
  have h78 : conjRange .E8 0 79 = true :=
    conjRange_trans (by norm_num) (by norm_num) h77 e8_conjRange_78_79
  have h79 : conjRange .E8 0 80 = true :=
    conjRange_trans (by norm_num) (by norm_num) h78 e8_conjRange_79_80
  have h80 : conjRange .E8 0 81 = true :=
    conjRange_trans (by norm_num) (by norm_num) h79 e8_conjRange_80_81
  have h81 : conjRange .E8 0 82 = true :=
    conjRange_trans (by norm_num) (by norm_num) h80 e8_conjRange_81_82
  have h82 : conjRange .E8 0 83 = true :=
    conjRange_trans (by norm_num) (by norm_num) h81 e8_conjRange_82_83
  have h83 : conjRange .E8 0 84 = true :=
    conjRange_trans (by norm_num) (by norm_num) h82 e8_conjRange_83_84
  have h84 : conjRange .E8 0 85 = true :=
    conjRange_trans (by norm_num) (by norm_num) h83 e8_conjRange_84_85
  have h85 : conjRange .E8 0 86 = true :=
    conjRange_trans (by norm_num) (by norm_num) h84 e8_conjRange_85_86
  have h86 : conjRange .E8 0 87 = true :=
    conjRange_trans (by norm_num) (by norm_num) h85 e8_conjRange_86_87
  have h87 : conjRange .E8 0 88 = true :=
    conjRange_trans (by norm_num) (by norm_num) h86 e8_conjRange_87_88
  have h88 : conjRange .E8 0 89 = true :=
    conjRange_trans (by norm_num) (by norm_num) h87 e8_conjRange_88_89
  have h89 : conjRange .E8 0 90 = true :=
    conjRange_trans (by norm_num) (by norm_num) h88 e8_conjRange_89_90
  have h90 : conjRange .E8 0 91 = true :=
    conjRange_trans (by norm_num) (by norm_num) h89 e8_conjRange_90_91
  have h91 : conjRange .E8 0 92 = true :=
    conjRange_trans (by norm_num) (by norm_num) h90 e8_conjRange_91_92
  have h92 : conjRange .E8 0 93 = true :=
    conjRange_trans (by norm_num) (by norm_num) h91 e8_conjRange_92_93
  have h93 : conjRange .E8 0 94 = true :=
    conjRange_trans (by norm_num) (by norm_num) h92 e8_conjRange_93_94
  have h94 : conjRange .E8 0 95 = true :=
    conjRange_trans (by norm_num) (by norm_num) h93 e8_conjRange_94_95
  have h95 : conjRange .E8 0 96 = true :=
    conjRange_trans (by norm_num) (by norm_num) h94 e8_conjRange_95_96
  have h96 : conjRange .E8 0 97 = true :=
    conjRange_trans (by norm_num) (by norm_num) h95 e8_conjRange_96_97
  have h97 : conjRange .E8 0 98 = true :=
    conjRange_trans (by norm_num) (by norm_num) h96 e8_conjRange_97_98
  have h98 : conjRange .E8 0 99 = true :=
    conjRange_trans (by norm_num) (by norm_num) h97 e8_conjRange_98_99
  have h99 : conjRange .E8 0 100 = true :=
    conjRange_trans (by norm_num) (by norm_num) h98 e8_conjRange_99_100
  have h100 : conjRange .E8 0 101 = true :=
    conjRange_trans (by norm_num) (by norm_num) h99 e8_conjRange_100_101
  have h101 : conjRange .E8 0 102 = true :=
    conjRange_trans (by norm_num) (by norm_num) h100 e8_conjRange_101_102
  have h102 : conjRange .E8 0 103 = true :=
    conjRange_trans (by norm_num) (by norm_num) h101 e8_conjRange_102_103
  have h103 : conjRange .E8 0 104 = true :=
    conjRange_trans (by norm_num) (by norm_num) h102 e8_conjRange_103_104
  have h104 : conjRange .E8 0 105 = true :=
    conjRange_trans (by norm_num) (by norm_num) h103 e8_conjRange_104_105
  have h105 : conjRange .E8 0 106 = true :=
    conjRange_trans (by norm_num) (by norm_num) h104 e8_conjRange_105_106
  have h106 : conjRange .E8 0 107 = true :=
    conjRange_trans (by norm_num) (by norm_num) h105 e8_conjRange_106_107
  have h107 : conjRange .E8 0 108 = true :=
    conjRange_trans (by norm_num) (by norm_num) h106 e8_conjRange_107_108
  have h108 : conjRange .E8 0 109 = true :=
    conjRange_trans (by norm_num) (by norm_num) h107 e8_conjRange_108_109
  have h109 : conjRange .E8 0 110 = true :=
    conjRange_trans (by norm_num) (by norm_num) h108 e8_conjRange_109_110
  have h110 : conjRange .E8 0 111 = true :=
    conjRange_trans (by norm_num) (by norm_num) h109 e8_conjRange_110_111
  have h111 : conjRange .E8 0 112 = true :=
    conjRange_trans (by norm_num) (by norm_num) h110 e8_conjRange_111_112
  have h112 : conjRange .E8 0 113 = true :=
    conjRange_trans (by norm_num) (by norm_num) h111 e8_conjRange_112_113
  have h113 : conjRange .E8 0 114 = true :=
    conjRange_trans (by norm_num) (by norm_num) h112 e8_conjRange_113_114
  have h114 : conjRange .E8 0 115 = true :=
    conjRange_trans (by norm_num) (by norm_num) h113 e8_conjRange_114_115
  have h115 : conjRange .E8 0 116 = true :=
    conjRange_trans (by norm_num) (by norm_num) h114 e8_conjRange_115_116
  have h116 : conjRange .E8 0 117 = true :=
    conjRange_trans (by norm_num) (by norm_num) h115 e8_conjRange_116_117
  have h117 : conjRange .E8 0 118 = true :=
    conjRange_trans (by norm_num) (by norm_num) h116 e8_conjRange_117_118
  have h118 : conjRange .E8 0 119 = true :=
    conjRange_trans (by norm_num) (by norm_num) h117 e8_conjRange_118_119
  have h119 : conjRange .E8 0 120 = true :=
    conjRange_trans (by norm_num) (by norm_num) h118 e8_conjRange_119_120
  have h120 : conjRange .E8 0 121 = true :=
    conjRange_trans (by norm_num) (by norm_num) h119 e8_conjRange_120_121
  have h121 : conjRange .E8 0 122 = true :=
    conjRange_trans (by norm_num) (by norm_num) h120 e8_conjRange_121_122
  have h122 : conjRange .E8 0 123 = true :=
    conjRange_trans (by norm_num) (by norm_num) h121 e8_conjRange_122_123
  have h123 : conjRange .E8 0 124 = true :=
    conjRange_trans (by norm_num) (by norm_num) h122 e8_conjRange_123_124
  have h124 : conjRange .E8 0 125 = true :=
    conjRange_trans (by norm_num) (by norm_num) h123 e8_conjRange_124_125
  have h125 : conjRange .E8 0 126 = true :=
    conjRange_trans (by norm_num) (by norm_num) h124 e8_conjRange_125_126
  have h126 : conjRange .E8 0 127 = true :=
    conjRange_trans (by norm_num) (by norm_num) h125 e8_conjRange_126_127
  have h127 : conjRange .E8 0 128 = true :=
    conjRange_trans (by norm_num) (by norm_num) h126 e8_conjRange_127_128
  have h128 : conjRange .E8 0 129 = true :=
    conjRange_trans (by norm_num) (by norm_num) h127 e8_conjRange_128_129
  have h129 : conjRange .E8 0 130 = true :=
    conjRange_trans (by norm_num) (by norm_num) h128 e8_conjRange_129_130
  have h130 : conjRange .E8 0 131 = true :=
    conjRange_trans (by norm_num) (by norm_num) h129 e8_conjRange_130_131
  have h131 : conjRange .E8 0 132 = true :=
    conjRange_trans (by norm_num) (by norm_num) h130 e8_conjRange_131_132
  have h132 : conjRange .E8 0 133 = true :=
    conjRange_trans (by norm_num) (by norm_num) h131 e8_conjRange_132_133
  have h133 : conjRange .E8 0 134 = true :=
    conjRange_trans (by norm_num) (by norm_num) h132 e8_conjRange_133_134
  have h134 : conjRange .E8 0 135 = true :=
    conjRange_trans (by norm_num) (by norm_num) h133 e8_conjRange_134_135
  have h135 : conjRange .E8 0 136 = true :=
    conjRange_trans (by norm_num) (by norm_num) h134 e8_conjRange_135_136
  have h136 : conjRange .E8 0 137 = true :=
    conjRange_trans (by norm_num) (by norm_num) h135 e8_conjRange_136_137
  have h137 : conjRange .E8 0 138 = true :=
    conjRange_trans (by norm_num) (by norm_num) h136 e8_conjRange_137_138
  have h138 : conjRange .E8 0 139 = true :=
    conjRange_trans (by norm_num) (by norm_num) h137 e8_conjRange_138_139
  have h139 : conjRange .E8 0 140 = true :=
    conjRange_trans (by norm_num) (by norm_num) h138 e8_conjRange_139_140
  have h140 : conjRange .E8 0 141 = true :=
    conjRange_trans (by norm_num) (by norm_num) h139 e8_conjRange_140_141
  have h141 : conjRange .E8 0 142 = true :=
    conjRange_trans (by norm_num) (by norm_num) h140 e8_conjRange_141_142
  have h142 : conjRange .E8 0 143 = true :=
    conjRange_trans (by norm_num) (by norm_num) h141 e8_conjRange_142_143
  have h143 : conjRange .E8 0 144 = true :=
    conjRange_trans (by norm_num) (by norm_num) h142 e8_conjRange_143_144
  have h144 : conjRange .E8 0 145 = true :=
    conjRange_trans (by norm_num) (by norm_num) h143 e8_conjRange_144_145
  have h145 : conjRange .E8 0 146 = true :=
    conjRange_trans (by norm_num) (by norm_num) h144 e8_conjRange_145_146
  have h146 : conjRange .E8 0 147 = true :=
    conjRange_trans (by norm_num) (by norm_num) h145 e8_conjRange_146_147
  have h147 : conjRange .E8 0 148 = true :=
    conjRange_trans (by norm_num) (by norm_num) h146 e8_conjRange_147_148
  have h148 : conjRange .E8 0 149 = true :=
    conjRange_trans (by norm_num) (by norm_num) h147 e8_conjRange_148_149
  have h149 : conjRange .E8 0 150 = true :=
    conjRange_trans (by norm_num) (by norm_num) h148 e8_conjRange_149_150
  have h150 : conjRange .E8 0 151 = true :=
    conjRange_trans (by norm_num) (by norm_num) h149 e8_conjRange_150_151
  have h151 : conjRange .E8 0 152 = true :=
    conjRange_trans (by norm_num) (by norm_num) h150 e8_conjRange_151_152
  have h152 : conjRange .E8 0 153 = true :=
    conjRange_trans (by norm_num) (by norm_num) h151 e8_conjRange_152_153
  have h153 : conjRange .E8 0 154 = true :=
    conjRange_trans (by norm_num) (by norm_num) h152 e8_conjRange_153_154
  have h154 : conjRange .E8 0 155 = true :=
    conjRange_trans (by norm_num) (by norm_num) h153 e8_conjRange_154_155
  have h155 : conjRange .E8 0 156 = true :=
    conjRange_trans (by norm_num) (by norm_num) h154 e8_conjRange_155_156
  have h156 : conjRange .E8 0 157 = true :=
    conjRange_trans (by norm_num) (by norm_num) h155 e8_conjRange_156_157
  have h157 : conjRange .E8 0 158 = true :=
    conjRange_trans (by norm_num) (by norm_num) h156 e8_conjRange_157_158
  have h158 : conjRange .E8 0 159 = true :=
    conjRange_trans (by norm_num) (by norm_num) h157 e8_conjRange_158_159
  have h159 : conjRange .E8 0 160 = true :=
    conjRange_trans (by norm_num) (by norm_num) h158 e8_conjRange_159_160
  have h160 : conjRange .E8 0 161 = true :=
    conjRange_trans (by norm_num) (by norm_num) h159 e8_conjRange_160_161
  have h161 : conjRange .E8 0 162 = true :=
    conjRange_trans (by norm_num) (by norm_num) h160 e8_conjRange_161_162
  have h162 : conjRange .E8 0 163 = true :=
    conjRange_trans (by norm_num) (by norm_num) h161 e8_conjRange_162_163
  have h163 : conjRange .E8 0 164 = true :=
    conjRange_trans (by norm_num) (by norm_num) h162 e8_conjRange_163_164
  have h164 : conjRange .E8 0 165 = true :=
    conjRange_trans (by norm_num) (by norm_num) h163 e8_conjRange_164_165
  have h165 : conjRange .E8 0 166 = true :=
    conjRange_trans (by norm_num) (by norm_num) h164 e8_conjRange_165_166
  have h166 : conjRange .E8 0 167 = true :=
    conjRange_trans (by norm_num) (by norm_num) h165 e8_conjRange_166_167
  have h167 : conjRange .E8 0 168 = true :=
    conjRange_trans (by norm_num) (by norm_num) h166 e8_conjRange_167_168
  have h168 : conjRange .E8 0 169 = true :=
    conjRange_trans (by norm_num) (by norm_num) h167 e8_conjRange_168_169
  have h169 : conjRange .E8 0 170 = true :=
    conjRange_trans (by norm_num) (by norm_num) h168 e8_conjRange_169_170
  have h170 : conjRange .E8 0 171 = true :=
    conjRange_trans (by norm_num) (by norm_num) h169 e8_conjRange_170_171
  have h171 : conjRange .E8 0 172 = true :=
    conjRange_trans (by norm_num) (by norm_num) h170 e8_conjRange_171_172
  have h172 : conjRange .E8 0 173 = true :=
    conjRange_trans (by norm_num) (by norm_num) h171 e8_conjRange_172_173
  have h173 : conjRange .E8 0 174 = true :=
    conjRange_trans (by norm_num) (by norm_num) h172 e8_conjRange_173_174
  have h174 : conjRange .E8 0 175 = true :=
    conjRange_trans (by norm_num) (by norm_num) h173 e8_conjRange_174_175
  have h175 : conjRange .E8 0 176 = true :=
    conjRange_trans (by norm_num) (by norm_num) h174 e8_conjRange_175_176
  have h176 : conjRange .E8 0 177 = true :=
    conjRange_trans (by norm_num) (by norm_num) h175 e8_conjRange_176_177
  have h177 : conjRange .E8 0 178 = true :=
    conjRange_trans (by norm_num) (by norm_num) h176 e8_conjRange_177_178
  have h178 : conjRange .E8 0 179 = true :=
    conjRange_trans (by norm_num) (by norm_num) h177 e8_conjRange_178_179
  have h179 : conjRange .E8 0 180 = true :=
    conjRange_trans (by norm_num) (by norm_num) h178 e8_conjRange_179_180
  have h180 : conjRange .E8 0 181 = true :=
    conjRange_trans (by norm_num) (by norm_num) h179 e8_conjRange_180_181
  have h181 : conjRange .E8 0 182 = true :=
    conjRange_trans (by norm_num) (by norm_num) h180 e8_conjRange_181_182
  have h182 : conjRange .E8 0 183 = true :=
    conjRange_trans (by norm_num) (by norm_num) h181 e8_conjRange_182_183
  have h183 : conjRange .E8 0 184 = true :=
    conjRange_trans (by norm_num) (by norm_num) h182 e8_conjRange_183_184
  have h184 : conjRange .E8 0 185 = true :=
    conjRange_trans (by norm_num) (by norm_num) h183 e8_conjRange_184_185
  have h185 : conjRange .E8 0 186 = true :=
    conjRange_trans (by norm_num) (by norm_num) h184 e8_conjRange_185_186
  have h186 : conjRange .E8 0 187 = true :=
    conjRange_trans (by norm_num) (by norm_num) h185 e8_conjRange_186_187
  have h187 : conjRange .E8 0 188 = true :=
    conjRange_trans (by norm_num) (by norm_num) h186 e8_conjRange_187_188
  have h188 : conjRange .E8 0 189 = true :=
    conjRange_trans (by norm_num) (by norm_num) h187 e8_conjRange_188_189
  have h189 : conjRange .E8 0 190 = true :=
    conjRange_trans (by norm_num) (by norm_num) h188 e8_conjRange_189_190
  have h190 : conjRange .E8 0 191 = true :=
    conjRange_trans (by norm_num) (by norm_num) h189 e8_conjRange_190_191
  have h191 : conjRange .E8 0 192 = true :=
    conjRange_trans (by norm_num) (by norm_num) h190 e8_conjRange_191_192
  have h192 : conjRange .E8 0 193 = true :=
    conjRange_trans (by norm_num) (by norm_num) h191 e8_conjRange_192_193
  have h193 : conjRange .E8 0 194 = true :=
    conjRange_trans (by norm_num) (by norm_num) h192 e8_conjRange_193_194
  have h194 : conjRange .E8 0 195 = true :=
    conjRange_trans (by norm_num) (by norm_num) h193 e8_conjRange_194_195
  have h195 : conjRange .E8 0 196 = true :=
    conjRange_trans (by norm_num) (by norm_num) h194 e8_conjRange_195_196
  have h196 : conjRange .E8 0 197 = true :=
    conjRange_trans (by norm_num) (by norm_num) h195 e8_conjRange_196_197
  have h197 : conjRange .E8 0 198 = true :=
    conjRange_trans (by norm_num) (by norm_num) h196 e8_conjRange_197_198
  have h198 : conjRange .E8 0 199 = true :=
    conjRange_trans (by norm_num) (by norm_num) h197 e8_conjRange_198_199
  have h199 : conjRange .E8 0 200 = true :=
    conjRange_trans (by norm_num) (by norm_num) h198 e8_conjRange_199_200
  have h200 : conjRange .E8 0 201 = true :=
    conjRange_trans (by norm_num) (by norm_num) h199 e8_conjRange_200_201
  have h201 : conjRange .E8 0 202 = true :=
    conjRange_trans (by norm_num) (by norm_num) h200 e8_conjRange_201_202
  have h202 : conjRange .E8 0 203 = true :=
    conjRange_trans (by norm_num) (by norm_num) h201 e8_conjRange_202_203
  have h203 : conjRange .E8 0 204 = true :=
    conjRange_trans (by norm_num) (by norm_num) h202 e8_conjRange_203_204
  have h204 : conjRange .E8 0 205 = true :=
    conjRange_trans (by norm_num) (by norm_num) h203 e8_conjRange_204_205
  have h205 : conjRange .E8 0 206 = true :=
    conjRange_trans (by norm_num) (by norm_num) h204 e8_conjRange_205_206
  have h206 : conjRange .E8 0 207 = true :=
    conjRange_trans (by norm_num) (by norm_num) h205 e8_conjRange_206_207
  have h207 : conjRange .E8 0 208 = true :=
    conjRange_trans (by norm_num) (by norm_num) h206 e8_conjRange_207_208
  have h208 : conjRange .E8 0 209 = true :=
    conjRange_trans (by norm_num) (by norm_num) h207 e8_conjRange_208_209
  have h209 : conjRange .E8 0 210 = true :=
    conjRange_trans (by norm_num) (by norm_num) h208 e8_conjRange_209_210
  have h210 : conjRange .E8 0 211 = true :=
    conjRange_trans (by norm_num) (by norm_num) h209 e8_conjRange_210_211
  have h211 : conjRange .E8 0 212 = true :=
    conjRange_trans (by norm_num) (by norm_num) h210 e8_conjRange_211_212
  have h212 : conjRange .E8 0 213 = true :=
    conjRange_trans (by norm_num) (by norm_num) h211 e8_conjRange_212_213
  have h213 : conjRange .E8 0 214 = true :=
    conjRange_trans (by norm_num) (by norm_num) h212 e8_conjRange_213_214
  have h214 : conjRange .E8 0 215 = true :=
    conjRange_trans (by norm_num) (by norm_num) h213 e8_conjRange_214_215
  have h215 : conjRange .E8 0 216 = true :=
    conjRange_trans (by norm_num) (by norm_num) h214 e8_conjRange_215_216
  have h216 : conjRange .E8 0 217 = true :=
    conjRange_trans (by norm_num) (by norm_num) h215 e8_conjRange_216_217
  have h217 : conjRange .E8 0 218 = true :=
    conjRange_trans (by norm_num) (by norm_num) h216 e8_conjRange_217_218
  have h218 : conjRange .E8 0 219 = true :=
    conjRange_trans (by norm_num) (by norm_num) h217 e8_conjRange_218_219
  have h219 : conjRange .E8 0 220 = true :=
    conjRange_trans (by norm_num) (by norm_num) h218 e8_conjRange_219_220
  have h220 : conjRange .E8 0 221 = true :=
    conjRange_trans (by norm_num) (by norm_num) h219 e8_conjRange_220_221
  have h221 : conjRange .E8 0 222 = true :=
    conjRange_trans (by norm_num) (by norm_num) h220 e8_conjRange_221_222
  have h222 : conjRange .E8 0 223 = true :=
    conjRange_trans (by norm_num) (by norm_num) h221 e8_conjRange_222_223
  have h223 : conjRange .E8 0 224 = true :=
    conjRange_trans (by norm_num) (by norm_num) h222 e8_conjRange_223_224
  have h224 : conjRange .E8 0 225 = true :=
    conjRange_trans (by norm_num) (by norm_num) h223 e8_conjRange_224_225
  have h225 : conjRange .E8 0 226 = true :=
    conjRange_trans (by norm_num) (by norm_num) h224 e8_conjRange_225_226
  have h226 : conjRange .E8 0 227 = true :=
    conjRange_trans (by norm_num) (by norm_num) h225 e8_conjRange_226_227
  have h227 : conjRange .E8 0 228 = true :=
    conjRange_trans (by norm_num) (by norm_num) h226 e8_conjRange_227_228
  have h228 : conjRange .E8 0 229 = true :=
    conjRange_trans (by norm_num) (by norm_num) h227 e8_conjRange_228_229
  have h229 : conjRange .E8 0 230 = true :=
    conjRange_trans (by norm_num) (by norm_num) h228 e8_conjRange_229_230
  have h230 : conjRange .E8 0 231 = true :=
    conjRange_trans (by norm_num) (by norm_num) h229 e8_conjRange_230_231
  have h231 : conjRange .E8 0 232 = true :=
    conjRange_trans (by norm_num) (by norm_num) h230 e8_conjRange_231_232
  have h232 : conjRange .E8 0 233 = true :=
    conjRange_trans (by norm_num) (by norm_num) h231 e8_conjRange_232_233
  have h233 : conjRange .E8 0 234 = true :=
    conjRange_trans (by norm_num) (by norm_num) h232 e8_conjRange_233_234
  have h234 : conjRange .E8 0 235 = true :=
    conjRange_trans (by norm_num) (by norm_num) h233 e8_conjRange_234_235
  have h235 : conjRange .E8 0 236 = true :=
    conjRange_trans (by norm_num) (by norm_num) h234 e8_conjRange_235_236
  have h236 : conjRange .E8 0 237 = true :=
    conjRange_trans (by norm_num) (by norm_num) h235 e8_conjRange_236_237
  have h237 : conjRange .E8 0 238 = true :=
    conjRange_trans (by norm_num) (by norm_num) h236 e8_conjRange_237_238
  have h238 : conjRange .E8 0 239 = true :=
    conjRange_trans (by norm_num) (by norm_num) h237 e8_conjRange_238_239
  have h239 : conjRange .E8 0 240 = true :=
    conjRange_trans (by norm_num) (by norm_num) h238 e8_conjRange_239_240
  exact h239

theorem dataChecks_E8 : DataChecks .E8 := by
  refine dataChecks_of e8_tabCheck e8_allValid ?_ fun j => ?_
  · rw [Tag.rootCertificate_length]
    exact e8_conjRange_all
  · fin_cases j
    · exact e8_simpleRow_0
    · exact e8_simpleRow_1
    · exact e8_simpleRow_2
    · exact e8_simpleRow_3
    · exact e8_simpleRow_4
    · exact e8_simpleRow_5
    · exact e8_simpleRow_6
    · exact e8_simpleRow_7

end CFSG.LieType.Chevalley.RootOps
