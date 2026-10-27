module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4Odd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKL5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKG2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKTits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKF4
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate43
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate4017
public import Certificates.Certificate4024
public import Certificates.Certificate4025
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3084
public import Certificates.Certificate3086
public import Certificates.Certificate3119
public import Certificates.Certificate3120
public import Certificates.Certificate3139
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3172
public import Certificates.Certificate4047
public import Certificates.Certificate4060
public import Certificates.Certificate4065
public import Certificates.Certificate4072
public import Certificates.Certificate4073
public import Certificates.Certificate4075
public import Certificates.Certificate4076
public import Certificates.Certificate4077
public import Certificates.Certificate8010
public import Certificates.Certificate8011
public import Certificates.Certificate8012
public import Certificates.Certificate8013
public import Certificates.Certificate8014
public import Certificates.Certificate8015
public import Certificates.Certificate8016
public import Certificates.Certificate8017
public import Certificates.Certificate8018
public import Certificates.Certificate8019
public import Certificates.Certificate8020
public import Certificates.Certificate8021
public import Certificates.Certificate8022
public import Certificates.Certificate8024
public import Certificates.Certificate8025
public import Certificates.Certificate8026
public import Certificates.Certificate8027
public import Certificates.Certificate8028
public import Certificates.Certificate8029
public import Certificates.Certificate8030
public import Certificates.Certificate8031
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate4131
public import Certificates.Certificate4132
public import Certificates.Certificate4140
public import Certificates.Certificate4141
public import Certificates.Certificate4142
public import Certificates.Certificate4143
public import Certificates.Certificate4155
public import Certificates.Certificate14952
public import Certificates.Certificate3951
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3S23
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem examExcludes_sporadic_rank
    (s : TauCeti.SporadicName) (hs : s = .J2 ∨ s = .HS) :
    ExamExcludes (FamSporadic s) := by
  rintro G _ _ K B B' P R m h ⟨e⟩
  obtain ⟨Ab, hAb, hcard⟩ := h.exists_bar_elem_big
  have hAb' : IsElemAbelian 2 (Ab.map e.toMonoidHom) := isElemAbelian_map' hAb _
  have hc : Nat.card (Ab.map e.toMonoidHom) = Nat.card Ab :=
    card_map_of_inf_ker_eq_bot Ab _ fun x _ hx => (e.map_eq_one_iff).mp hx
  rcases hs with rfl | rfl
  · have h1 := j2_native_rank _ hAb'
    rw [hc] at h1
    omega
  · have h1 := hs_native_rank _ hAb'
    rw [hc] at h1
    omega

theorem examExcludes_evenL3 : ExamExcludes FamEvenL3 := by
  rintro G _ _ K B B' P R m hcfg ⟨f, hf1, hmodel⟩
  by_cases hf : f ≤ 2
  · exact examExcludes_evenL3_small G K B B' P R m hcfg f hf hf1 hmodel
  · exact examExcludes_evenL3_large G K B B' P R m hcfg ⟨f, by omega, hmodel⟩

theorem lemma2_4_23_five_examK_proved
    : Lemma2_4_23_five_examK :=
  examK_of_families
    { alt := examExcludes_alt
      oddL2 := examExcludes_oddL2
      oddL3 := examExcludes_oddL3
      oddU3 := examExcludes_oddU3
      evenL2 := examExcludes_evenL2
      evenL3 := examExcludes_evenL3
      evenU3 := examExcludes_evenU3
      sp4 := examSp4 sp4OddMultiplierTrivial
      g2 := examExcludes_g2
      d4 := examExcludes_d4
      f4 := examExcludes_f4
      sz := examExcludes_sz
      tits := examExcludes_tits
      l4 := examExcludes_l4
      l5 := examExcludes_l5
      sporadic := fun s hs => by
        by_cases hsmall : s = .M11 ∨ s = .M12 ∨ s = .J1
        · exact examExcludes_sporadic_small s hsmall
        · by_cases hmat : s = .M22 ∨ s = .M23
          · exact examExcludes_sporadic_M2x s hmat
          · by_cases hrank : s = .J2 ∨ s = .HS
            · exact examExcludes_sporadic_rank s hrank
            · by_cases hfus : s = .M24 ∨ s = .He ∨ s = .Ru ∨ s = .J4
              · exact examExcludes_sporadic_fusion s hfus
              · exfalso
                rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                  simp at hsmall hmat hrank hfus }

end CFSG.QuasithinUnique.Lin2
