module

public import CFSG.GF2Type.Smith1979.ParrottTh
public import CFSG.Sporadic.Th.Recog.A9Mod.Classify
public import CFSG.Sporadic.Th.Recog.MFactsB.ConjThree
public import CFSG.Sporadic.Th.Recog.MFactsB.ConjThreeSound
public import CFSG.Sporadic.Th.Recog.MFactsB.E8
public import CFSG.Sporadic.Th.Recog.MFactsB.G1
public import CFSG.Sporadic.Th.Recog.MFactsB.RowsSound
public import CFSG.Sporadic.Th.Recog.MFactsB.Seven

public section

namespace CFSG.GF2Type.Smith1979

open CFSG.Sporadic.Th.Recog


theorem parrottThKP_holds : ParrottThKP :=
  parrottThKP_of_glueMFacts a9FaithfulDimEight_holds ({ card_centralizer_t := card_centralizer_t,
                                                        conj_three := MFactsB.conj_three_of
                                                            MFactsB.ω₁_comm_ω₂
                                                            MFactsB.eq_one_or_eq_z_of_comm_ω₁_mul_ω₂
                                                            MFactsB.eq_one_or_eq_z_of_comm_ω₁,
                                                        g1 := ⟨MFactsB.H₁, MFactsB.H₂,
                                                            MFactsB.mg1_of MFactsB.y₁_mul_x₁
                                                            MFactsB.ω₁_mul_y₁ MFactsB.x₁_comm_x₂
                                                            MFactsB.x₁_comm_ω₂ MFactsB.ω₁_comm_x₂
                                                            MFactsB.ω₁_comm_ω₂⟩,
                                                        complement_t := MFactsB.exists_complement_t,
                                                        center_t := center_t,
                                                        e8 := ⟨MFactsB.E₀, MFactsB.e₀,
                                                            MFactsB.e8Facts_of MFactsB.e₀_comm_e₁
                                                            MFactsB.e8_injective
                                                            MFactsB.nE_comm_tLetter
                                                            MFactsB.nE_conj_e₀ MFactsB.nE_conj_e₁
                                                            MFactsB.eq_e8_of_commute_pre_mul
                                                            MFactsB.cE_comm_e₀ MFactsB.cN_comm_e₀
                                                            MFactsB.of_commute_e₀⟩,
                                                        seven := seven_of_card_Q_inf_centralizer_s
                                                            MFactsB.card_Q_inf_centralizer_s,
                                                        card_D8 := card_D8M })

end CFSG.GF2Type.Smith1979
