module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenCount
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenClasses

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

theorem JankoEleven.jankoProp11 {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z}
    (hz : orderOf z = 2) (p7 : JankoProp7 fr) (p10 : JankoProp10 fr) : JankoProp11 fr where
  card_N := JankoEleven.card_N p10
  N_pow_three := JankoEleven.N_pow_three p7 p10 hz
  isSylowOf_N := JankoEleven.isSylowOf_N p7 p10
  normalizer_N_inf := JankoEleven.normalizer_N_inf p7 p10
  N_inf_centralizer_z := JankoEleven.N_inf_centralizer_z p10
  N_inf_centralizer_t := JankoEleven.N_inf_centralizer_t p7 p10
  card_ZN := JankoEleven.card_ZN p7 p10 hz
  ZN_le_M := JankoEleven.ZN_le_M p10
  card_P3bar := JankoEleven.card_P3bar p7 p10 hz
  card_P3bbar := JankoEleven.card_P3bbar p7 p10 hz
  ZN_eq := JankoEleven.ZN_eq p7 p10 hz
  commutator_N := JankoEleven.commutator_N p7 p10 hz
  card_I := JankoEleven.card_I p7 p10 hz
  I_comm := JankoEleven.I_comm
  N_le_normalizer_I := JankoEleven.N_le_normalizer_I p7 p10 hz
  L_le_normalizer_I := JankoEleven.L_le_normalizer_I p7
  N_inf_normalizer_E := JankoEleven.N_inf_normalizer_E p7 p10 hz
  normalizer_P₁_le := JankoEleven.normalizer_P₁_le_normalizer_Mbar p7 p10 hz
  isConj_of_mem_Mbar := JankoEleven.isConj_of_mem_Mbar p7 p10 hz
  exists_conj_ZN := JankoEleven.exists_conj_ZN p7 p10 hz
  exists_conj_M := JankoEleven.exists_conj_M p7 p10 hz
  M_inf_centralizer := JankoEleven.M_inf_centralizer p7 p10 hz
  card_abelian := JankoEleven.card_abelian p7 p10 hz
  centralizer_E := JankoEleven.centralizer_E p7 p10 hz

theorem jankoStep11 : JankoStep11 := fun _ _ _ _ _ hset _ p7 _ p10 =>
  JankoEleven.jankoProp11 hset.orderOf_z p7 p10

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
