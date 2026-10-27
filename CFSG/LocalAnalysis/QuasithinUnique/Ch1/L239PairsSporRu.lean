module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuGood
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuSelf
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporModel

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Sporadic.RuSchreier CFSG.QuasithinUnique.Vol2Native.L239.RuPairs CFSG.Blueprint

theorem ruP_localPair
    : LocalPair ↥ruP := by
  have hSC : ruS.subgroupOf ruP ≤ ruC.subgroupOf ruP := Subgroup.subgroupOf_mono ruP ruS_leC
  have hSN : ruS.subgroupOf ruP ≤ ruN.subgroupOf ruP := Subgroup.subgroupOf_mono ruP ruS_leN
  have hself : ∀ g : ↥ruP, (ruS.subgroupOf ruP).map (MulAut.conj g).toMonoidHom =
      ruS.subgroupOf ruP → g ∈ ruS.subgroupOf ruP := by
    intro g hg
    obtain ⟨h1, h2⟩ := mem_of_map_conj_eq hg
    refine ruS_selfNormalizing g.2 (fun s hs => ?_) (fun s hs => ?_)
    · exact h1 ⟨s, ruS_le hs⟩ (Subgroup.mem_subgroupOf.2 hs)
    · exact h2 ⟨s, ruS_le hs⟩ (Subgroup.mem_subgroupOf.2 hs)
  have hC : ruC.subgroupOf ruP ≠ ⊤ := fun h => by
    have hle : ruP ≤ ruC := Subgroup.subgroupOf_eq_top.1 h
    have := Subgroup.card_le_of_le hle
    rw [card_ruP, card_ruC] at this
    omega
  have hN : ruN.subgroupOf ruP ≠ ⊤ := fun h => by
    have hle : ruP ≤ ruN := Subgroup.subgroupOf_eq_top.1 h
    have := Subgroup.card_le_of_le hle
    rw [card_ruP, card_ruN] at this
    omega
  refine ⟨ruS.subgroupOf ruP, ruC.subgroupOf ruP, ruN.subgroupOf ruP, ruSylow.isPGroup',
    ruSylow.not_dvd_index, invariant_of_selfNormalizing hSC mulAut_inner hself,
    invariant_of_selfNormalizing hSN mulAut_inner hself, hC, hN, ?_, ruC_goodLocal,
    ruN_goodLocal⟩
  rw [← Subgroup.subgroupOf_sup ruC_le ruN_le, ← ruP_eq_sup, Subgroup.subgroupOf_self]

theorem pairsFor_Ru
    : PairsFor (TypeSporadic .Ru) :=
  pairsFor_of_localPair_equiv .Ru ruEquivP ruP_localPair

end CFSG.QuasithinUnique.Vol2Native.L239
