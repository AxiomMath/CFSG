module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanHost
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanNormal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanBalance
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanPair
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanSign
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanSpare
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanPump

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open scoped commutatorElement

theorem false_of_onanWConfig (hcat : SuzONanNotProperFixedCatalog)
    (hGold : GoldschmidtStronglyClosedInput) (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple)
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G} (hc : ONanWConfig G t P W) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalizer (W : Set G) with hM
  have htM : t ∈ M := hc.mem_normalizer
  have hCM : centralizer ({t} : Set G) ≤ M := hc.centralizer_le
  have hPM : P ≤ M := hc.le_normalizer'
  have hbase := hc.base
  have ht2 := hc.order_two
  have hPt := hc.le_centralizer
  have hPp := hc.isPComponent
  have hPON := hc.isSporadic
  set s : ↥M := ⟨t, htM⟩ with hsdef
  have hs : orderOf s = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  set Λ := P.subgroupOf M with hΛdef
  have hΛs : Λ ≤ centralizer ({s} : Set ↥M) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hPt (mem_subgroupOf.mp hx))
  have hΛ : IsPComponent 2 (Λ.subgroupOf (centralizer ({s} : Set ↥M))) := by
    rw [hsdef, FooteLit.centralizer_mk_eq htM,
      UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two,
      inf_of_le_left hCM]
    exact hPp
  have hΛON : IsSporadic (↥Λ ⧸ Open.fusionZStar ↥Λ) .ONan := by
    obtain ⟨f⟩ := hPON
    exact ⟨(Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hPM).symm).symm.trans f⟩
  obtain ⟨L, hL, hZ, hLON, hone, htwo⟩ :=
    exists_component_on_of_twoComponent hcat hc.isKGroupCat hs hΛs hΛ hΛON
  by_cases hLt : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) s)).toMonoidHom = L
  · obtain ⟨hPL, hcent⟩ := hone hLt
    by_cases hLn : L.Normal
    · exact false_of_onan_normal_component hGold hc hM htM hL hLn hZ hLON hPL hcent
    · exact false_of_onan_one_factor h13 hc hM htM hL hLn hZ hLON hPL hcent
  · obtain ⟨hPL, hPL1, hPL2⟩ := htwo hLt
    by_cases hpair : ∀ x : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj x).toMonoidHom = L ∨
        L.map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) s)).toMonoidHom
    · obtain ⟨hodd, hfus⟩ := onan_pair_sylow_fusion hc hM htM hL hZ hLON hLt hpair
      obtain ⟨H, hHM, hH2, htH⟩ := exists_index_two_of_pair htM hLt hpair
      have := hbase.1
      have hperf : Group.IsPerfect G :=
        OrderReductions.Helpers.simple_noncommutative_isPerfect G fun hcomm => by
          obtain ⟨g, k, hgk⟩ := hbase.2.1
          exact hgk (hcomm.is_comm.comm g k)
      have htt : t * t = 1 := by
        have h := pow_orderOf_eq_one t
        rwa [ht2, pow_two] at h
      exact false_of_index_two_of_fusion hperf hHM hH2 hodd htt htM htH hfus
    · push Not at hpair
      obtain ⟨v, hvM, hv, htv, hvL⟩ :=
        exists_involution_centralizing_pair hc hM htM hL hZ hLON hLt hpair
      have hvP := commutator_mem_oddIn_of_centralizes hc hM htM hPL hvM htv hvL
      obtain ⟨Q, hQv, hQ, hQn, hDQ, hQW, hQON⟩ :=
        exists_onan_pump_le_normalizer hS hCI hGA h13 hc hv htv hvP
      exact false_of_onan_pump hS hc hM htM hL hZ hLON hLt hPL hPL1 hPL2 hvM hv htv hvL hQv hQ
        hQn hDQ hQW hQON

end CFSG.ComponentClassification.GrSLit.L34Sec5S
