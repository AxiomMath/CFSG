module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutClosing
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutVPairs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverMore

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78

theorem fi24out_closing_core {H : Type} [Group H] [Finite H] {N L K : Subgroup H} {t u : H}
    (hN : FStarSimple N) (hq : CFSG.IsQuasisimple ↥L) (hodd : Odd (Nat.card ↥(center ↥L)))
    (hstd : StdBare L) (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S)
    (ht2 : orderOf t = 2) (htC : t ∈ centralizer (L : Set H)) (hut : u * t = t * u)
    (h35 : K = componentProduct K u) (hu2 : orderOf u = 2)
    (huN : u ∈ normalizer (L : Set H)) (hunot : u ∉ L ⊔ centralizer (L : Set H))
    (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k) (hKq : CFSG.IsQuasisimple ↥K)
    (hcard : 4089470473293004800 ≤ Nat.card (↥K ⧸ CFSG.oddCore ↥K))
    (hclass : ∀ ν : MulAut (↥L ⧸ center ↥L), ν * ν = 1 → (¬ ∃ g, ν = MulAut.conj g) →
      ∀ B : Subgroup (↥L ⧸ center ↥L), B ≤ fixSubgroup ν → ⁅B, B⁆ = B →
        4089470473293004800 ≤ Nat.card B →
          Fi24OutFacts (↥L ⧸ center ↥L) ν ∧ B = fixSubgroup ν)
    (hacc : AutCenterCond (↥L ⧸ center ↥L)) (hoc : AutOddCoreTrivial (↥L ⧸ center ↥L))
    (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2) : False := by
  classical
  have hLperf : commutator ↥L = ⊤ := Group.isPerfect_def.1 hq.1
  have hu1 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  set ν := normalizerAction L ⟨u, huN⟩ with hν
  have hνν : ν * ν = 1 := Closing.act_mul_self huN hu1
  have hout : ¬ ∃ g, ν = MulAut.conj g := by
    rintro ⟨g, hg⟩
    exact hunot ((normalizerAction_mem_range_conj_iff hLperf ⟨u, huN⟩).1 ⟨g, hg.symm⟩)
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have hB : bar (K.subgroupOf L) ≤ fixSubgroup ν := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy
    have hkK : (k : H) ∈ K := Subgroup.mem_subgroupOf.1 hk
    show ν (k : ↥L ⧸ center ↥L) = k
    rw [hν, Closing.act_mk]
    congr 1
    refine Subtype.ext ?_
    show u * (k : H) * u⁻¹ = k
    calc u * (k : H) * u⁻¹ = ((k : H) * u) * u⁻¹ := by rw [hKu _ hkK]
      _ = k := by group
  have hperf : ⁅bar (K.subgroupOf L), bar (K.subgroupOf L)⁆ = bar (K.subgroupOf L) := by
    unfold bar
    rw [← Subgroup.map_commutator, hK']
  have hcard' : 4089470473293004800 ≤ Nat.card (bar (K.subgroupOf L)) :=
    hcard.trans (card_quotient_oddCore_le_bar hodd hKL)
  obtain ⟨hfacts, hbar⟩ := hclass ν hνν hout _ hB hperf hcard'
  have D : Fi24OutLocalData H L K u huN := ⟨hq, hodd, hu1, hKL, hKq, hKu, hfacts, hbar⟩
  have hhyp38 : centralizer ({u} : Set H) ≤ normalizer (L : Set H) :=
    fi24out_hyp38 h35 D.vPairs_nonempty (D.fusion39 h35) (D.generate hu2)
  have S : Fi24OutSetup H N L t u :=
    ⟨hN, hq, hodd, hstd, hcyc, ht2, htC, hu2, huN, hunot, hut, hhyp38⟩
  have hf := S.sol78Fusion_of_data hacc hoc
  have hex := fi24out_exists_comm_conj D hS2 htC ht2 hut
  exact fi24out_false_of_fusion S (fun t' ht' => fi24out_fusedSet_eq S hf hex ht') D hS2

end CFSG.EvenSporadicStandard.Induction
