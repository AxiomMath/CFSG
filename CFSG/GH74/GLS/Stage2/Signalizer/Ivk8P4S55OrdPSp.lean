module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55OrdPL
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3Sp
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace OrdPSp

theorem ordP_psp4 {r f : ℕ} [hr : Fact r.Prime] {K : Type} [Field K] [CharP K r]
    [Finite (StatedProj (StatedSp 2 K))] (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (α : MulAut (StatedProj (StatedSp 2 K))) (hα : orderOf α = p) :
    OrdPConcl r (StatedProj (StatedSp 2 K)) α := by
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hr.out hf
      (le_refl 2) hK
  have hαp : α ^ p = 1 := hα ▸ pow_orderOf_eq_one α
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hE : α ∈ spSemilinearAutGroup 2 K := by
    refine CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two _
      (Nat.le_of_dvd (by norm_num) hidx) hpodd ?_
    rw [hαp]
    exact Subgroup.one_mem _
  by_cases hD : α ∈ spLinearAutGroup 2 K
  · right
    have hle : ((inner (StatedProj (StatedSp 2 K))).subgroupOf (spLinearAutGroup 2 K)).index ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (hrel.trans (Nat.gcd_dvd_left 2 _))
    have hmem := CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two
      ((inner (StatedProj (StatedSp 2 K))).subgroupOf (spLinearAutGroup 2 K)) hle hpodd
      (α := (⟨α, hD⟩ : ↥(spLinearAutGroup 2 K))) (N := p) (by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        change α ^ p ∈ inner (StatedProj (StatedSp 2 K))
        rw [hαp]
        exact Subgroup.one_mem _)
    exact Subgroup.mem_subgroupOf.mp hmem
  · left
    obtain ⟨-, σ, -, -, h, hh, hαh⟩ := hdesc p hp α hE hD hα
    obtain ⟨H, rfl⟩ := mem_spLinearAutGroup_iff.mp hh
    rw [hαh]
    exact StepH3Sp.exists_rgroup_of_field H σ

end OrdPSp

theorem ordPInner_fsp4d : OrdPInner FSp4d := by
  intro r p Y _ _ hr _ hp hp5 _ hY b hb
  obtain ⟨f, hf, hLM⟩ := hY
  have hcm : StatedClassicalModel Y .PSp 2 r f := by
    rcases hLM with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K r :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv Y e.toEquiv
  change OrdPConcl r Y b
  apply OrdPConcl.of_mulEquiv e
  exact OrdPSp.ordP_psp4 hf hK hp hp5 _ ((MulEquiv.orderOf_eq (MulAut.congr e) b).trans hb)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
