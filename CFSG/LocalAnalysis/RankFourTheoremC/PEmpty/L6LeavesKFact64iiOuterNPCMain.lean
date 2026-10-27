module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPCSemi
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.GroupTheory.FrobeniusNormalComplement

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open L6LeavesKF64iiNPC

theorem kFact64iiOuterNPC_of_outerSylow (h : KFact64iiOuterSylow) : KFact64iiOuterNPC := by
  intro p hp hp3 K _ _ hsimple hnab hcat hrk φ hφ hφinn
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup K := hsimple
  have hp1 : 1 < p := hp.one_lt
  have hp2 : p ≠ 2 := by omega
  obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup K)
  rw [hrk, pow_one] at hEcard
  have hpK : p ∣ Nat.card K := by
    have hdvd := Subgroup.card_subgroup_dvd_card E
    rwa [hEcard] at hdvd
  have hcyc : ∀ P : Sylow p K, IsCyclic (P : Subgroup K) := fun P => by
    refine CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hp hp2
      (le_top : (P : Subgroup K) ≤ ⊤) P.isPGroup' ?_
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact le_of_eq hrk
  have hmov := h p hp hp3 K hsimple hnab hcat hrk φ hφ hφinn
  obtain ⟨w, r, hw, hr, hrord, hwr, hwrne⟩ :=
    exists_fixed_normalizing hnab hp2 hpK hcyc φ hφ hmov
  let C : Subgroup K :=
    { carrier := {g : K | φ g = g}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hC : Subgroup.closure {g : K | φ g = g} = C := Subgroup.closure_eq C
  rw [hC]
  intro hNPC
  have hcrit := (CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer p).1 hNPC
  have hwC : w ∈ C := hw
  have hrC : r ∈ C := hr
  set w' : C := ⟨w, hwC⟩ with hw'
  set r' : C := ⟨r, hrC⟩ with hr'
  set Q : Subgroup C := Subgroup.zpowers r' with hQ
  have hr'ord : orderOf r' = p := by rw [hr', Subgroup.orderOf_mk, hrord]
  have hQp : IsPGroup p Q :=
    IsPGroup.of_card (n := 1) (by rw [hQ, Nat.card_zpowers, hr'ord, pow_one])
  have hwr' : w' * r' * w'⁻¹ ∈ Q := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hwr
    exact Subgroup.mem_zpowers_iff.2 ⟨i, Subtype.ext (by simpa using hi)⟩
  have hwr'' : w'⁻¹ * r' * w' ∈ Q := inv_mul_mul_mem_zpowers hwr'
  have hw'N : w' ∈ Subgroup.normalizer (Q : Set C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ hwr' i
    · intro hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h1 : x = w'⁻¹ * r' ^ i * w' := by rw [hi]; group
      have h2 : w'⁻¹ * r' ^ i * w' = (w'⁻¹ * r' * w') ^ i := by
        simpa using (conj_zpow (a := w'⁻¹) (b := r') (i := i)).symm
      rw [h1, h2]
      exact Subgroup.zpow_mem _ hwr'' i
  obtain ⟨c, hc⟩ := hcrit Q hQp (QuotientGroup.mk ⟨w', hw'N⟩)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hc
  have hcomm : w' ^ (p ^ c) * r' = r' * w' ^ (p ^ c) := by
    have h1 := Subgroup.mem_centralizer_iff.1 hc r' (Subgroup.mem_zpowers r')
    simpa using h1.symm
  have h3 : w' * r' = r' * w' := commute_of_pow_prime_pow hr'ord hwr' hcomm
  apply hwrne
  have h4 : w * r = r * w := congrArg Subtype.val h3
  calc w * r * w⁻¹ = r * w * w⁻¹ := by rw [h4]
    _ = r := by group

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
