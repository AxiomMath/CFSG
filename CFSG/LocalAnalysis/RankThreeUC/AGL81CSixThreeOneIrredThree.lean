module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
public import Certificates.Certificate8171
public import Certificates.Certificate8172
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
import CFSG.RankThree.PartTwo.Toolkit.Bloom
import CFSG.RankThree.PartTwo.KFacts.K74Bloom
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.RankThree.PartOne.S12.LA126
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartOne.S12.BaseNodes
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Subgroup
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem neg_one_not_mem_of_le_statedSL {H : Subgroup (GL (Fin 3) (ZMod 3))}
    (hSL : H ≤ CFSG.Open.StatedSL 3 (ZMod 3)) : (-1 : GL (Fin 3) (ZMod 3)) ∉ H := by
  intro h
  have hdet := (CFSG.RankThree.SubgroupLists.mem_statedSL_iff (-1 : GL (Fin 3) (ZMod 3))).mp
    (hSL h)
  rw [CFSG.RankThree.PartTwo.Toolkit.det_neg_one_GL] at hdet
  exact absurd hdet (by decide)

theorem neg_one_mem_normalizer (F : Subgroup (GL (Fin 3) (ZMod 3))) :
    (-1 : GL (Fin 3) (ZMod 3)) ∈
      Subgroup.normalizer (F : Set (GL (Fin 3) (ZMod 3))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hc : (-1 : GL (Fin 3) (ZMod 3)) * x = x * (-1) := (Commute.neg_one_left x).eq
  have hx : (-1 : GL (Fin 3) (ZMod 3)) * x * (-1)⁻¹ = x := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · intro hmem
    rwa [hx]
  · intro hmem
    rwa [← hx]

theorem eq_statedSL_of_caseB {H : Subgroup (GL (Fin 3) (ZMod 3))}
    (hB : CFSG.RankThree.PartTwo.Toolkit.BloomCaseB H)
    (hneg : (-1 : GL (Fin 3) (ZMod 3)) ∉ H) : H = CFSG.Open.StatedSL 3 (ZMod 3) := by
  rcases hB with h | h
  · exact h
  · rw [h] at hneg
    exact absurd (Subgroup.mem_top (-1 : GL (Fin 3) (ZMod 3))) hneg

theorem isExtNotation_of_caseA {H : Subgroup (GL (Fin 3) (ZMod 3))}
    (hA : CFSG.RankThree.PartTwo.Toolkit.BloomCaseA H)
    (h39 : Nat.card H = 39)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype) :
    IsExtNotation (fun A _ => Nat.card A = 3) (fun B _ => Nat.card B = 13) ↥H := by
  obtain ⟨F, hFH, hFnorm, hFcard, -, -⟩ := hA
  let N : Subgroup ↥H := F.subgroupOf H
  have hNnorm : N.Normal := hFnorm
  have hNcard : Nat.card ↥N = 13 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFH).toEquiv, hFcard]
  have hq3 : Nat.card (↥H ⧸ N) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard, h39] at h
    omega
  have hO : CFSG.pCore 3 ↥H = ⊥ := pCore_eq_bot_of_isIrreducibleMatrixRep hirr
  refine ⟨N, hNnorm, hNcard, hq3, ?_⟩
  rintro ⟨K, hKnorm, hinf, hsup⟩
  have hdisj : Disjoint N K := by
    rw [disjoint_iff_inf_le, hinf]
  have hmul : ((N : Set ↥H) * (K : Set ↥H)) = Set.univ := by
    rw [← Subgroup.normal_mul N K, hsup]
    rfl
  have hcomp : N.IsComplement' K :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hKcard : Nat.card ↥K = 3 := by
    have h := hcomp.card_mul_card
    rw [hNcard, h39] at h
    omega
  have hKp : IsPGroup 3 ↥K := IsPGroup.of_card (n := 1) (by simpa using hKcard)
  have hKle : K ≤ CFSG.pCore 3 ↥H := le_sSup ⟨hKnorm, hKp⟩
  have hKbot : K = ⊥ := le_bot_iff.mp (hO ▸ hKle)
  rw [hKbot, Subgroup.card_bot] at hKcard
  omega

section

theorem card_eq_39_of_caseA {H : Subgroup (GL (Fin 3) (ZMod 3))}
    (hA : CFSG.RankThree.PartTwo.Toolkit.BloomCaseA H)
    (hH : oPPrimeHull 3 H = H)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype) : Nat.card H = 39 := by
  have h78 : Nat.card H ∣ 78 := CFSG.RankThree.PartTwo.Toolkit.card_dvd_78_of_caseA hA
  obtain ⟨F, hFH, -, hFcard, hHN, -⟩ := hA
  have hSL : H ≤ CFSG.Open.StatedSL 3 (ZMod 3) := le_statedSL_of_oPPrimeHull hH
  have hneg : (-1 : GL (Fin 3) (ZMod 3)) ∉ H := neg_one_not_mem_of_le_statedSL hSL
  have hne : H ≠ ⊥ := CFSG.RankThree.PartOne.LA126.ne_bot_of_isIrreducibleMatrixRep H hirr
  have h3 : 3 ∣ Nat.card H := dvd_card_of_oPPrimeHull_of_ne_bot hH hne
  have h13 : 13 ∣ Nat.card H := hFcard ▸ Subgroup.card_dvd_of_le hFH
  have h39 : 39 ∣ Nat.card H := by
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 13) h3 h13
  have hcardN : Nat.card ↥(Subgroup.normalizer (F : Set (GL (Fin 3) (ZMod 3)))) = 78 :=
    CFSG.RankThree.PartTwo.Toolkit.card_normalizer_of_card_13 hFcard
  have hne78 : Nat.card H ≠ 78 := by
    intro hcard
    have hEq : H = Subgroup.normalizer (F : Set (GL (Fin 3) (ZMod 3))) :=
      Subgroup.eq_of_le_of_card_ge hHN (by rw [hcard, hcardN])
    apply hneg
    rw [hEq]
    exact neg_one_mem_normalizer F
  obtain ⟨k, hk⟩ := h39
  have hk2 : k ∣ 2 := by
    rw [hk] at h78
    exact Nat.dvd_of_mul_dvd_mul_left (k := 39) (m := k) (n := 2) (by norm_num) h78
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h | h
  · rwa [h, mul_one] at hk
  · rw [h] at hk
    norm_num at hk
    exact absurd hk hne78

theorem sl3_or_psl2_or_frobenius_of_irreducible_three {H : Subgroup (GL (Fin 3) (ZMod 3))}
    (hH : oPPrimeHull 3 H = H)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype) :
    IsSLType 3 (ZMod 3) (↥H ⧸ CFSG.pCore 3 ↥H) ∨
      IsPSLType 2 (ZMod 3) (↥H ⧸ CFSG.pCore 3 ↥H) ∨
      IsExtNotation (fun A _ => Nat.card A = 3) (fun B _ => Nat.card B = 13)
        (↥H ⧸ CFSG.pCore 3 ↥H) := by
  have hSL : H ≤ CFSG.Open.StatedSL 3 (ZMod 3) := le_statedSL_of_oPPrimeHull hH
  have hneg : (-1 : GL (Fin 3) (ZMod 3)) ∉ H := neg_one_not_mem_of_le_statedSL hSL
  have hO : CFSG.pCore 3 ↥H = ⊥ := pCore_eq_bot_of_isIrreducibleMatrixRep hirr
  let e : (↥H ⧸ CFSG.pCore 3 ↥H) ≃* ↥H :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hirrOn : CFSG.RankThree.SubgroupLists.IsIrreducibleOn H :=
    CFSG.RankThree.SubgroupLists.isIrreducibleOn_iff.mpr hirr
  rcases (CFSG.RankThree.PartTwo.Toolkit.toolkit_clause2 H hirrOn).1 with hA | hB | hC
  · exact Or.inr (Or.inr (IsExtNotation.of_mulEquiv
      (fun V V' _ _ f hf => (Nat.card_congr f.toEquiv).symm.trans hf)
      (fun V V' _ _ f hf => (Nat.card_congr f.toEquiv).symm.trans hf)
      e.symm (isExtNotation_of_caseA hA (card_eq_39_of_caseA hA hH hirr) hirr)))
  · have hEq : H = CFSG.Open.StatedSL 3 (ZMod 3) := eq_statedSL_of_caseB hB hneg
    exact Or.inl ⟨e.trans ((MulEquiv.subgroupCongr hEq).trans
      (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 3)))⟩
  · obtain ⟨G₀, ⟨eG⟩, hclos⟩ :=
      CFSG.RankThree.PartTwo.KFacts.closure_threeElements_of_caseC hC
    have hHG₀ : H ≤ G₀ := by
      rw [← hH, oPPrimeHull]
      calc Subgroup.closure {x | x ∈ H ∧ ∃ k, orderOf x = 3 ^ k}
          ≤ Subgroup.closure {g | g ∈ H ∧ ∃ k, g ^ 3 ^ k = 1} := by
            refine Subgroup.closure_mono ?_
            rintro x ⟨hxH, k, hk⟩
            exact ⟨hxH, k, by rw [← hk]; exact pow_orderOf_eq_one x⟩
        _ = G₀ := hclos
    have hG₀H : G₀ ≤ H := by
      rw [← hclos]
      exact Subgroup.closure_le _ |>.mpr fun x hx => hx.1
    have hEq : H = G₀ := le_antisymm hHG₀ hG₀H
    exact Or.inr (Or.inl
      (CFSG.LocalAnalysis.RankThreeUC.AGL81C.isPSLType_two_three_of_mulEquiv_alternatingGroup
        (e.trans ((MulEquiv.subgroupCongr hEq).trans eG))))

end

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
