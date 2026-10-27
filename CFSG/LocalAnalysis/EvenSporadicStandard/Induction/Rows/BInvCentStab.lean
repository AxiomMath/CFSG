module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentGeneric
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentData
public import Certificates.Certificate27200
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.Census
public import CFSG.Monster.B.Cbar.LocalAux

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.Short CFSG.Monster.SpinLattice
  CFSG.Monster.Griess
open CFSG.Monster.B.CTIB.Native (censusWord fixesBasis movesBasis a5WordA a5WordB a5Cycle a5OK)

attribute [local instance] kvLeft

section


@[expose] noncomputable def censusElt : List ℕ → KS
  | [] => 1
  | k :: w => censusElt w * censusGen k

end

section


theorem censusElt_append (w₁ w₂ : List ℕ) :
    censusElt (w₁ ++ w₂) = censusElt w₂ * censusElt w₁ := by
  induction w₁ with
  | nil => simp [censusElt]
  | cons k w ih => rw [List.cons_append, censusElt, ih, censusElt, mul_assoc]

end

section


theorem vecW_censusWord {w : List ℕ} (hw : ∀ k ∈ w, k < 2) (v : ℕ) :
    vecW (censusWord w v) = censusElt w • vecW v := by
  induction w generalizing v with
  | nil => simp [censusWord, censusElt]
  | cons k w ih =>
    rw [censusWord, ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')),
      vecW_censusAct (hw k List.mem_cons_self), censusElt, mul_smul]

end

theorem vecW_two_pow (i : Fin 22) : vecW (2 ^ (i : ℕ)) = Multiplicative.toAdd (psiBar (eE i)) := by
  rw [vecW, psiS_qS_fin, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : (i : ℕ) ≠ j := fun h => hj (Fin.ext h.symm)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem vecW_eq_sum (n : ℕ) :
    vecW n = ∑ i : Fin 22, (if n.testBit i then (1 : ZMod 2) else 0) • vecW (2 ^ (i : ℕ)) := by
  rw [vecW, psiS_qS_fin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vecW_two_pow i]

section


theorem eq_one_of_smul_basis (k : KS) (h : ∀ i < 22, k • vecW (2 ^ i) = vecW (2 ^ i)) : k = 1 := by
  have hk : wAct _ k⁻¹ = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨n, -, rfl⟩ := exists_vecW w
    rw [vecW_eq_sum n, map_sum, Module.End.one_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    have := h i i.2
    rw [kvLeft_smul] at this
    rw [this]
  have h1 : k⁻¹ = 1 := by
    apply KvAct_injective_rStar
    show MulOpposite.op (wAct _ k⁻¹) = KvAct _ 1
    rw [map_one, hk]
    rfl
  exact inv_eq_one.1 h1

end

section


theorem censusElt_eq_one_of_fixesBasis {w : List ℕ} (hw : ∀ k ∈ w, k < 2)
    (h : fixesBasis w = true) : censusElt w = 1 := by
  apply eq_one_of_smul_basis
  intro i hi
  rw [← vecW_censusWord hw]
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [beq_iff_eq] at this
  rw [this]

end

section


theorem censusElt_ne_one_of_movesBasis {w : List ℕ} (hw : ∀ k ∈ w, k < 2)
    (h : movesBasis w = true) : censusElt w ≠ 1 := by
  intro h1
  obtain ⟨i, hi, hmv⟩ := List.any_eq_true.1 h
  have hi22 : i < 22 := List.mem_range.1 hi
  rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_iff] at hmv
  obtain ⟨hne, hlt⟩ := hmv
  have h2 := vecW_censusWord hw (2 ^ i)
  rw [h1, one_smul] at h2
  have hlt2 : 2 ^ i < 2 ^ 22 := Nat.pow_lt_pow_right (by norm_num) hi22
  exact hne (vecW_injOn (Set.mem_Iio.2 hlt) (Set.mem_Iio.2 hlt2) h2)

end

section


theorem exists_a5_stab :
    ∃ P : Subgroup KS, Nontrivial P ∧ Group.IsPerfect P ∧ ∀ k ∈ P, k • vecW 7 = vecW 7 := by
  have h := Certificates.certificate27200
  unfold a5OK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hwa : ∀ k ∈ a5WordA, k < 2 := fun k hk => of_decide_eq_true (List.all_eq_true.1 hA k hk)
  have hwb : ∀ k ∈ a5WordB, k < 2 := fun k hk => of_decide_eq_true (List.all_eq_true.1 hB k hk)
  have hwc : ∀ k ∈ a5Cycle, k < 2 := fun k hk => by
    rcases List.mem_append.1 hk with h | h
    · exact hwb k h
    · exact hwa k h
  have hA2 : censusElt a5WordA * censusElt a5WordA = 1 := by
    have := censusElt_eq_one_of_fixesBasis (List.forall_mem_append.2 ⟨hwa, hwa⟩) h1
    rwa [censusElt_append] at this
  have hB3 : censusElt a5WordB * censusElt a5WordB * censusElt a5WordB = 1 := by
    have := censusElt_eq_one_of_fixesBasis
      (List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨hwb, hwb⟩, hwb⟩) h2
    rw [censusElt_append, censusElt_append] at this
    rwa [← mul_assoc] at this
  have hcyc : censusElt a5Cycle = censusElt a5WordA * censusElt a5WordB := by
    rw [a5Cycle, censusElt_append]
  have hAB5 : (censusElt a5WordA * censusElt a5WordB) ^ 5 = 1 := by
    have := censusElt_eq_one_of_fixesBasis
      (List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2
        ⟨List.forall_mem_append.2 ⟨hwc, hwc⟩, hwc⟩, hwc⟩, hwc⟩) h3
    simp only [censusElt_append, hcyc] at this
    generalize censusElt a5WordA * censusElt a5WordB = C at this ⊢
    calc C ^ 5 = C * (C * (C * (C * C))) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hA1 : censusElt a5WordA ≠ 1 := censusElt_ne_one_of_movesBasis hwa h4
  have hfix : ∀ {w : List ℕ}, (∀ k ∈ w, k < 2) → (censusWord w 7 == 7) = true →
      censusElt w • vecW 7 = vecW 7 := fun {w} hw hc => by
    rw [← vecW_censusWord hw, beq_iff_eq.1 hc]
  have hAfix := hfix hwa h5
  have hBfix := hfix hwb h6
  have hAmem : censusElt a5WordA ∈ Subgroup.closure ({censusElt a5WordA, censusElt a5WordB} :
      Set KS) := Subgroup.subset_closure (Set.mem_insert _ _)
  refine ⟨Subgroup.closure ({censusElt a5WordA, censusElt a5WordB} : Set KS), ⟨⟨⟨_, hAmem⟩, 1,
    fun h => hA1 (congrArg Subtype.val h)⟩⟩, isPerfect_closure_pair hA2 hB3 hAB5, fun k hk => ?_⟩
  have hle : Subgroup.closure ({censusElt a5WordA, censusElt a5WordB} : Set KS) ≤
      MulAction.stabilizer KS (vecW 7) := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with h | h
    · rw [h]
      exact hAfix
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact hBfix
  exact hle hk

end

end CFSG.EvenSporadicStandard.Induction.Hyp
