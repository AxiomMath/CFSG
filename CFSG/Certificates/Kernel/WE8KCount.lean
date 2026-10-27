
module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8ClassesBase
public import CFSG.RankThree.Chevalley.SteinbergBIWE8Enum

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.WE8.Native

@[expose] def oneCode : ICode := List.ofFn fun i : Fin 8 => rootIdx (basisV i)

@[expose] def zNegOK (i : ℕ) : Bool :=
  !(negI (frameCode (frameData.getD i [])) == oneCode) &&
    WE8.Native.negCount (negI (frameCode (frameData.getD i []))) ==
      negCounts.getD (zClass.getD i 0) 0

@[expose] def simpleNegOK (j : ℕ) : Bool :=
  !(wordCode [j] == oneCode) && WE8.Native.negCount (wordCode [j]) == negCounts.getD 0 0

theorem zNegOK_all : ∀ i < 8, zNegOK i = true := by
  decide +kernel

theorem simpleNegOK_all : ∀ j < 8, simpleNegOK j = true := by
  decide +kernel

theorem zClass_lt_nine : ∀ i < 8, zClass.getD i 0 < 9 := by
  decide

theorem nInv_eq_negCount (t : W8) :
    nInv t = WE8.Native.negCount (code t) / 2 := by
  rw [nInv, ncard_rootsV_negSpace, negCount_code]

theorem classes_of_bounds
    (hlow : ∀ i < 9, classSizes.getD i 0 ≤ Nat.card {u : W8 // IsConj (rep i) u})
    (hsym : Nat.card {w : W8 // SgnSym 1 w} ≤ 199952) :
    (∀ i < 9, Nat.card {u : W8 // IsConj (rep i) u} = classSizes.getD i 0) ∧
      ∀ t : W8, t * t = 1 → t ≠ 1 → ∃ i < 9, IsConj (rep i) t := by
  classical
  let _ : Fintype W8 := Fintype.ofFinite W8
  let C : ℕ → Finset W8 := fun i => Finset.univ.filter (IsConj (rep i))
  let S : Finset W8 := Finset.univ.filter fun w => w * w = 1
  have hC : ∀ i, (C i).card = Nat.card {u : W8 // IsConj (rep i) u} := fun i => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hdisj : ((Finset.range 9 : Finset ℕ) : Set ℕ).PairwiseDisjoint C := by
    intro i hi j hj hij
    refine Finset.disjoint_left.2 fun w hwi hwj => hij ?_
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    exact nList_inj i hi' j hj' ((nInv_of_isConj hi' (Finset.mem_filter.1 hwi).2).symm.trans
      (nInv_of_isConj hj' (Finset.mem_filter.1 hwj).2))
  have h1 : (1 : W8) ∉ (Finset.range 9).biUnion C := by
    intro h
    obtain ⟨i, hi, h1i⟩ := Finset.mem_biUnion.1 h
    obtain ⟨u, hu⟩ := isConj_iff.1 (Finset.mem_filter.1 h1i).2
    refine rep_ne_one (Finset.mem_range.1 hi) ?_
    have : rep i = u⁻¹ * (u * rep i * u⁻¹) * u := by group
    rw [this, hu, mul_one, inv_mul_cancel]
  have hcardU : (insert 1 ((Finset.range 9).biUnion C)).card =
      (∑ i ∈ Finset.range 9, (C i).card) + 1 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_biUnion hdisj]
  have hsumS : ∑ i ∈ Finset.range 9, classSizes.getD i 0 = 199951 := by
    rw [← sum_classSizes, ← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
  have hsub : insert 1 ((Finset.range 9).biUnion C) ⊆ S := by
    intro w hw
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact mul_one 1
    · obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.1 hw
      obtain ⟨u, rfl⟩ := isConj_iff.1 (Finset.mem_filter.1 hwi).2
      exact conj_mul_self (rep_mul_self (Finset.mem_range.1 hi)) u
  have hS : S.card ≤ 199952 := by
    have hle : Nat.card {w : W8 // w * w = 1} ≤ Nat.card {w : W8 // SgnSym 1 w} :=
      Nat.card_le_card_of_injective (fun w => ⟨w.1, sym_of_sq_eq_one w.2⟩)
        fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hle
    exact hle.trans hsym
  have hlow' : ∀ i ∈ Finset.range 9, classSizes.getD i 0 ≤ (C i).card := fun i hi => by
    rw [hC]
    exact hlow i (Finset.mem_range.1 hi)
  have hge := Finset.sum_le_sum hlow'
  have hle : ∑ i ∈ Finset.range 9, (C i).card ≤ 199951 := by
    have := (Finset.card_le_card hsub).trans hS
    rw [hcardU] at this
    omega
  have heqs := (Finset.sum_eq_sum_iff_of_le hlow').1 (by omega)
  refine ⟨fun i hi => by rw [← hC]; exact (heqs i (Finset.mem_range.2 hi)).symm,
    fun t ht ht1 => ?_⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcardU]; omega)
  have htS : t ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩
  rw [← heq] at htS
  rcases Finset.mem_insert.1 htS with h | h
  · exact absurd h ht1
  · obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.1 h
    exact ⟨i, Finset.mem_range.1 hi, (Finset.mem_filter.1 hti).2⟩

theorem card_y0_of_bounds
    (hy : 15120 ≤ Nat.card {u : W8 // IsConj y0 u})
    (hskew : Nat.card {w : W8 // SgnSym (-1) w} ≤ 15120) :
    Nat.card {u : W8 // IsConj y0 u} = 15120 := by
  refine le_antisymm ?_ hy
  have h1 : Nat.card {u : W8 // IsConj y0 u} ≤ Nat.card {w : W8 // w * w = z} :=
    Nat.card_le_card_of_injective
      (fun u => ⟨u.1, by obtain ⟨g, hg⟩ := isConj_iff.1 u.2; rw [← hg]; exact conj_y0_sq g⟩)
      fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
  have h2 : Nat.card {w : W8 // w * w = z} ≤ Nat.card {w : W8 // SgnSym (-1) w} :=
    Nat.card_le_card_of_injective (fun w => ⟨w.1, skew_of_sq_eq_neg (sq_eq_z_smul w.2)⟩)
      fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
  exact (h1.trans h2).trans hskew

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint in
open CFSG.LieType.Chevalley.WE8.Native CFSG.RankThree.Chevalley.WeylE8 in
theorem cert18004_of_bounds
    (hlow : ∀ i < 9, classSizes.getD i 0 ≤ Nat.card {u : W8 // IsConj (rep i) u})
    (hy : 15120 ≤ Nat.card {u : W8 // IsConj y0 u})
    (hsym : Nat.card {w : W8 // SgnSym 1 w} ≤ 199952)
    (hskew : Nat.card {w : W8 // SgnSym (-1) w} ≤ 15120) :
    (∀ i < 9, Nat.card {u : W8 // IsConj (rep i) u} = classSizes.getD i 0) ∧
    (∀ i < 8, IsConj (rep (zClass.getD i 0)) (rep 8 * rep i)) ∧
    (∀ j : Fin Tag.E8.rank, IsConj (rep 0) (simple .E8 j)) ∧
    Nat.card {u : W8 // IsConj y0 u} = 15120 ∧
    Nat.card {w : W8 // SgnSym 1 w} ≤ 199952 ∧ Nat.card {w : W8 // SgnSym (-1) w} ≤ 15120 := by
  obtain ⟨hcard, hcls⟩ := classes_of_bounds hlow hsym
  have pick : ∀ t : W8, ∀ k < 9, t * t = 1 → code t ≠ oneCode →
      WE8.Native.negCount (code t) = negCounts.getD k 0 → IsConj (rep k) t := by
    intro t k hk ht hc hn
    have ht1 : t ≠ 1 := fun h => hc (by rw [h]; exact code_one)
    obtain ⟨m, hm, hmt⟩ := hcls t ht ht1
    have e1 := nInv_of_isConj hm hmt
    rw [nInv_eq_negCount, hn, negCounts_eq k hk] at e1
    obtain rfl := nList_inj k hk m hm e1
    exact hmt
  refine ⟨hcard, fun i hi => ?_, fun j => ?_, card_y0_of_bounds hy hskew, hsym, hskew⟩
  · have hz := zNegOK_all i hi
    simp only [zNegOK, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at hz
    have hc : code (rep 8 * rep i) = negI (frameCode (frameData.getD i [])) := by
      rw [code_neg z_smul, code_rep (by omega)]
    have hcomm := z_mul_comm (rep i)
    have hsq : rep 8 * rep i * (rep 8 * rep i) = 1 :=
      calc rep 8 * rep i * (rep 8 * rep i) = rep 8 * (rep i * rep 8) * rep i := by group
        _ = rep 8 * (rep 8 * rep i) * rep i := by rw [← hcomm]
        _ = rep 8 * rep 8 * (rep i * rep i) := by group
        _ = 1 := by rw [z_mul_z, rep_mul_self (by omega), one_mul]
    exact pick _ _ (zClass_lt_nine i hi) hsq (by rw [hc]; exact hz.1) (by rw [hc]; exact hz.2)
  · have hs := simpleNegOK_all j j.2
    simp only [simpleNegOK, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      beq_iff_eq] at hs
    have hc : code (simple .E8 j) = wordCode [(j : ℕ)] := by
      have := code_wordProd [j]
      rw [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one] at this
      exact this
    exact pick _ 0 (by decide) ((coxeterSystem .E8).simple_mul_simple_self j)
      (by rw [hc]; exact hs.1) (by rw [hc]; exact hs.2)

end CFSG.RankThree.Chevalley.WeylE8
