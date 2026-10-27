module

public import CFSG.RankThree.Native.PermEnumeration
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Certificates.Native

variable {n : ℕ}

theorem getElem!_rawInvs_of_lt {S : Array (Array ℕ)} {j : ℕ} (hj : j < S.size) :
    (rawInvs n S)[j]! = invCand n S[j]! := by
  rw [rawInvs, getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem validA_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    validA n t = true := by
  have hr := rep_invCand_of_rep ht
  rw [validA, isInvA, CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr.apply (g ⟨i, hi⟩).2]
  simp

theorem wordA_mem_closure {gs : Array (Array ℕ)} (hgs : ∀ k < gs.size, validA n gs[k]! = true) :
    ∀ w : List ℤ, lettersOK gs.size w = true →
      Rep n (wordA n gs (rawInvs n gs) w) (permOfArr n (wordA n gs (rawInvs n gs) w)) ∧
        permOfArr n (wordA n gs (rawInvs n gs) w) ∈ Subgroup.closure (permsA n gs)
  | [], _ => by
    refine ⟨?_, ?_⟩
    · have h := rep_idA (n := n)
      rwa [← permOfArr_eq_of_rep h] at h
    · rw [wordA, permOfArr_eq_of_rep (rep_idA (n := n))]
      exact Subgroup.one_mem _
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK gs.size w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨ih1, ih2⟩ := wordA_mem_closure hgs w hw'
    have hk : l.natAbs - 1 < gs.size := by omega
    have hrep := rep_of_validA (hgs _ hk)
    have hinv := rep_inv_of_validA (hgs _ hk)
    have hmem : permOfArr n gs[l.natAbs - 1]! ∈ Subgroup.closure (permsA n gs) :=
      Subgroup.subset_closure ⟨l.natAbs - 1, hk, rfl⟩
    have hlet : Rep n (letterA gs (rawInvs n gs) l)
        (permOfArr n (letterA gs (rawInvs n gs) l)) ∧
        permOfArr n (letterA gs (rawInvs n gs) l) ∈ Subgroup.closure (permsA n gs) := by
      unfold letterA
      by_cases hpos : 0 < l
      · rw [ite_eq_left hpos]
        have e : l.toNat - 1 = l.natAbs - 1 := by omega
        rw [e]
        exact ⟨hrep, hmem⟩
      · rw [ite_eq_right hpos]
        have e : (-l).toNat - 1 = l.natAbs - 1 := by omega
        rw [e, getElem!_rawInvs_of_lt hk]
        rw [permOfArr_eq_of_rep hinv]
        exact ⟨hinv, Subgroup.inv_mem _ hmem⟩
    have hprod := rep_compA hlet.1 ih1
    refine ⟨?_, ?_⟩
    · rw [wordA, permOfArr_eq_of_rep hprod]
      exact hprod
    · rw [wordA, permOfArr_eq_of_rep hprod]
      exact Subgroup.mul_mem _ hlet.2 ih2

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
