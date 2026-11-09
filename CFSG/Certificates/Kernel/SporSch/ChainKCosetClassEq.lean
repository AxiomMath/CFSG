module

public import CFSG.Certificates.Kernel.SporSch.ChainKClassEq
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MBT
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu

@[expose] noncomputable def cosetRepK (n w m nw BP k : Nat) (LR TR TRI : Nat → Nat)
    (G₀ X C : Nat) : Bool :=
  canonK n w m nw X && canonK n w m nw (pcomp n w m (pinvS n w m G₀) X) &&
    siftK n w m nw (pidn n w) LR TRI BP k (nat_lit 0) (pcomp n w m (pinvS n w m G₀) X) &&
    Nat.beq (btK n w m nw BP k LR TR TRI X X) C

@[expose] noncomputable def cosetRepC (n w m nw BP k : Nat) (LR TRI : Nat → Nat) (G₀ X : Nat) :
    Bool :=
  canonK n w m nw X && canonK n w m nw (pcomp n w m (pinvS n w m G₀) X) &&
    siftK n w m nw (pidn n w) LR TRI BP k (nat_lit 0) (pcomp n w m (pinvS n w m G₀) X)

theorem cosetRepC_of_K {n w m nw BP k : Nat} {LR TR TRI : Nat → Nat} {G₀ X C : Nat}
    (h : cosetRepK n w m nw BP k LR TR TRI G₀ X C = true) :
    cosetRepC n w m nw BP k LR TRI G₀ X = true ∧ btK n w m nw BP k LR TR TRI X X = C := by
  unfold cosetRepK at h
  unfold cosetRepC
  simp only [Bool.and_eq_true, beq_dec, decide_eq_true_eq] at h ⊢
  exact h

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
  (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem cosetClassEq_soundC (hk64 : k ≤ 64) (hnw : n < 2 ^ w) {G₀ : Nat}
    {g₀ : Equiv.Perm (Fin n)} (pg₀ : PRep n w G₀ g₀)
    (hnorm : ∀ c ∈ (certificate hn gens words bv hbs).originalSubgroup,
      g₀⁻¹ * c * g₀ ∈ (certificate hn gens words bv hbs).originalSubgroup)
    {XL CL : List Nat} (hlen : XL.length = CL.length)
    (hrep : ∀ i < XL.length, cosetRepC n w (mask w) (n * w) BP k LR TRI G₀ (XL.getD i 0) = true)
    (hcard : ∀ i < XL.length, ∀ x, PRep n w (XL.getD i 0) x →
      Nat.card ↥((certificate hn gens words bv hbs).originalSubgroup ⊓
        Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n)))) = CL.getD i 0)
    (hdist : ∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true)
    (hsum : sumAllK (ordK LR k) CL XL.length = ordK LR k) :
    (∀ mo, 0 < mo → (cosetOrderTables (certificate hn gens words bv hbs) g₀ mo).length =
        sumOrdK n w (mask w) (ordK LR k) XL CL mo XL.length) ∧
      ((∀ i < XL.length, CL.getD i 0 < ordK LR k) →
        ∀ h ∈ (certificate hn gens words bv hbs).originalSubgroup,
          ∃ c ∈ (certificate hn gens words bv hbs).originalSubgroup,
            c * (g₀ * h) ≠ g₀ * h * c) := by
  classical
  set Q := certificate hn gens words bv hbs
  set G := Q.originalSubgroup
  set N := ordK LR k
  set len := XL.length
  have hV := chainK_valid hQ hn hbs
  have h32 := chainK_h32 hQ
  have pinv := (prep_pinvS hnw pg₀).1
  have hX : ∀ i < len, canonK n w (mask w) (n * w) (XL.getD i 0) = true ∧
      canonK n w (mask w) (n * w) (pcomp n w (mask w) (pinvS n w (mask w) G₀) (XL.getD i 0)) =
        true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0
        (pcomp n w (mask w) (pinvS n w (mask w) G₀) (XL.getD i 0)) = true := by
    intro i hi
    have h := hrep i hi
    unfold cosetRepC at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hex : ∀ i, ∃ y : Equiv.Perm (Fin n), i < len →
      PRep n w (pcomp n w (mask w) (pinvS n w (mask w) G₀) (XL.getD i 0)) y := by
    intro i
    by_cases hi : i < len
    · obtain ⟨y, py⟩ := prep_of_siftK hQ k 0 (Nat.zero_add k) _
        (fun j hj => (PF.canon_facts (hX i hi).2.1).2.2.2 j hj) (hX i hi).2.2
      exact ⟨y, fun _ => py⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose ys hys using hex
  set xs : Nat → Equiv.Perm (Fin n) := fun i => g₀ * ys i
  have hxs : ∀ i < len, PRep n w (XL.getD i 0) (xs i) := by
    intro i hi x
    have hb : pg w (mask w) (XL.getD i 0) x < n := (PF.canon_facts (hX i hi).1).2.2.2 x x.2
    have e1 := hys i hi x
    rw [PF.pg_pcomp h32 x.2] at e1
    have e2 := pinv ⟨_, hb⟩
    have e3 : g₀⁻¹ ⟨_, hb⟩ = ys i x := Fin.ext (e2.symm.trans e1)
    change _ = ((g₀ * ys i) x : Nat)
    rw [Equiv.Perm.mul_apply, ← e3]
    simp
  have hyG : ∀ i < len, ys i ∈ G := fun i hi =>
    (Q.sift_eq_true_iff_mem_original hV _).1 (chainK_sift hn hbs hQ
      (imageList_of_prep (hys i hi)) (hX i hi).2.1 (hX i hi).2.2)
  set L := (enumeration Q).map (g₀ * ·)
  have hLnd : L.Nodup := (enumeration_nodup Q hV).map (mul_right_injective g₀)
  set Cs := L.toFinset
  have hCs : ∀ x, x ∈ Cs ↔ g₀⁻¹ * x ∈ G := fun x => by
    simp only [Cs, L, List.mem_toFinset, List.mem_map, mem_enumeration_iff Q hV]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro h
      exact ⟨_, h, by group⟩
  have hcardCs : Cs.card = N := by
    rw [List.toFinset_card_of_nodup hLnd, List.length_map, length_enumeration,
      (chainK_check hn hbs hQ).2]
  set C : Nat → Finset (Equiv.Perm (Fin n)) :=
    fun i => Cs.filter fun g => g ∈ CFSG.Sporadic.SmallOddCore.conjClass G (xs i)
  have hclsub : ∀ i < len, ∀ g ∈ CFSG.Sporadic.SmallOddCore.conjClass G (xs i), g ∈ Cs := by
    intro i hi g hg
    obtain ⟨c, hc, rfl⟩ := hg
    rw [hCs]
    have e : g₀⁻¹ * (c * xs i * c⁻¹) = (g₀⁻¹ * c * g₀) * ys i * c⁻¹ := by
      simp only [xs]
      group
    rw [e]
    exact G.mul_mem (G.mul_mem (hnorm c hc) (hyG i hi)) (G.inv_mem hc)
  have hCcard : ∀ i < len, (C i).card = N / CL.getD i 0 := by
    intro i hi
    have h1 := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card G (xs i)
    rw [hcard i hi (xs i) (hxs i hi), CFSG.KS.SporSch.MOC.card_group hQ hn hbs] at h1
    have hpos : 0 < CL.getD i 0 := by
      rcases Nat.eq_zero_or_pos (CL.getD i 0) with h0 | h0
      · rw [h0, Nat.mul_zero] at h1
        exact absurd h1.symm (ordK_pos hQ).ne'
      · exact h0
    have e : (C i).card = (CFSG.Sporadic.SmallOddCore.conjClass G (xs i)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext g
      simp only [C, Finset.coe_filter, Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨hclsub i hi g h, h⟩
    rw [e]
    change _ = ordK LR k / _
    rw [← h1, Nat.mul_div_cancel _ hpos]
  have hdisj : ∀ i < len, ∀ j < i, Disjoint (C j) (C i) := by
    intro i hi j hj
    rw [Finset.disjoint_left]
    intro g hgj hgi
    simp only [C, Finset.mem_filter] at hgj hgi
    have hij : xs i ∈ CFSG.Sporadic.SmallOddCore.conjClass G (xs j) :=
      CFSG.KS.SporSch.ClsSpec.conjClass_trans (CFSG.KS.SporSch.ClsSpec.conjClass_symm hgi.2)
        hgj.2
    obtain ⟨c, hc, hci⟩ := hij
    have hd := hdist i hi j hj
    unfold distK at hd
    rw [Orb.bIf_eq] at hd
    split_ifs at hd with hdf
    · exact not_conj_of_diffK h32 (hxs j (by omega)) (hxs i hi) hdf c hci
    · have h0 := Nat.eq_of_beq_eq_true hd
      rw [btK_eq hQ hn hbs hk64 (hxs j (by omega)) (hxs i hi)] at h0
      have hmem : c ∈ enumeration Q := (mem_enumeration_iff Q hV c).2 hc
      have := List.countP_eq_zero.1 h0 c hmem
      simp only [decide_eq_true_eq] at this
      exact this (by rw [hci]; group)
  have hdisj' : ∀ i ∈ Finset.range len, ∀ j ∈ Finset.range len, i ≠ j → Disjoint (C i) (C j) :=
    fun i hi j hj hij => by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact hdisj j (Finset.mem_range.1 hj) i h
      · exact (hdisj i (Finset.mem_range.1 hi) j h).symm
  have hU : (Finset.range len).biUnion C = Cs := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      obtain ⟨i, -, hgi⟩ := Finset.mem_biUnion.1 hg
      exact (Finset.mem_filter.1 hgi).1
    · rw [hcardCs, Finset.card_biUnion hdisj']
      have hs : sumAllK N CL len = ∑ i ∈ Finset.range len, N / CL.getD i 1 := by
        unfold sumAllK
        rw [foldN_eq]
        exact (foldr_add_range (fun i => N / CL.getD i 1) len 0).trans (Nat.zero_add _)
      have hs' : ∑ i ∈ Finset.range len, (C i).card = sumAllK N CL len := by
        rw [hs]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        rw [hCcard i hi']
        congr 1
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      rw [hs', hsum]
  refine ⟨fun mo hmo => ?_, fun hlt h hh => ?_⟩
  · have hcount : L.countP (fun g => decide (orderOf g = mo)) =
        sumOrdK n w (mask w) N XL CL mo len := by
      rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hLnd.filter _)]
      have e1 : (L.filter fun g => decide (orderOf g = mo)).toFinset =
          Cs.filter fun g => orderOf g = mo := by
        ext g
        simp only [Cs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter]
      rw [e1, ← hU, Finset.filter_biUnion, Finset.card_biUnion (fun i hi j hj hij =>
        Finset.disjoint_filter_filter (hdisj' i hi j hj hij))]
      have hs : sumOrdK n w (mask w) N XL CL mo len = ∑ i ∈ Finset.range len,
          if ordC n w (mask w) (XL.getD i 0) = mo then N / CL.getD i 1 else 0 := by
        unfold sumOrdK
        rw [foldN_eq]
        refine Eq.trans ?_ ((foldr_add_range (fun i => if ordC n w (mask w) (XL.getD i 0) = mo
          then N / CL.getD i 1 else 0) len 0).trans (Nat.zero_add _))
        congr 1
        funext i s
        rw [Orb.nIf_eq, beq_dec]
        by_cases hc : ordC n w (mask w) (XL.getD i 0) = mo
        · simp only [hc, decide_true, ↓reduceIte]
          rfl
        · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [hs]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have hcl : ∀ g ∈ C i, orderOf g = orderOf (xs i) := by
        intro g hg
        simp only [C, Finset.mem_filter] at hg
        obtain ⟨c, _, rfl⟩ := hg.2
        exact (MulAut.conj c).orderOf_eq (xs i)
      rw [← orderOf_of_ordC (hxs i hi')]
      split
      · rename_i ho
        rw [Finset.filter_true_of_mem (fun g hg => (hcl g hg).trans ho), hCcard i hi']
        congr 1
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      · rename_i ho
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro g hg
        rw [hcl g hg]
        exact ho
    rw [(forall₂_cosetOrderTables h32 Q g₀ hmo).length_eq, List.length_reverse,
      ← List.countP_eq_length_filter, ← hcount]
  · by_contra! hc
    have hx : g₀ * h ∈ Cs := (hCs _).2 (by simpa using hh)
    rw [← hU] at hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
    have hi' := Finset.mem_range.1 hi
    obtain ⟨c, hcG, hcx⟩ := (Finset.mem_filter.1 hxi).2
    have hxe : xs i = g₀ * h := by
      have e : xs i = c⁻¹ * (g₀ * h) * c := by rw [hcx]; group
      rw [e, mul_assoc, ← hc c hcG]
      group
    have hle : G ≤ Subgroup.centralizer ({xs i} : Set (Equiv.Perm (Fin n))) := fun g hg => by
      rw [Subgroup.mem_centralizer_singleton_iff, hxe]
      exact hc g hg
    have hcent := hcard i hi' (xs i) (hxs i hi')
    rw [inf_eq_left.2 hle, CFSG.KS.SporSch.MOC.card_group hQ hn hbs] at hcent
    exact (hlt i hi').ne' hcent

theorem cosetClassEq_sound' (hk64 : k ≤ 64) (hnw : n < 2 ^ w) {G₀ : Nat}
    {g₀ : Equiv.Perm (Fin n)} (pg₀ : PRep n w G₀ g₀)
    (hnorm : ∀ c ∈ (certificate hn gens words bv hbs).originalSubgroup,
      g₀⁻¹ * c * g₀ ∈ (certificate hn gens words bv hbs).originalSubgroup)
    {XL CL : List Nat} (hlen : XL.length = CL.length)
    (hrep : ∀ i < XL.length, cosetRepK n w (mask w) (n * w) BP k LR TR TRI G₀ (XL.getD i 0)
      (CL.getD i 0) = true)
    (hdist : ∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true)
    (hsum : sumAllK (ordK LR k) CL XL.length = ordK LR k) :
    (∀ mo, 0 < mo → (cosetOrderTables (certificate hn gens words bv hbs) g₀ mo).length =
        sumOrdK n w (mask w) (ordK LR k) XL CL mo XL.length) ∧
      ((∀ i < XL.length, CL.getD i 0 < ordK LR k) →
        ∀ h ∈ (certificate hn gens words bv hbs).originalSubgroup,
          ∃ c ∈ (certificate hn gens words bv hbs).originalSubgroup,
            c * (g₀ * h) ≠ g₀ * h * c) := by
  refine cosetClassEq_soundC hQ hn hbs hk64 hnw pg₀ hnorm hlen
    (fun i hi => (cosetRepC_of_K (hrep i hi)).1) (fun i hi x px => ?_) hdist hsum
  rw [card_centralizer_eq hQ hn hbs hk64 px]
  exact (cosetRepC_of_K (hrep i hi)).2

end Chain

end CFSG.KS.SporSch.MOC

end
