module

public import CFSG.Certificates.Kernel.SporSch.ChainKBt
public import CFSG.Certificates.Kernel.SporSch.ChainKClasses
public import CFSG.Certificates.Kernel.SporSch.ChainKReps

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MBT
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu

variable {n w : Nat}

theorem fixN_eq {X : Nat} {x : Equiv.Perm (Fin n)} (pX : PRep n w X x) :
    fixN n w (mask w) X = (Finset.univ.filter fun i : Fin n => x i = i).card := by
  have e : fixN n w (mask w) X = (List.range n).foldr
      (fun i s => if pg w (mask w) X i = i then s + 1 else s) 0 := by
    unfold fixN
    rw [foldN_eq]
    congr 1
    funext i s
    rw [Orb.nIf_eq, beq_dec]
    simp
  rw [e]
  have h2 : ∀ l : List Nat, l.Nodup → (∀ i ∈ l, i < n) →
      l.foldr (fun i s => if pg w (mask w) X i = i then s + 1 else s) 0 =
        (l.filter fun i => decide (pg w (mask w) X i = i)).length := by
    intro l _ _
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.foldr_cons, List.filter_cons]
      split <;> simp_all
  rw [h2 _ List.nodup_range (fun i hi => List.mem_range.1 hi)]
  rw [← List.countP_eq_length_filter, ← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq,
    Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨⟨i, hi⟩, ?_, rfl⟩
    apply Fin.ext
    rw [← pX ⟨i, hi⟩]
    exact h
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.2, ?_⟩
    rw [pX j, hj]

theorem card_fix_conj (g x : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun i : Fin n => (g * x * g⁻¹) i = i).card =
      (Finset.univ.filter fun i : Fin n => x i = i).card := by
  refine Finset.card_bij (fun i _ => g⁻¹ i) (fun i hi => ?_) (fun a _ b _ h => g⁻¹.injective h)
    (fun j hj => ⟨g j, ?_, by simp⟩)
  · rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, g.injective ?_⟩
    have := hi.2
    simp only [Equiv.Perm.mul_apply] at this
    simpa using this
  · rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [hj.2]

theorem not_conj_of_diffK {X Y : Nat} {x y : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (pX : PRep n w X x) (pY : PRep n w Y y) (h : diffK n w (mask w) X Y = true)
    (g : Equiv.Perm (Fin n)) : y ≠ g * x * g⁻¹ := by
  intro hy
  have p2X := prep_pcomp hn pX pX
  have p2Y := prep_pcomp hn pY pY
  unfold diffK at h
  simp only [Orb.bIf_eq, beq_dec, decide_eq_true_eq] at h
  rw [← orderOf_of_ordC pX, ← orderOf_of_ordC pY, fixN_eq pX, fixN_eq pY, fixN_eq p2X,
    fixN_eq p2Y] at h
  have ho : orderOf y = orderOf x := by rw [hy]; exact (MulAut.conj g).orderOf_eq x
  have hf : (Finset.univ.filter fun i : Fin n => y i = i).card =
      (Finset.univ.filter fun i : Fin n => x i = i).card := by
    rw [hy]
    exact card_fix_conj g x
  have hf2 : (Finset.univ.filter fun i : Fin n => (y * y) i = i).card =
      (Finset.univ.filter fun i : Fin n => (x * x) i = i).card := by
    have : y * y = g * (x * x) * g⁻¹ := by rw [hy]; group
    rw [this]
    exact card_fix_conj g (x * x)
  simp only [Equiv.Perm.mul_apply] at hf2
  simp [ho, hf, hf2] at h

theorem foldr_add_range (f : Nat → Nat) : ∀ len init : Nat,
    (List.range len).foldr (fun i s => s + f i) init = init + ∑ i ∈ Finset.range len, f i
  | 0, init => by simp
  | len + 1, init => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_add_range f len,
      Finset.sum_range_succ]
    ring

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
include hQ

theorem prep_of_siftK : ∀ d l, l + d = k → ∀ G, (∀ i < n, pg w (mask w) G i < n) →
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true →
      ∃ g : Equiv.Perm (Fin n), PRep n w G g
  | 0, _, _, G, _, h => by
    rw [siftK_zero, bAnd_eq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.2]
    exact ⟨1, prep_pidn (chainK_n24 hQ) hQ.2.1⟩
  | d + 1, l, hl, G, hG, h => by
    have h32 := chainK_h32 hQ
    have hlk : l < k := by omega
    rw [siftK_succ] at h
    simp only [Orb.strictB_eq, Orb.bIf_eq, Nat.blt_eq] at h
    split_ifs at h with ht
    · set t := rpos w (mask w) (n * w) (LR l) (pg w (mask w) G (pg w (mask w) BP l))
      have pT := ((chainK_agree hQ hlk).2 t ht).2
      have hG' : ∀ i < n, pg w (mask w) (pcomp n w (mask w) (TRI (roff n (n * w) (LR l) + t)) G)
          i < n := fun i hi => by
        rw [PF.pg_pcomp h32 hi, pT ⟨_, hG i hi⟩]
        exact Fin.isLt _
      obtain ⟨g', pg'⟩ := prep_of_siftK d (l + 1) (by omega) _ hG' h
      refine ⟨trP n w LR TR l t * g', fun x => ?_⟩
      have e := pg' x
      rw [PF.pg_pcomp h32 x.2, pT ⟨_, hG x x.2⟩] at e
      rw [Equiv.Perm.mul_apply, ← Fin.ext_iff.mpr e]
      simp

variable (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
include hn hbs

theorem card_centralizer_eq (hk64 : k ≤ 64) {X : Nat} {x : Equiv.Perm (Fin n)}
    (pX : PRep n w X x) :
    Nat.card ↥((certificate hn gens words bv hbs).originalSubgroup ⊓
      Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n)))) =
        btK n w (mask w) (n * w) BP k LR TR TRI X X := by
  set Q := certificate hn gens words bv hbs
  have hV := chainK_valid hQ hn hbs
  rw [btK_eq hQ hn hbs hk64 pX pX, ← card_subtype_eq_countP Q.originalSubgroup _
    (enumeration_nodup Q hV) (mem_enumeration_iff Q hV) (fun g => g * x = x * g)]
  refine Nat.card_congr ⟨fun g => ⟨⟨g, g.2.1⟩, Subgroup.mem_centralizer_singleton_iff.1 g.2.2⟩,
    fun g => ⟨g.1, g.1.2, Subgroup.mem_centralizer_singleton_iff.2 g.2⟩, fun _ => rfl,
    fun _ => rfl⟩

theorem classEq_sound' (hk64 : k ≤ 64) {XL CL : List Nat} (hlen : XL.length = CL.length)
    (hrep : ∀ i < XL.length, repK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0)
      (CL.getD i 0) = true)
    (hdist : ∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true)
    (hsum : Nat.succ (sumAllK (ordK LR k) CL XL.length) = ordK LR k) {mo : Nat} (hmo : 1 < mo) :
    (orderTables (certificate hn gens words bv hbs) mo).length =
        sumOrdK n w (mask w) (ordK LR k) XL CL mo XL.length ∧
      (cosetOrderTables (certificate hn gens words bv hbs) 1 mo).length =
        sumOrdK n w (mask w) (ordK LR k) XL CL mo XL.length := by
  classical
  set Q := certificate hn gens words bv hbs
  set G := Q.originalSubgroup
  set N := ordK LR k
  set len := XL.length
  have hV := chainK_valid hQ hn hbs
  have h32 := chainK_h32 hQ
  have hX : ∀ i < len, canonK n w (mask w) (n * w) (XL.getD i 0) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (XL.getD i 0) = true ∧
      1 < ordC n w (mask w) (XL.getD i 0) ∧
      btK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0) (XL.getD i 0) = CL.getD i 0 := by
    intro i hi
    have h := hrep i hi
    unfold repK at h
    simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, beq_dec, decide_eq_true_eq] at h
    exact h
  have hex : ∀ i, ∃ x : Equiv.Perm (Fin n), i < len → PRep n w (XL.getD i 0) x := by
    intro i
    by_cases hi : i < len
    · obtain ⟨x, px⟩ := prep_of_siftK hQ k 0 (Nat.zero_add k) _
        (fun j hj => (PF.canon_facts (hX i hi).1).2.2.2 j hj) (hX i hi).2.1
      exact ⟨x, fun _ => px⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose xs hxs using hex
  have hxG : ∀ i < len, xs i ∈ G := fun i hi =>
    (Q.sift_eq_true_iff_mem_original hV _).1 (chainK_sift hn hbs hQ
      (imageList_of_prep (hxs i hi)) (hX i hi).1 (hX i hi).2.1)
  have hord : ∀ i < len, orderOf (xs i) = ordC n w (mask w) (XL.getD i 0) := fun i hi =>
    orderOf_of_ordC (hxs i hi)
  have hne1 : ∀ i < len, xs i ≠ 1 := fun i hi h1 => by
    have := hord i hi
    rw [h1, orderOf_one] at this
    have := (hX i hi).2.2.1
    omega
  set Gs := (enumeration Q).toFinset
  have hGs : ∀ g, g ∈ Gs ↔ g ∈ G := fun g => by
    rw [List.mem_toFinset]
    exact mem_enumeration_iff Q hV g
  have hcardG : Gs.card = N := by
    rw [List.toFinset_card_of_nodup (enumeration_nodup Q hV), length_enumeration,
      (chainK_check hn hbs hQ).2]
  set C : Nat → Finset (Equiv.Perm (Fin n)) :=
    fun i => Gs.filter fun g => g ∈ CFSG.Sporadic.SmallOddCore.conjClass G (xs i)
  have hCsub : ∀ i < len, ∀ g ∈ C i, g ∈ Gs.erase 1 := by
    intro i hi g hg
    simp only [C, Finset.mem_filter] at hg
    obtain ⟨c, hc, rfl⟩ := hg.2
    refine Finset.mem_erase.2 ⟨fun h => hne1 i hi ?_, hg.1⟩
    have : xs i = c⁻¹ * (c * xs i * c⁻¹) * c := by group
    rw [this, h]
    group
  have hCcard : ∀ i < len, (C i).card = N / CL.getD i 0 := by
    intro i hi
    have h1 := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card G (xs i)
    rw [card_centralizer_eq hQ hn hbs hk64 (hxs i hi), (hX i hi).2.2.2,
      CFSG.KS.SporSch.MOC.card_group hQ hn hbs] at h1
    have hpos : 0 < CL.getD i 0 := by
      rcases Nat.eq_zero_or_pos (CL.getD i 0) with h0 | h0
      · rw [h0, Nat.mul_zero] at h1
        exact absurd h1.symm (ordK_pos hQ).ne'
      · exact h0
    have e : (C i).card = (CFSG.Sporadic.SmallOddCore.conjClass G (xs i)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext g
      simp only [C, Finset.coe_filter, Set.mem_ofPred_eq, hGs]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨CFSG.KS.SporSch.ClsSpec.conjClass_sub (hxG i hi) h, h⟩
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
  have hU : (Finset.range len).biUnion C = Gs.erase 1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 hg
      exact hCsub i (Finset.mem_range.1 hi) g hgi
    · rw [Finset.card_erase_of_mem ((hGs 1).2 G.one_mem), hcardG, Finset.card_biUnion
        (fun i hi j hj hij => by
          rcases Nat.lt_or_gt_of_ne hij with h | h
          · exact hdisj j (Finset.mem_range.1 hj) i h
          · exact (hdisj i (Finset.mem_range.1 hi) j h).symm)]
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
      rw [hs']
      have := hsum
      simp only [Nat.succ_eq_add_one] at this
      omega
  have hcount : (enumeration Q).countP (fun g => decide (orderOf g = mo)) =
      sumOrdK n w (mask w) N XL CL mo len := by
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
      ((enumeration_nodup Q hV).filter _)]
    have e1 : ((enumeration Q).filter fun g => decide (orderOf g = mo)).toFinset =
        (Gs.erase 1).filter fun g => orderOf g = mo := by
      ext g
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter,
        Finset.mem_erase, Gs]
      constructor
      · rintro ⟨hg, ho⟩
        refine ⟨⟨fun h1 => ?_, hg⟩, ho⟩
        rw [h1, orderOf_one] at ho
        omega
      · rintro ⟨⟨-, hg⟩, ho⟩
        exact ⟨hg, ho⟩
    rw [e1, ← hU, Finset.filter_biUnion, Finset.card_biUnion (fun i hi j hj hij => by
      refine Finset.disjoint_filter_filter ?_
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact hdisj j (Finset.mem_range.1 hj) i h
      · exact (hdisj i (Finset.mem_range.1 hi) j h).symm)]
    have hs : sumOrdK n w (mask w) N XL CL mo len = ∑ i ∈ Finset.range len,
        if ordC n w (mask w) (XL.getD i 0) = mo then N / CL.getD i 1 else 0 := by
      unfold sumOrdK
      rw [foldN_eq]
      refine Eq.trans ?_ ((foldr_add_range (fun i => if ordC n w (mask w) (XL.getD i 0) = mo then
        N / CL.getD i 1 else 0) len 0).trans (Nat.zero_add _))
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
    rw [← hord i hi']
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
  have hmo : 0 < mo := by omega
  refine ⟨?_, ?_⟩
  · rw [(forall₂_orderTables h32 Q hmo).length_eq, List.length_reverse,
      ← List.countP_eq_length_filter, ← hcount]
  · rw [(forall₂_cosetOrderTables h32 Q 1 hmo).length_eq, List.length_reverse,
      ← List.countP_eq_length_filter, ← hcount]
    simp only [one_mul, List.map_id']

end Chain

end CFSG.KS.SporSch.MOC

end
