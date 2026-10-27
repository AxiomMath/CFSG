module

public import CFSG.Certificates.Kernel.SporSch.ChainKClassEq

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MBT
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu

variable {n w : Nat}

theorem card_centralizer_conj {M : Type*} [Group M] (G : Subgroup M) [Finite G] {c : M}
    (hc : c ∈ G) (x : M) :
    Nat.card ↥(G ⊓ Subgroup.centralizer ({c * x * c⁻¹} : Set M)) =
      Nat.card ↥(G ⊓ Subgroup.centralizer ({x} : Set M)) := by
  have e : CFSG.Sporadic.SmallOddCore.conjClass G (c * x * c⁻¹) =
      CFSG.Sporadic.SmallOddCore.conjClass G x := by
    ext y
    simp only [CFSG.Sporadic.SmallOddCore.mem_conjClass]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g * c, G.mul_mem hg hc, by group⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g * c⁻¹, G.mul_mem hg (G.inv_mem hc), by group⟩
  have h1 := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card G (c * x * c⁻¹)
  have h2 := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card G x
  rw [e] at h1
  have hpos : 0 < (CFSG.Sporadic.SmallOddCore.conjClass G x).ncard := by
    rcases Nat.eq_zero_or_pos (CFSG.Sporadic.SmallOddCore.conjClass G x).ncard with h0 | h0
    · rw [h0, Nat.zero_mul] at h2
      exact absurd h2.symm Nat.card_pos.ne'
    · exact h0
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
include hQ

variable (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
include hn hbs

theorem card_of_repK (hk64 : k ≤ 64) {X C : Nat} {x : Equiv.Perm (Fin n)} (pX : PRep n w X x)
    (h : repK n w (mask w) (n * w) BP k LR TR TRI X C = true) :
    Nat.card ↥((certificate hn gens words bv hbs).originalSubgroup ⊓
      Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n)))) = C := by
  unfold repK at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, beq_dec, decide_eq_true_eq] at h
  rw [card_centralizer_eq hQ hn hbs hk64 pX]
  exact h.2.2.2

theorem chainK_cover (hk64 : k ≤ 64) {XL CL : List Nat} (hlen : XL.length = CL.length)
    (hrep : ∀ i < XL.length, repK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0)
      (CL.getD i 0) = true)
    (hdist : ∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true)
    {mo : Nat} (hmo : 1 < mo) (hord : ∀ i < XL.length, ordC n w (mask w) (XL.getD i 0) = mo)
    (hsum : sumAllK (ordK LR k) CL XL.length =
      (cosetOrderTables (certificate hn gens words bv hbs) 1 mo).length) :
    ∀ g ∈ (certificate hn gens words bv hbs).originalSubgroup, orderOf g = mo →
      ∃ i < XL.length, Nat.card ↥((certificate hn gens words bv hbs).originalSubgroup ⊓
        Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n)))) = CL.getD i 0 := by
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
  have hordx : ∀ i < len, orderOf (xs i) = mo := fun i hi =>
    (orderOf_of_ordC (hxs i hi)).trans (hord i hi)
  set Gs := (enumeration Q).toFinset
  have hGs : ∀ g, g ∈ Gs ↔ g ∈ G := fun g => by
    rw [List.mem_toFinset]
    exact mem_enumeration_iff Q hV g
  set S := Gs.filter fun g => orderOf g = mo
  set C : Nat → Finset (Equiv.Perm (Fin n)) :=
    fun i => Gs.filter fun g => g ∈ CFSG.Sporadic.SmallOddCore.conjClass G (xs i)
  have hCsub : ∀ i < len, ∀ g ∈ C i, g ∈ S := by
    intro i hi g hg
    simp only [C, Finset.mem_filter] at hg
    obtain ⟨c, hc, rfl⟩ := hg.2
    exact Finset.mem_filter.2 ⟨hg.1, ((MulAut.conj c).orderOf_eq (xs i)).trans (hordx i hi)⟩
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
  have hS : S.card = (cosetOrderTables Q 1 mo).length := by
    rw [(forall₂_cosetOrderTables h32 Q 1 (by omega)).length_eq, List.length_reverse]
    simp only [one_mul, List.map_id']
    rw [← List.toFinset_card_of_nodup ((enumeration_nodup Q hV).filter _)]
    congr 1
    ext g
    simp only [S, Gs, List.mem_toFinset, List.mem_filter, Finset.mem_filter, decide_eq_true_eq]
  have hU : (Finset.range len).biUnion C = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 hg
      exact hCsub i (Finset.mem_range.1 hi) g hgi
    · rw [hS, ← hsum, Finset.card_biUnion
        (fun i hi j hj hij => by
          rcases Nat.lt_or_gt_of_ne hij with h | h
          · exact hdisj j (Finset.mem_range.1 hj) i h
          · exact (hdisj i (Finset.mem_range.1 hi) j h).symm)]
      have hs : sumAllK N CL len = ∑ i ∈ Finset.range len, N / CL.getD i 1 := by
        unfold sumAllK
        rw [foldN_eq]
        exact (foldr_add_range (fun i => N / CL.getD i 1) len 0).trans (Nat.zero_add _)
      rw [hs]
      refine le_of_eq (Finset.sum_congr rfl fun i hi => ?_)
      have hi' := Finset.mem_range.1 hi
      rw [hCcard i hi']
      congr 1
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  intro g hg ho
  have hgS : g ∈ S := Finset.mem_filter.2 ⟨(hGs g).2 hg, ho⟩
  rw [← hU] at hgS
  obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 hgS
  have hi' := Finset.mem_range.1 hi
  simp only [C, Finset.mem_filter] at hgi
  obtain ⟨c, hc, rfl⟩ := hgi.2
  refine ⟨i, hi', ?_⟩
  rw [card_centralizer_conj G hc, card_centralizer_eq hQ hn hbs hk64 (hxs i hi'),
    (hX i hi').2.2.2]

end Chain

end CFSG.KS.SporSch.MOC

end
