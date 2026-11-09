module

public import CFSG.Certificates.Kernel.SporSch.ChainKClassEq

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MBT
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu

@[expose] noncomputable def conjLowK (n w : Nat) (LR TRI : Nat → Nat) (BP k N X C : Nat)
    (CJ : List (Nat × Nat)) : Bool :=
  canonK n w (mask w) (n * w) X && siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 X &&
    Nat.blt 1 (ordC n w (mask w) X) && Nat.blt 0 C && Nat.beq (N % C) 0 &&
    Nat.beq CJ.length (N / C) && decide (CJ.map Prod.snd).Nodup &&
    CJ.all fun p => canonK n w (mask w) (n * w) p.1 &&
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 p.1 &&
      canonK n w (mask w) (n * w) p.2 &&
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 p.2 &&
      Nat.beq (pcomp n w (mask w) p.1 X) (pcomp n w (mask w) p.2 p.1)

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem prep_perm_eq {P : Nat} {x y : Equiv.Perm (Fin n)} (hx : PRep n w P x)
    (hy : PRep n w P y) : x = y :=
  Equiv.ext fun i => Fin.ext ((hx i).symm.trans (hy i))

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
  (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem memG_of_siftK {P : Nat} (hc : canonK n w (mask w) (n * w) P = true)
    (hs : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 P = true) :
    ∃ x : Equiv.Perm (Fin n), PRep n w P x ∧
      x ∈ (certificate hn gens words bv hbs).originalSubgroup := by
  obtain ⟨x, px⟩ := prep_of_siftK hQ k 0 (Nat.zero_add k) _
    (fun j hj => (PF.canon_facts hc).2.2.2 j hj) hs
  exact ⟨x, px, ((certificate hn gens words bv hbs).sift_eq_true_iff_mem_original
    (chainK_valid hQ hn hbs) _).1 (chainK_sift hn hbs hQ (imageList_of_prep px) hc hs)⟩

theorem repK_of_conjLowK (hk64 : k ≤ 64) {XL CL : List Nat} {CJ : List (List (Nat × Nat))}
    (hlen : XL.length = CL.length)
    (hrep : ∀ i < XL.length, repK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0)
      (CL.getD i 0) = true ∨
        conjLowK n w LR TRI BP k (ordK LR k) (XL.getD i 0) (CL.getD i 0) (CJ.getD i []) = true)
    (hdist : ∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true)
    (hsum : Nat.succ (sumAllK (ordK LR k) CL XL.length) = ordK LR k) :
    ∀ i < XL.length, repK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0)
      (CL.getD i 0) = true := by
  classical
  set Q := certificate hn gens words bv hbs
  set G := Q.originalSubgroup
  set N := ordK LR k
  set len := XL.length
  have hV := chainK_valid hQ hn hbs
  have h32 := chainK_h32 hQ
  have hX : ∀ i < len, canonK n w (mask w) (n * w) (XL.getD i 0) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (XL.getD i 0) = true ∧
      1 < ordC n w (mask w) (XL.getD i 0) := by
    intro i hi
    rcases hrep i hi with h | h
    · unfold repK at h
      simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, beq_dec, decide_eq_true_eq] at h
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    · unfold conjLowK at h
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2⟩
  have hex : ∀ i, ∃ x : Equiv.Perm (Fin n), i < len →
      PRep n w (XL.getD i 0) x ∧ x ∈ G := by
    intro i
    by_cases hi : i < len
    · obtain ⟨x, px, hx⟩ := memG_of_siftK hQ hn hbs (hX i hi).1 (hX i hi).2.1
      exact ⟨x, fun _ => ⟨px, hx⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose xs hxs using hex
  have hord : ∀ i < len, orderOf (xs i) = ordC n w (mask w) (XL.getD i 0) := fun i hi =>
    orderOf_of_ordC (hxs i hi).1
  have hne1 : ∀ i < len, xs i ≠ 1 := fun i hi h1 => by
    have := hord i hi
    rw [h1, orderOf_one] at this
    have := (hX i hi).2.2
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
  have hCn : ∀ i < len, (C i).card = (CFSG.Sporadic.SmallOddCore.conjClass G (xs i)).ncard := by
    intro i hi
    rw [← Set.ncard_coe_finset]
    congr 1
    ext g
    simp only [C, Finset.coe_filter, Set.mem_ofPred_eq, hGs]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨CFSG.KS.SporSch.ClsSpec.conjClass_sub (hxs i hi).2 h, h⟩
  have hmul : ∀ i < len, (C i).card * Nat.card ↥(G ⊓
      Subgroup.centralizer ({xs i} : Set (Equiv.Perm (Fin n)))) = N := by
    intro i hi
    rw [hCn i hi, CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card G (xs i),
      CFSG.KS.SporSch.MOC.card_group hQ hn hbs]
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
    · exact not_conj_of_diffK h32 (hxs j (by omega)).1 (hxs i hi).1 hdf c hci
    · have h0 := Nat.eq_of_beq_eq_true hd
      rw [btK_eq hQ hn hbs hk64 (hxs j (by omega)).1 (hxs i hi).1] at h0
      have hmem : c ∈ enumeration Q := (mem_enumeration_iff Q hV c).2 hc
      have := List.countP_eq_zero.1 h0 c hmem
      simp only [decide_eq_true_eq] at this
      exact this (by rw [hci]; group)
  have hlow : ∀ i < len, N / CL.getD i 0 ≤ (C i).card := by
    intro i hi
    rcases hrep i hi with h | h
    · unfold repK at h
      simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, beq_dec, decide_eq_true_eq] at h
      have h1 := hmul i hi
      rw [card_centralizer_eq hQ hn hbs hk64 (hxs i hi).1, h.2.2.2] at h1
      rcases Nat.eq_zero_or_pos (CL.getD i 0) with h0 | h0
      · rw [h0, Nat.div_zero]
        exact Nat.zero_le _
      · rw [← h1, Nat.mul_div_cancel _ h0]
    · unfold conjLowK at h
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨-, hlenG⟩, hnd⟩, hall⟩ := h
      rw [← Nat.eq_of_beq_eq_true hlenG, ← List.length_map (f := Prod.snd),
        ← List.toFinset_card_of_nodup hnd]
      let f : Nat → Equiv.Perm (Fin n) := fun Y => if h : ∃ y, PRep n w Y y then h.choose else 1
      refine Finset.card_le_card_of_injOn f (fun Y hY => ?_) (fun Y hY Y' hY' e => ?_)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hY)
        have hq := hall p hp
        obtain ⟨⟨⟨⟨hg1, hg2⟩, hy1⟩, hy2⟩, he⟩ := hq
        obtain ⟨g, pg', hgG⟩ := memG_of_siftK hQ hn hbs hg1 hg2
        obtain ⟨y, py, hyG⟩ := memG_of_siftK hQ hn hbs hy1 hy2
        have hex : ∃ y, PRep n w p.2 y := ⟨y, py⟩
        have hfy : f p.2 = y := by
          simp only [f, dif_pos hex]
          exact prep_perm_eq hex.choose_spec py
        rw [Finset.mem_coe, hfy]
        have e1 := prep_pcomp h32 pg' (hxs i hi).1
        have e2 := prep_pcomp h32 py pg'
        rw [Nat.eq_of_beq_eq_true he] at e1
        have hgx := prep_perm_eq e1 e2
        simp only [C, Finset.mem_filter, hGs]
        refine ⟨hyG, g, hgG, ?_⟩
        rw [hgx]
        group
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hY))
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hY'))
        have hq := hall p hp
        have hq' := hall p' hp'
        obtain ⟨y, py, -⟩ := memG_of_siftK hQ hn hbs hq.1.1.2 hq.1.2
        obtain ⟨y', py', -⟩ := memG_of_siftK hQ hn hbs hq'.1.1.2 hq'.1.2
        have hex : ∃ y, PRep n w p.2 y := ⟨y, py⟩
        have hex' : ∃ y, PRep n w p'.2 y := ⟨y', py'⟩
        have hfy : f p.2 = y := by
          simp only [f, dif_pos hex]
          exact prep_perm_eq hex.choose_spec py
        have hfy' : f p'.2 = y' := by
          simp only [f, dif_pos hex']
          exact prep_perm_eq hex'.choose_spec py'
        rw [hfy, hfy'] at e
        rw [e] at py
        obtain ⟨-, hw, hp0, -⟩ := PF.canon_facts hq.1.1.2
        obtain ⟨-, -, hq0, -⟩ := PF.canon_facts hq'.1.1.2
        exact PF.eq_of_fields (PF.w_pos hw) hp0 hq0 fun j hj =>
          (py ⟨j, hj⟩).trans (py' ⟨j, hj⟩).symm
  have hs : sumAllK N CL len = ∑ i ∈ Finset.range len, N / CL.getD i 0 := by
    unfold sumAllK
    rw [foldN_eq]
    refine (foldr_add_range (fun i => N / CL.getD i 1) len 0).trans ?_
    rw [Nat.zero_add]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  have hle : ∑ i ∈ Finset.range len, (C i).card ≤ N - 1 := by
    rw [← Finset.card_biUnion (fun i hi j hj hij => by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact hdisj j (Finset.mem_range.1 hj) i h
      · exact (hdisj i (Finset.mem_range.1 hi) j h).symm)]
    calc _ ≤ (Gs.erase 1).card := Finset.card_le_card fun g hg => by
          obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 hg
          exact hCsub i (Finset.mem_range.1 hi) g hgi
      _ = N - 1 := by rw [Finset.card_erase_of_mem ((hGs 1).2 G.one_mem), hcardG]
  have hall : ∀ i ∈ Finset.range len, N / CL.getD i 0 = (C i).card := by
    refine (Finset.sum_eq_sum_iff_of_le fun i hi => hlow i (Finset.mem_range.1 hi)).1 ?_
    refine le_antisymm (Finset.sum_le_sum fun i hi => hlow i (Finset.mem_range.1 hi)) ?_
    rw [← hs]
    have := hsum
    simp only [Nat.succ_eq_add_one] at this
    omega
  intro i hi
  rcases hrep i hi with h | h
  · exact h
  · have hl := h
    unfold conjLowK at hl
    simp only [Bool.and_eq_true, Nat.blt_eq] at hl
    have hC0 : 0 < CL.getD i 0 := hl.1.1.1.1.2
    have hdvd : CL.getD i 0 ∣ N := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true hl.1.1.1.2)
    have hN : 0 < N := ordK_pos hQ
    have hq : 0 < N / CL.getD i 0 := Nat.div_pos (Nat.le_of_dvd hN hdvd) hC0
    have h1 := hmul i hi
    rw [← hall i (Finset.mem_range.2 hi)] at h1
    have hcent : Nat.card ↥(G ⊓ Subgroup.centralizer ({xs i} : Set (Equiv.Perm (Fin n)))) =
        CL.getD i 0 := by
      refine Nat.eq_of_mul_eq_mul_left hq ?_
      rw [h1, Nat.div_mul_cancel hdvd]
    rw [card_centralizer_eq hQ hn hbs hk64 (hxs i hi).1] at hcent
    unfold repK
    simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, beq_dec, decide_eq_true_eq]
    exact ⟨(hX i hi).1, (hX i hi).2.1, (hX i hi).2.2, hcent⟩

end Chain

end CFSG.KS.SporSch.MOC

end
