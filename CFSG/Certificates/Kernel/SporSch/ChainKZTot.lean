module

public import CFSG.Certificates.Kernel.SporSch.ChainKClassEq
public import CFSG.Certificates.Kernel.SporSch.MathieuClsSound
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd

public section

namespace CFSG.KS.SporSch.ClsSpec

open CFSG.Sporadic CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native

variable {n : ℕ} {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
  (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹)
  {X : List Table} {xs : List (Equiv.Perm (Fin n))} (hX : List.Forall₂ (Rep n) X xs)
  {cap : ℕ} (hcap : ∀ y ∈ xs, (SmallOddCore.conjClass (genK gens gg) y).ncard ≤ cap)
include hg hX hcap

theorem classOK_of_closed (hnd : xs.Nodup)
    (hcl : ∀ y ∈ xs, ∀ z ∈ SmallOddCore.conjClass (genK gens gg) y, z ∈ xs) :
    classOK n gens gensInv X cap = true := by
  classical
  set K := genK gens gg
  have hl := hX.length_eq
  have hR := findReps_spec hg hX hcap
  have hRlt : ∀ p ∈ findReps n gens gensInv X cap, p < X.length := fun p hp => by
    rw [hR] at hp
    exact List.mem_range.1 (List.mem_filter.1 hp).1
  have hRfirst : ∀ p ∈ findReps n gens gensInv X cap, First K xs p := fun p hp => by
    rw [hR] at hp
    simpa using (List.mem_filter.1 hp).2
  have hsp := fun p (hp : p < X.length) => conjClosure_spec hg (rep_get hX hp) (cap_get hcap
    (by omega))
  set E : ℕ → List Table := fun p => (conjClosure n gens gensInv X.toArray[p]! cap).1.toList
  set L := (findReps n gens gensInv X cap).flatMap fun p => (E p).map (key n)
  have hLnd : L.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun p hp => (hsp p (hRlt p hp)).2.1, ?_⟩
    have hpw : (findReps n gens gensInv X cap).Pairwise (· < ·) := by
      rw [hR]
      exact List.pairwise_lt_range.filter _
    refine hpw.imp_of_mem fun {a b} ha hb hab => ?_
    rw [Function.onFun, List.disjoint_left]
    intro kk h1 h2
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h1
    obtain ⟨t', ht', e⟩ := List.mem_map.1 h2
    obtain ⟨z, hz, htz⟩ := (hsp a (hRlt a ha)).2.2.1 t ht
    obtain ⟨z', hz', htz'⟩ := (hsp b (hRlt b hb)).2.2.1 t' ht'
    have := eq_of_key htz' htz e
    subst this
    exact hRfirst b hb a hab (conjClass_trans (conjClass_symm hz) hz')
  have hLmem : ∀ kk, kk ∈ L ↔ kk ∈ xs.map (keyOf n) := by
    intro kk
    simp only [L, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨p, hp, t, ht, rfl⟩
      obtain ⟨z, hz, htz⟩ := (hsp p (hRlt p hp)).2.2.1 t ht
      have hxp : xs.getD p 1 ∈ xs := by
        rw [List.getD_eq_getElem _ _ (by have := hRlt p hp; omega)]
        exact List.getElem_mem _
      exact ⟨z, hcl _ hxp z hz, (key_eq_keyOf htz).symm⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hz
      have hex : ∃ p, p < X.length ∧ xs.getD p 1 ∈ SmallOddCore.conjClass K xs[q] :=
        ⟨q, by omega, by
          rw [List.getD_eq_getElem _ _ hq]
          exact SmallOddCore.self_mem_conjClass _ _⟩
      set p := Nat.find hex
      obtain ⟨hp, hpc⟩ := Nat.find_spec hex
      have hfirst : First K xs p := fun p' hp' hm =>
        Nat.find_min hex hp' ⟨by omega, conjClass_trans hm hpc⟩
      have hpR : p ∈ findReps n gens gensInv X cap := by
        rw [hR]
        exact List.mem_filter.2 ⟨List.mem_range.2 hp, by simpa using hfirst⟩
      obtain ⟨t, ht, htz⟩ := (hsp p hp).2.2.2 _ (conjClass_symm hpc)
      exact ⟨p, hpR, t, ht, key_eq_keyOf htz⟩
  have hxnd : (xs.map (keyOf n)).Nodup := hnd.map fun a b h => keyOf_inj h
  have hLlen : L.length = X.length := by
    rw [((List.perm_ext_iff_of_nodup hLnd hxnd).2 hLmem).length_eq, List.length_map, hl]
  unfold classOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hRlt, ?_⟩, ?_⟩, ?_⟩
  · intro c hc
    rw [classes] at hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    exact (hsp p (hRlt p hp)).1
  · apply keysDistinct_of
    rw [classes, List.flatMap_map, List.map_flatMap]
    exact hLnd
  · rw [← hLlen, classes, List.map_map]
    simp only [L, List.length_flatMap, List.length_map, Function.comp_def]
    rfl

end CFSG.KS.SporSch.ClsSpec

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum
open CFSG.KS.SporSch.MBT CFSG.Certificates CFSG.Sporadic CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Monster.B.Mathieu CFSG.KS.SporSch.ClsSpec

variable {n w : Nat}

theorem sum_range_list (f : Nat → Nat) (L : Nat) :
    ((List.range L).map f).sum = ∑ i ∈ Finset.range L, f i := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.sum_coe]

theorem list_sum_eq (l : List Nat) : l.sum = ∑ b ∈ Finset.range l.length, l.getD b 0 := by
  rw [← sum_range_list, sum_range_getD rfl (fun _ _ => rfl)]

theorem countP_card {M : Type*} [DecidableEq M] {l : List M} (hl : l.Nodup) (p : M → Bool) :
    l.countP p = (l.toFinset.filter fun x => p x = true).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _),
    List.toFinset_filter]

theorem wordElts_map {M M' : Type*} [Group M] [Group M'] (f : M →* M') (x y : M) (mx my : Nat) :
    ∀ wd : List Nat, wordElts (f x) (f y) mx my wd = (wordElts x y mx my wd).map f
  | [] => rfl
  | l :: wd => by
    have ih := wordElts_map f x y mx my wd
    simp only [wordElts] at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
    congr 1
    split_ifs <;> simp [List.map_replicate]

theorem wsVal_conj (mx my : Nat) (ws : List (List Nat × Nat)) (c x y : Equiv.Perm (Fin n)) :
    wsVal mx my ws (c * x * c⁻¹) (c * y * c⁻¹) = wsVal mx my ws x y := by
  unfold wsVal
  congr 1
  funext p
  congr 2
  have h := wordElts_map (MulAut.conj c).toMonoidHom x y mx my p.1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [h, ← map_list_prod, MulEquiv.orderOf_eq]

theorem orderOf_of_wsVal {mx my r : Nat} {ws : List (List Nat × Nat)} (hws : ([0, 1], r) ∈ ws)
    (hr : r ≠ 0) {x y : Equiv.Perm (Fin n)} (h : wsVal mx my ws x y = true) :
    orderOf (x * y) = r := by
  unfold wsVal at h
  rw [List.all_eq_true] at h
  have := h _ hws
  simp only [wordElts, List.flatMap_cons, List.flatMap_nil, List.prod_append,
    List.prod_nil] at this
  simpa [hr] using this

theorem cntZK_eq (n w m idn mx my : Nat) (ws : List (List Nat × Nat)) (Z : Nat) (d : ClsD)
    (lo : Nat) : ∀ len, cntZK n w m idn mx my ws Z d lo len =
      ∑ l ∈ Finset.range len,
        if lo + l < d.c ∧ zTest n w m idn mx my ws Z (d.ST (lo + l)) = true then 1 else 0
  | 0 => by
    unfold cntZK
    rw [foldUp_eq]
    rfl
  | len + 1 => by
    have ih := cntZK_eq n w m idn mx my ws Z d lo len
    unfold cntZK at ih ⊢
    rw [foldUp_eq] at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Finset.sum_range_succ, strictN_eq]
    by_cases h1 : lo + len < d.c <;>
      by_cases h2 : zTest n w m idn mx my ws Z (d.ST (lo + len)) = true <;>
      simp [nIf_eq, Nat.blt_eq, Nat.add_eq, h1, h2]

theorem sum_blocks (p : Nat → Bool) (c : Nat) (L : List Nat) (hc : c ≤ L.length * 256)
    (hL : ∀ b < L.length, L.getD b 0 = ∑ l ∈ Finset.range 256,
      if b * 256 + l < c ∧ p (b * 256 + l) = true then 1 else 0) :
    L.sum = ∑ k ∈ Finset.range c, if p k = true then 1 else 0 := by
  have hall : ∀ nb, ∑ b ∈ Finset.range nb, (∑ l ∈ Finset.range 256,
      if b * 256 + l < c ∧ p (b * 256 + l) = true then 1 else 0) =
      ∑ k ∈ Finset.range (nb * 256), if k < c ∧ p k = true then 1 else 0 := by
    intro nb
    induction nb with
    | zero => simp
    | succ nb ih => rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
  rw [list_sum_eq, Finset.sum_congr rfl fun b hb => hL b (Finset.mem_range.1 hb), hall,
    ← Nat.add_sub_cancel' hc, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range (L.length * 256 - c),
      (if c + x < c ∧ p (c + x) = true then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => by
      have hx : ¬ (c + x < c ∧ p (c + x) = true) := fun h => absurd h.1 (by omega)
      simp only [hx, ↓reduceIte]
  rw [h0, Nat.add_zero]
  exact Finset.sum_congr rfl fun k hk => by
    have := Finset.mem_range.1 hk
    simp [this]

theorem orderOf_conjP (c a : Equiv.Perm (Fin n)) : orderOf (c * a * c⁻¹) = orderOf a :=
  (MulAut.conj c).orderOf_eq a

theorem card_filter_conj {s : Finset (Equiv.Perm (Fin n))} (c : Equiv.Perm (Fin n))
    (hs : ∀ a ∈ s, c * a * c⁻¹ ∈ s ∧ c⁻¹ * a * c ∈ s) {p q : Equiv.Perm (Fin n) → Prop}
    [DecidablePred p] [DecidablePred q] (hpq : ∀ a, q (c * a * c⁻¹) ↔ p a) :
    (s.filter p).card = (s.filter q).card := by
  refine Finset.card_nbij' (fun a => c * a * c⁻¹) (fun a => c⁻¹ * a * c) (fun a ha => ?_)
    (fun a ha => ?_) (fun a _ => by group) (fun a _ => by group)
  · simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨(hs a ha.1).1, (hpq a).2 ha.2⟩
  · simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    refine ⟨(hs a ha.1).2, (hpq _).1 ?_⟩
    have e : c * (c⁻¹ * a * c) * c⁻¹ = a := by group
    rw [e]
    exact ha.2

theorem entry_inj {A Ai B Bi : Nat} {d : ClsD} (hw : 0 < w)
    (he : ∀ k < d.c, clsElemK n w (mask w) (n * w) A Ai B Bi d k = true) {i j : Nat}
    (hi : i < d.c) (hj : j < d.c) {z : Equiv.Perm (Fin n)} (p1 : PRep n w (d.ST i) z)
    (p2 : PRep n w (d.ST j) z) : i = j := by
  have s1 := (clsElemK_facts hi (he i hi)).2.1
  have s2 := (clsElemK_facts hj (he j hj)).2.1
  have eq : d.ST i = d.ST j := PF.eq_of_fields hw s1 s2 fun t ht => by
    rw [p1 ⟨t, ht⟩, p2 ⟨t, ht⟩]
  have hinc := lt_of_consec (c := d.c) (ST := d.ST) fun k hk =>
    (clsElemK_facts (by omega) (he k (by omega))).1 hk
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd eq (Nat.ne_of_lt (hinc i j h hj))
  · exact h
  · exact absurd eq (Nat.ne_of_gt (hinc j i h hi))

theorem fpow_iterZ (f : Nat → Nat) : ∀ e q, fpow f e q = f^[e] q
  | 0, _ => rfl
  | e + 1, q => by
    change strictN (f q) (fpow f e) = _
    rw [strictN_eq, fpow_iterZ f e, Function.iterate_succ_apply]

theorem iter_permZ {f : Nat → Nat} {σ : Equiv.Perm (Fin n)} (hf : ∀ v : Fin n, f v = σ v) :
    ∀ (k : Nat) (v : Fin n), f^[k] v = ((σ ^ k) v : Nat)
  | 0, v => by simp
  | k + 1, v => by
    rw [Function.iterate_succ_apply, pow_succ, Equiv.Perm.mul_apply, hf v]
    exact iter_permZ hf k (σ v)

theorem yPtK_eq {X Z : Nat} {x z : Equiv.Perm (Fin n)} (pX : PRep n w X x) (pZ : PRep n w Z z)
    (e : Nat) (v : Fin n) : yPtK w (mask w) X e Z v = ((x ^ e * z) v : Nat) := by
  unfold yPtK
  rw [pZ v, fpow_iterZ, iter_permZ pX e (z v), Equiv.Perm.mul_apply]

theorem zFixK_of {X Z : Nat} {x z : Equiv.Perm (Fin n)} (pX : PRep n w X x) (pZ : PRep n w Z z)
    {e my : Nat} (h : (x ^ e * z) ^ my = 1) : zFixK n w (mask w) e my Z X = true := by
  have key : ∀ i (hi : i < n), fpow (yPtK w (mask w) X e Z) my i = i := fun i hi => by
    have := iter_permZ (yPtK_eq pX pZ e) my ⟨i, hi⟩
    rw [h] at this
    rw [fpow_iterZ]
    simpa using this
  unfold zFixK
  rw [Orb.bIf_eq]
  split
  · rename_i hb
    have h1 : 1 < n := by simpa using hb
    have k0 := key (nat_lit 0) (Nat.lt_trans Nat.zero_lt_one h1)
    have k1 := key (nat_lit 1) h1
    rw [bAnd_eq, k0, k1, Nat.beq_refl, Nat.beq_refl]
    rfl
  · rfl

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Sum

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem classSum' (hk64 : k ≤ 64) {XL CL : List Nat} (hlen : XL.length = CL.length)
    (hrep : ∀ i < XL.length, repK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0)
      (CL.getD i 0) = true)
    (hdist : ∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true)
    (hsum : Nat.succ (sumAllK (ordK LR k) CL XL.length) = ordK LR k)
    (f : Equiv.Perm (Fin n) → Nat)
    (hf : ∀ c ∈ (certificate hn gens words bv hbs).originalSubgroup, ∀ x,
      f (c * x * c⁻¹) = f x)
    (F : Nat → Nat) (hF : ∀ i < XL.length, ∀ x, PRep n w (XL.getD i 0) x → F i = f x) :
    ∑ g ∈ (enumeration (certificate hn gens words bv hbs)).toFinset.erase 1, f g =
      ∑ i ∈ Finset.range XL.length, ordK LR k / CL.getD i 1 * F i := by
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
  have hpd : ∀ i ∈ Finset.range len, ∀ j ∈ Finset.range len, i ≠ j → Disjoint (C i) (C j) :=
    fun i hi j hj hij => by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact hdisj j (Finset.mem_range.1 hj) i h
      · exact (hdisj i (Finset.mem_range.1 hi) j h).symm
  have hU : (Finset.range len).biUnion C = Gs.erase 1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 hg
      exact hCsub i (Finset.mem_range.1 hi) g hgi
    · rw [Finset.card_erase_of_mem ((hGs 1).2 G.one_mem), hcardG, Finset.card_biUnion hpd]
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
  rw [← hU, Finset.sum_biUnion hpd]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hconst : ∀ g ∈ C i, f g = f (xs i) := by
    intro g hg
    simp only [C, Finset.mem_filter] at hg
    obtain ⟨c, hc, rfl⟩ := hg.2
    exact hf c hc _
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, hCcard i hi',
    hF i hi' _ (hxs i hi')]
  congr 2
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

end Sum

theorem orig_pair (hn : 1 ≤ n) {gA gB : Equiv.Perm (Fin n)} (hbs : bv.toList.Nodup) :
    (certificate hn [gA, gB] words bv hbs).originalSubgroup =
      Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) := by
  simp only [RawSchreierDatum.originalSubgroup, certificate]
  congr 1
  ext g
  simp

section Pair

variable {gA gB : Equiv.Perm (Fin n)}
  (hQ : ChainK n w [gA, gB] words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem rep_of_sift {R : Nat}
    (h : bAnd(canonK n w (mask w) (n * w) R,
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 R) = true) :
    ∃ r : Equiv.Perm (Fin n), PRep n w R r ∧
      r ∈ (certificate hn [gA, gB] words bv hbs).originalSubgroup := by
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨r, pr⟩ := prep_of_siftK hQ k 0 (Nat.zero_add k) _
    (fun j hj => (PF.canon_facts h.1).2.2.2 j hj) h.2
  exact ⟨r, pr, ((certificate hn [gA, gB] words bv hbs).sift_eq_true_iff_mem_original
    (chainK_valid hQ hn hbs) _).1 (chainK_sift hn hbs hQ (imageList_of_prep pr) h.1 h.2)⟩

omit hn hbs in
theorem gens_prep {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB) :
    PRep n w (packL w tA) gA ∧ PRep n w (pinvS n w (mask w) (packL w tA)) gA⁻¹ ∧
      PRep n w (packL w tB) gB ∧ PRep n w (pinvS n w (mask w) (packL w tB)) gB⁻¹ ∧
      n < 2 ^ 32 ∧ 0 < w := by
  subst hA hB
  have hsz := chainK_szOK hQ
  have hf := CFSG.KS.Raw.Orb.szOK_facts hsz
  have hwn : n < 2 ^ w := by omega
  have pA := (prep_packL (g := gA) hf.2).1
  have pB := (prep_packL (g := gB) hf.2).1
  exact ⟨pA, (prep_pinvS hwn pA).1, pB, (prep_pinvS hwn pB).1, szOK_lt hsz, PF.w_pos hf.2⟩

omit hn hbs in
theorem datum_class {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB)
    {mx cap : Nat} {CS : List ClsD} (hcls : ClsOK n w tA tB mx cap CS) {j : Nat}
    (hj : j < CS.length) {r : Equiv.Perm (Fin n)} (pr : PRep n w (CS.getD j clsD0).R r) :
    (∀ z, z ∈ SmallOddCore.conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r ↔
      ∃ k' < (CS.getD j clsD0).c, PRep n w ((CS.getD j clsD0).ST k') z) ∧
      (SmallOddCore.conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r).ncard =
        (CS.getD j clsD0).c ∧ (CS.getD j clsD0).c ≤ cap ∧ orderOf r = mx := by
  obtain ⟨pA, pAi, pB, pBi, h32, hw⟩ := gens_prep hQ hA hB
  obtain ⟨hd, he, -⟩ := hcls j hj
  have hf := clsHdK_facts hd
  exact ⟨mem_class_iff h32 pA pAi pB pBi hd he pr, ncard_class h32 pA pAi pB pBi hd he pr hw,
    hf.2.1, (orderOf_of_ordC pr).trans hf.2.2.2.2⟩

omit hn hbs in
theorem datum_disj {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB)
    {mx cap : Nat} {CS : List ClsD} (hcls : ClsOK n w tA tB mx cap CS) {i j : Nat}
    (hij : i < j) (hj : j < CS.length) {ri rj : Equiv.Perm (Fin n)}
    (pi : PRep n w (CS.getD i clsD0).R ri) (pj : PRep n w (CS.getD j clsD0).R rj) :
    rj ∉ SmallOddCore.conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) ri := by
  intro hrj
  obtain ⟨pA, pAi, pB, pBi, h32, hw⟩ := gens_prep hQ hA hB
  obtain ⟨hdi, hei, -⟩ := hcls i (by omega)
  obtain ⟨hdj, hej, hnot⟩ := hcls j hj
  obtain ⟨k', hk, pk⟩ := (mem_class_iff h32 pA pAi pB pBi hdi hei pi _).1 hrj
  have hfj := clsHdK_facts hdj
  have sR : (CS.getD j clsD0).R >>> (n * w) = 0 := by
    rw [← hfj.2.2.2.1]
    exact (clsElemK_facts hfj.2.2.1 (hej _ hfj.2.2.1)).2.1
  have sk := (clsElemK_facts hk (hei k' hk)).2.1
  have eq : (CS.getD i clsD0).ST k' = (CS.getD j clsD0).R :=
    PF.eq_of_fields hw sk sR fun t ht => by rw [pk ⟨t, ht⟩, pj ⟨t, ht⟩]
  exact notInK_spec (hnot i hij) k' hk eq

theorem classOK_sound' {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB)
    {mx cap : Nat} {CS : List ClsD} (hcls : ClsOK n w tA tB mx cap CS)
    (hRs : ∀ j < CS.length, bAnd(canonK n w (mask w) (n * w) (CS.getD j clsD0).R,
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (CS.getD j clsD0).R) = true)
    (hmx : 0 < mx)
    (hX : (orderTables (certificate hn [gA, gB] words bv hbs) mx).length = (CS.map ClsD.c).sum) :
    classOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹)
      (orderTables (certificate hn [gA, gB] words bv hbs) mx) cap = true := by
  classical
  set Q := certificate hn [gA, gB] words bv hbs
  set G := Q.originalSubgroup
  set K := Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))
  set L := CS.length
  have hV := chainK_valid hQ hn hbs
  have h32 := chainK_h32 hQ
  have hGK : G = K := orig_pair hn hbs
  have hex : ∀ j, ∃ r : Equiv.Perm (Fin n), j < L → PRep n w (CS.getD j clsD0).R r ∧ r ∈ G := by
    intro j
    by_cases hj : j < L
    · obtain ⟨r, pr, hr⟩ := rep_of_sift hQ hn hbs (hRs j hj)
      exact ⟨r, fun _ => ⟨pr, hr⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose rs hrs using hex
  have hcf := fun j (hj : j < L) => datum_class hQ hA hB hcls hj (hrs j hj).1
  set xs := ((enumeration Q).filter fun h => decide (orderOf h = mx)).reverse
  have hXf := forall₂_orderTables h32 Q hmx
  have hmemxs : ∀ g, g ∈ xs ↔ g ∈ G ∧ orderOf g = mx := fun g => by
    simp only [xs, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
    rw [mem_enumeration_iff Q hV]
  set XF := xs.toFinset
  have hXF : XF.card = (CS.map ClsD.c).sum := by
    rw [List.toFinset_card_of_nodup (List.nodup_reverse.2 ((enumeration_nodup Q hV).filter _)),
      ← hXf.length_eq, hX]
  set C : Nat → Finset (Equiv.Perm (Fin n)) :=
    fun j => XF.filter fun g => g ∈ SmallOddCore.conjClass K (rs j)
  have hclG : ∀ j < L, ∀ g ∈ SmallOddCore.conjClass K (rs j), g ∈ XF := by
    intro j hj g hg
    rw [List.mem_toFinset, hmemxs]
    obtain ⟨c, hc, rfl⟩ := hg
    rw [← hGK] at hc
    refine ⟨G.mul_mem (G.mul_mem hc (hrs j hj).2) (G.inv_mem hc), ?_⟩
    rw [← (hcf j hj).2.2.2]
    exact (MulAut.conj c).orderOf_eq (rs j)
  have hCcard : ∀ j < L, (C j).card = (CS.getD j clsD0).c := by
    intro j hj
    rw [← (hcf j hj).2.1, ← Set.ncard_coe_finset]
    congr 1
    ext g
    simp only [C, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨hclG j hj g h, h⟩⟩
  have hpd : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range L, i ≠ j → Disjoint (C i) (C j) := by
    have h1 : ∀ i j, i < j → j < L → Disjoint (C i) (C j) := by
      intro i j hij hj
      rw [Finset.disjoint_left]
      intro g hgi hgj
      simp only [C, Finset.mem_filter] at hgi hgj
      exact datum_disj hQ hA hB hcls hij hj (hrs i (by omega)).1 (hrs j hj).1
        (conjClass_trans (conjClass_symm hgj.2) hgi.2)
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact h1 i j h (Finset.mem_range.1 hj)
    · exact (h1 j i h (Finset.mem_range.1 hi)).symm
  have hU : (Finset.range L).biUnion C = XF := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      obtain ⟨i, -, hgi⟩ := Finset.mem_biUnion.1 hg
      exact (Finset.mem_filter.1 hgi).1
    · rw [Finset.card_biUnion hpd, hXF, ← range_map_getD (d0 := clsD0) ClsD.c rfl,
        sum_range_list]
      exact (Finset.sum_congr rfl fun j hj => hCcard j (Finset.mem_range.1 hj)).ge
  have hg := rep_pair h32 gA gB
  have hgK := genK_pair gA gB
  refine classOK_of_closed hg hXf (fun y hy => ?_) (List.nodup_reverse.2
    ((enumeration_nodup Q hV).filter _)) (fun y hy z hz => ?_)
  · rw [hgK]
    have hyF : y ∈ (Finset.range L).biUnion C := by
      rw [hU]
      exact List.mem_toFinset.2 hy
    obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hyF
    have hj' := Finset.mem_range.1 hj
    have hyc := (Finset.mem_filter.1 hyj).2
    have e : SmallOddCore.conjClass K y = SmallOddCore.conjClass K (rs j) := by
      ext z
      exact ⟨fun h => conjClass_trans h hyc, fun h => conjClass_trans h (conjClass_symm hyc)⟩
    rw [e, (hcf j hj').2.1]
    exact (hcf j hj').2.2.1
  · rw [hgK] at hz
    rw [hmemxs] at hy ⊢
    obtain ⟨c, hc, rfl⟩ := hz
    replace hc : c ∈ G := by rw [hGK]; exact hc
    exact ⟨G.mul_mem (G.mul_mem hc hy.1) (G.inv_mem hc),
      ((MulAut.conj c).orderOf_eq y).trans hy.2⟩

omit hn hbs in
theorem zTest_iff {mx my : Nat} (hmx : 0 < mx) (hmy : 0 < my) (ws : List (List Nat × Nat))
    {X Z : Nat} {x z : Equiv.Perm (Fin n)} (pX : PRep n w X x) (hx : orderOf x = mx)
    (pZ : PRep n w Z z) :
    zTest n w (mask w) (pidn n w) mx my ws Z X = true ↔
      orderOf (x⁻¹ * z) = my ∧ wsVal mx my ws x (x⁻¹ * z) = true := by
  have hsz := chainK_szOK hQ
  have h32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  have pP := prep_pcomp h32 (prep_powK hsz pX (Nat.sub mx (nat_lit 1))).1 pZ
  have hinv : x ^ (Nat.sub mx (nat_lit 1)) = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    change x ^ (mx - 1 + 1) = 1
    rw [Nat.sub_add_cancel hmx, ← hx, pow_orderOf_eq_one]
  rw [hinv] at pP
  have e : zTest n w (mask w) (pidn n w) mx my ws Z X =
      bAnd(zFixK n w (mask w) (Nat.sub mx (nat_lit 1)) my Z X,
        bAnd(ordIs n w (mask w) (pidn n w) (pcomp n w (mask w)
            (powK n w (mask w) (pidn n w) X (Nat.sub mx (nat_lit 1))) Z) (Nat.sub my (nat_lit 1)),
          wordOrdK n w (mask w) (pidn n w) mx my ws X (pcomp n w (mask w)
            (powK n w (mask w) (pidn n w) X (Nat.sub mx (nat_lit 1))) Z))) := by
    unfold zTest
    rw [Orb.strictB_eq]
  rw [e, wordP_eq hQ pX hmy ws _ _ pP (PF.pcomp_shr _ _ h32 hw), bAnd_eq, Bool.and_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun h => h.2, fun h => ⟨zFixK_of pX pZ ?_, h⟩⟩
  rw [hinv, ← h.1, pow_orderOf_eq_one]

theorem zReps_sound' (hk64 : k ≤ 64) {XL CL : List Nat} (hlen : XL.length = CL.length)
    (hrep : ∀ i < XL.length, repK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0)
      (CL.getD i 0) = true)
    (hdist : ∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true)
    (hsum : Nat.succ (sumAllK (ordK LR k) CL XL.length) = ordK LR k)
    {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB) {mx my r cap : Nat}
    {CS : List ClsD} {reps : List (Equiv.Perm (Fin n))} (hcls : ClsOK n w tA tB mx cap CS)
    (hRs : ∀ j < CS.length, bAnd(canonK n w (mask w) (n * w) (CS.getD j clsD0).R,
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (CS.getD j clsD0).R) = true)
    (hR : reps.length = CS.length ∧ ∀ j < CS.length,
      imageList (reps.getD j 1) = (unpack n w (CS.getD j clsD0).R).toList)
    (hmx : 0 < mx) (hmy : 0 < my) (hr : 1 < r) {ws : List (List Nat × Nat)}
    (hws : ([0, 1], r) ∈ ws) {SC : List (List (List Nat))}
    (hSC : SC.length = XL.length ∧ ∀ i < XL.length, ordC n w (mask w) (XL.getD i 0) = r →
      (SC.getD i []).length = CS.length ∧ ∀ j < CS.length,
        (CS.getD j clsD0).c ≤ ((SC.getD i []).getD j []).length * 256 ∧
        ∀ b < ((SC.getD i []).getD j []).length,
          cntZK n w (mask w) (pidn n w) mx my ws (XL.getD i 0) (CS.getD j clsD0) (b * 256) 256 =
            ((SC.getD i []).getD j []).getD b 0) :
    repsTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable)
        (orderTables (certificate hn [gA, gB] words bv hbs) my) cap (wordsTest n mx my ws) =
      zTotK n w (mask w) (ordK LR k) XL CL SC r XL.length := by
  classical
  set Q := certificate hn [gA, gB] words bv hbs
  set G := Q.originalSubgroup
  set K := Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))
  set L := CS.length
  set N := ordK LR k
  set len := XL.length
  have hV := chainK_valid hQ hn hbs
  have h32 := chainK_h32 hQ
  have hsz := chainK_szOK hQ
  have hw := PF.w_pos hQ.2.1
  have hGK : G = K := orig_pair hn hbs
  have hKG : ∀ c ∈ K, c ∈ G := fun c hc => by rw [hGK]; exact hc
  have hlenR : reps.length = L := hR.1
  set rs : Nat → Equiv.Perm (Fin n) := fun j => reps.getD j 1
  have prs : ∀ j < L, PRep n w (CS.getD j clsD0).R (rs j) := fun j hj =>
    prep_of_imageList (hR.2 j hj)
  have hrsG : ∀ j < L, rs j ∈ G := fun j hj => by
    have h := hRs j hj
    rw [bAnd_eq, Bool.and_eq_true] at h
    exact (Q.sift_eq_true_iff_mem_original hV _).1 (chainK_sift hn hbs hQ (hR.2 j hj) h.1 h.2)
  have hcf := fun j (hj : j < L) => datum_class hQ hA hB hcls hj (prs j hj)
  set Gs := (enumeration Q).toFinset
  have hGs : ∀ g, g ∈ Gs ↔ g ∈ G := fun g => by
    rw [List.mem_toFinset]
    exact mem_enumeration_iff Q hV g
  have hGsc : ∀ c ∈ G, ∀ a ∈ Gs, c * a * c⁻¹ ∈ Gs ∧ c⁻¹ * a * c ∈ Gs := fun c hc a ha => by
    rw [hGs, hGs]
    have ha' := (hGs a).1 ha
    exact ⟨G.mul_mem (G.mul_mem hc ha') (G.inv_mem hc),
      G.mul_mem (G.mul_mem (G.inv_mem hc) ha') hc⟩
  have hclG : ∀ j < L, ∀ x ∈ SmallOddCore.conjClass K (rs j), x ∈ G ∧ orderOf x = mx := by
    intro j hj x hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hc' := hKG c hc
    exact ⟨G.mul_mem (G.mul_mem hc' (hrsG j hj)) (G.inv_mem hc'),
      ((MulAut.conj c).orderOf_eq (rs j)).trans (hcf j hj).2.2.2⟩
  set V : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop := fun x y => wsVal mx my ws x y = true
  have hVc : ∀ c x y, V (c * x * c⁻¹) (c * y * c⁻¹) ↔ V x y := fun c x y => by
    simp only [V, wsVal_conj]
  set P : Equiv.Perm (Fin n) → Nat := fun x => (Gs.filter fun y => orderOf y = my ∧ V x y).card
  set Cl : Nat → Finset (Equiv.Perm (Fin n)) :=
    fun j => Gs.filter fun x => x ∈ SmallOddCore.conjClass K (rs j)
  set fj : Nat → Equiv.Perm (Fin n) → Nat := fun j z =>
    ((Cl j).filter fun x => orderOf (x⁻¹ * z) = my ∧ V x (x⁻¹ * z)).card
  have hPc : ∀ c ∈ G, ∀ x, P (c * x * c⁻¹) = P x := fun c hc x =>
    (card_filter_conj c (hGsc c hc) fun a => by
      rw [orderOf_conjP, hVc]).symm
  have hshift : ∀ x ∈ G, P x =
      (Gs.filter fun z => orderOf (x⁻¹ * z) = my ∧ V x (x⁻¹ * z)).card := by
    intro x hx
    refine Finset.card_nbij' (fun y => x * y) (fun z => x⁻¹ * z) (fun a ha => ?_)
      (fun a ha => ?_) (fun a _ => inv_mul_cancel_left x a) (fun a _ => mul_inv_cancel_left x a)
    · simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
      rw [inv_mul_cancel_left]
      exact ⟨(hGs _).2 (G.mul_mem hx ((hGs a).1 ha.1)), ha.2⟩
    · simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
      exact ⟨(hGs _).2 (G.mul_mem (G.inv_mem hx) ((hGs a).1 ha.1)), ha.2⟩
  have hClc : ∀ j < L, ∀ c ∈ G, ∀ a ∈ Cl j, c * a * c⁻¹ ∈ Cl j ∧ c⁻¹ * a * c ∈ Cl j := by
    intro j hj c hc a ha
    rw [Finset.mem_filter] at ha
    have hcK : c ∈ K := by rw [← hGK]; exact hc
    simp only [Cl, Finset.mem_filter]
    have hc' : c⁻¹ * a * c = c⁻¹ * a * c⁻¹⁻¹ := by rw [inv_inv]
    refine ⟨⟨(hGsc c hc a ha.1).1, conj_mem_conjClass hcK ha.2⟩,
      ⟨(hGsc c hc a ha.1).2, ?_⟩⟩
    rw [hc']
    exact conj_mem_conjClass (K.inv_mem hcK) ha.2
  have hfjc : ∀ j < L, ∀ c ∈ G, ∀ z, fj j (c * z * c⁻¹) = fj j z := fun j hj c hc z =>
    (card_filter_conj c (hClc j hj c hc) fun a => by
      have e : (c * a * c⁻¹)⁻¹ * (c * z * c⁻¹) = c * (a⁻¹ * z) * c⁻¹ := by group
      rw [e, orderOf_conjP, hVc]).symm
  have hno1 : ∀ x, ¬ (orderOf (x⁻¹ * 1) = my ∧ V x (x⁻¹ * 1)) := fun x h => by
    have := orderOf_of_wsVal hws (by omega) h.2
    rw [mul_inv_cancel_left, orderOf_one] at this
    omega
  have hsizes := (chainK_reps3 hA hB hsz hcls hR hmx
    (X := List.replicate (CS.map ClsD.c).sum #[]) (by simp)).2.1
  have hA1 : repsTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable)
      (orderTables Q my) cap (wordsTest n mx my ws) =
      ((List.range L).map fun j => (CS.getD j clsD0).c * P (rs j)).sum := by
    refine repsTotal_eq (c := fun j => (CS.getD j clsD0).c) (N := fun j => P (rs j)) hlenR
      (fun j hj => ?_) (fun j hj => ?_)
    · have hjL : j < L := by rw [← hlenR]; exact hj
      have e := congrArg (fun l => l[j]?) hsizes
      simp only [repSizes, List.map_map, List.getElem?_map, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hjL, Option.map_some,
        Option.some.injEq, Function.comp_apply] at e
      rw [e, List.getD_eq_getElem _ _ hjL]
    · have e : reps[j] = rs j := (List.getD_eq_getElem _ _ hj).symm
      rw [e, countP_orderTables_words hQ hn hbs hmy ws]
      simp only [one_mul, List.map_id']
      rw [countP_card (enumeration_nodup Q hV)]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rfl
  have hB1 : ∀ j < L, (CS.getD j clsD0).c * P (rs j) = ∑ z ∈ Gs.erase 1, fj j z := by
    intro j hj
    have hcard : (Cl j).card = (CS.getD j clsD0).c := by
      rw [← (hcf j hj).2.1, ← Set.ncard_coe_finset]
      congr 1
      ext x
      simp only [Cl, Finset.coe_filter, Set.mem_ofPred_eq, hGs]
      exact ⟨fun h => h.2, fun h => ⟨(hclG j hj x h).1, h⟩⟩
    have e1 : ∑ x ∈ Cl j, P x = (CS.getD j clsD0).c * P (rs j) := by
      rw [Finset.sum_congr rfl (g := fun _ => P (rs j)) fun x hx => ?_, Finset.sum_const,
        smul_eq_mul, hcard]
      obtain ⟨c, hc, rfl⟩ := (Finset.mem_filter.1 hx).2
      exact hPc c (hKG c hc) (rs j)
    have e2 : ∀ x ∈ Cl j, P x =
        (Gs.filter fun z => orderOf (x⁻¹ * z) = my ∧ V x (x⁻¹ * z)).card := fun x hx =>
      hshift x ((hGs x).1 (Finset.mem_filter.1 hx).1)
    rw [← e1, Finset.sum_congr rfl e2]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, ← Finset.add_sum_erase Gs _ ((hGs 1).2 G.one_mem)]
    rw [Finset.sum_eq_zero (s := Cl j) fun x _ => by simp only [hno1 x, ↓reduceIte], Nat.zero_add]
    refine Finset.sum_congr rfl fun z _ => ?_
    exact (Finset.card_filter _ _).symm
  have hbij : ∀ j < L, ∀ {Z : Nat} {z : Equiv.Perm (Fin n)}, PRep n w Z z →
      ((Finset.range (CS.getD j clsD0).c).filter fun k' =>
        zTest n w (mask w) (pidn n w) mx my ws Z ((CS.getD j clsD0).ST k') = true).card =
        fj j z := by
    intro j hj Z z pZ
    obtain ⟨pA, pAi, pB, pBi, -, -⟩ := gens_prep hQ hA hB
    obtain ⟨hd, he, -⟩ := hcls j hj
    have hE := entry_mem_class h32 pA pAi pB pBi hd he (prs j hj)
    refine Finset.card_bij (fun k' hk' => Classical.choose (hE k'
      (Finset.mem_range.1 (Finset.mem_filter.1 hk').1))) (fun k' hk' => ?_)
      (fun a ha b hb e => ?_) (fun x hx => ?_)
    · have hs := Classical.choose_spec (hE k' (Finset.mem_range.1 (Finset.mem_filter.1 hk').1))
      have hord := (hclG j hj _ hs.1).2
      simp only [Cl, Finset.mem_filter]
      exact ⟨⟨(hGs _).2 (hclG j hj _ hs.1).1, hs.1⟩,
        (zTest_iff hQ hmx hmy ws hs.2 hord pZ).1 (Finset.mem_filter.1 hk').2⟩
    · have p1 := (Classical.choose_spec (hE a (Finset.mem_range.1 (Finset.mem_filter.1 ha).1))).2
      have p2 := (Classical.choose_spec (hE b (Finset.mem_range.1 (Finset.mem_filter.1 hb).1))).2
      rw [e] at p1
      exact entry_inj hw he (Finset.mem_range.1 (Finset.mem_filter.1 ha).1)
        (Finset.mem_range.1 (Finset.mem_filter.1 hb).1) p1 p2
    · simp only [Cl, Finset.mem_filter] at hx
      obtain ⟨⟨-, hxc⟩, hcond⟩ := hx
      obtain ⟨k', hk', pk⟩ := ((hcf j hj).1 x).1 hxc
      have hk'' : k' ∈ (Finset.range (CS.getD j clsD0).c).filter fun k' =>
          zTest n w (mask w) (pidn n w) mx my ws Z ((CS.getD j clsD0).ST k') = true :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hk',
          (zTest_iff hQ hmx hmy ws pk (hclG j hj x hxc).2 pZ).2 hcond⟩
      exact ⟨k', hk'', prep_unique (Classical.choose_spec (hE k' hk')).2 pk⟩
  set f : Equiv.Perm (Fin n) → Nat := fun z => ∑ j ∈ Finset.range L, fj j z
  have hf : ∀ c ∈ G, ∀ x, f (c * x * c⁻¹) = f x := fun c hc x =>
    Finset.sum_congr rfl fun j hj => hfjc j (Finset.mem_range.1 hj) c hc x
  set F : Nat → Nat := fun i =>
    if ordC n w (mask w) (XL.getD i 0) = r then ((SC.getD i []).map List.sum).sum else 0
  have hF : ∀ i < len, ∀ x, PRep n w (XL.getD i 0) x → F i = f x := by
    intro i hi x px
    by_cases ho : ordC n w (mask w) (XL.getD i 0) = r
    · obtain ⟨hl1, hj⟩ := hSC.2 i hi ho
      simp only [F, ho, ↓reduceIte]
      rw [list_sum_eq, List.length_map, hl1]
      refine Finset.sum_congr rfl fun j hj' => ?_
      have hj'' := Finset.mem_range.1 hj'
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getElem_map,
        ← List.getD_eq_getElem _ [] (by omega)]
      rw [sum_blocks (fun k' => zTest n w (mask w) (pidn n w) mx my ws (XL.getD i 0)
          ((CS.getD j clsD0).ST k')) _ _ (hj j hj'').1 fun b hb => by
            rw [← (hj j hj'').2 b hb, cntZK_eq],
        ← Finset.card_filter]
      exact hbij j hj'' px
    · simp only [F, ho, ↓reduceIte]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x' _ hc
      have := orderOf_of_wsVal hws (by omega) hc.2
      rw [mul_inv_cancel_left, orderOf_of_ordC px] at this
      exact ho this
  have hz : zTotK n w (mask w) N XL CL SC r len =
      ∑ i ∈ Finset.range len, N / CL.getD i 1 * F i := by
    unfold zTotK
    rw [foldN_eq]
    refine Eq.trans ?_ ((foldr_add_range (fun i => N / CL.getD i 1 * F i) len 0).trans
      (Nat.zero_add _))
    congr 1
    funext i s
    rw [nIf_eq, beq_dec]
    by_cases hc : ordC n w (mask w) (XL.getD i 0) = r
    · simp only [F, hc, decide_true, ↓reduceIte]
      rfl
    · simp only [F, hc, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero,
        Nat.add_zero]
  calc repsTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable)
        (orderTables Q my) cap (wordsTest n mx my ws)
      = ∑ j ∈ Finset.range L, (CS.getD j clsD0).c * P (rs j) := by rw [hA1, sum_range_list]
    _ = ∑ j ∈ Finset.range L, ∑ z ∈ Gs.erase 1, fj j z :=
        Finset.sum_congr rfl fun j hj => hB1 j (Finset.mem_range.1 hj)
    _ = ∑ z ∈ Gs.erase 1, f z := Finset.sum_comm
    _ = ∑ i ∈ Finset.range len, N / CL.getD i 1 * F i :=
        classSum' hQ hn hbs hk64 hlen hrep hdist hsum f hf F hF
    _ = zTotK n w (mask w) N XL CL SC r len := hz.symm

theorem zClass_sound' (hk64 : k ≤ 64) {XL CL : List Nat} (hlen : XL.length = CL.length)
    (hrep : ∀ i < XL.length, repK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0)
      (CL.getD i 0) = true)
    (hdist : ∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true)
    (hsum : Nat.succ (sumAllK (ordK LR k) CL XL.length) = ordK LR k)
    {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB) {mx my r s cap : Nat}
    {CS : List ClsD} (hcls : ClsOK n w tA tB mx cap CS)
    (hRs : ∀ j < CS.length, bAnd(canonK n w (mask w) (n * w) (CS.getD j clsD0).R,
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (CS.getD j clsD0).R) = true)
    (hmx : 0 < mx) (hmy : 0 < my) (hr : 1 < r) (hs : 0 < s)
    (hX : (orderTables (certificate hn [gA, gB] words bv hbs) mx).length = (CS.map ClsD.c).sum)
    {SC : List (List (List Nat))}
    (hSC : SC.length = XL.length ∧ ∀ i < XL.length, ordC n w (mask w) (XL.getD i 0) = r →
      (SC.getD i []).length = CS.length ∧ ∀ j < CS.length,
        (CS.getD j clsD0).c ≤ ((SC.getD i []).getD j []).length * 256 ∧
        ∀ b < ((SC.getD i []).getD j []).length,
          cntZK n w (mask w) (pidn n w) mx my [([0, 1], r), ([0, 1, 2, 3], s)] (XL.getD i 0)
            (CS.getD j clsD0) (b * 256) 256 = ((SC.getD i []).getD j []).getD b 0) :
    classTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹)
        (orderTables (certificate hn [gA, gB] words bv hbs) mx)
        (orderTables (certificate hn [gA, gB] words bv hbs) my) cap r s mx my =
      zTotK n w (mask w) (ordK LR k) XL CL SC r XL.length := by
  classical
  set Q := certificate hn [gA, gB] words bv hbs
  set G := Q.originalSubgroup
  set L := CS.length
  set ws : List (List Nat × Nat) := [([0, 1], r), ([0, 1, 2, 3], s)]
  have hV := chainK_valid hQ hn hbs
  have h32 := chainK_h32 hQ
  have hsz := chainK_szOK hQ
  have hGK : G = Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) := orig_pair hn hbs
  have hab : gA ∈ G ∧ gB ∈ G := by
    rw [hGK]
    exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
  have hex : ∀ j, ∃ x : Equiv.Perm (Fin n), j < L → PRep n w (CS.getD j clsD0).R x ∧ x ∈ G := by
    intro j
    by_cases hj : j < L
    · obtain ⟨x, px, hx⟩ := rep_of_sift hQ hn hbs (hRs j hj)
      exact ⟨x, fun _ => ⟨px, hx⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose rs hrs using hex
  set reps := (List.range L).map rs
  have hget : ∀ j < L, reps.getD j 1 = rs j := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by simpa [reps] using hj)]
    simp [reps]
  have hR : reps.length = L ∧ ∀ j < L,
      imageList (reps.getD j 1) = (unpack n w (CS.getD j clsD0).R).toList :=
    ⟨by simp [reps], fun j hj => by rw [hget j hj]; exact imageList_of_prep (hrs j hj).1⟩
  have hreps : ∀ x ∈ reps, x ∈ G ∧ orderOf x = mx := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hj' := List.mem_range.1 hj
    exact ⟨(hrs j hj').2, (datum_class hQ hA hB hcls hj' (hrs j hj').1).2.2.2⟩
  have hok := classOK_sound' hQ hn hbs hA hB hcls hRs hmx hX
  rw [← card_image_pairs_eq_classTotal₂ h32 Q hV hmx hmy (by omega) hs hab.1 hab.2 cap hok]
  have hcoe : ∀ p : G × G, (orderOf p.1 = mx ∧ orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧
      orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s) ↔
      (orderOf p.1 = mx ∧ orderOf p.2 = my ∧ WordsRel ws p.1 p.2) := fun p => by
    simp [WordsRel, ws, evalW, letterW, mul_assoc]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe)]
  have hlenC : (cosetOrderTables Q 1 mx).length = (CS.map ClsD.c).sum := by
    rw [(forall₂_cosetOrderTables h32 Q 1 hmx).length_eq, List.length_reverse, ← hX,
      (forall₂_orderTables h32 Q hmx).length_eq, List.length_reverse]
    simp only [one_mul, List.map_id']
  have hcov := (chainK_reps3 hA hB hsz hcls hR hmx (X := cosetOrderTables Q 1 mx) hlenC).1
  have hws : ∀ p ∈ ws, 0 < p.2 := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega
  rw [card_pairs_eq_repsTotal h32 Q hV hmx hmy hws (gg := fun l => if l = 0 then gA else gB)
    (fun l hl => ?_) reps hreps cap hcov]
  · exact zReps_sound' hQ hn hbs hk64 hlen hrep hdist hsum hA hB hcls hRs hR hmx hmy hr
      (by simp [ws]) hSC
  · have hl2 : l < 2 := by simpa [pairTables] using hl
    obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
    · exact ⟨by simpa [pairTables] using rep_toTable h32 gA,
        by simpa [pairTables] using rep_toTable h32 gA⁻¹, by simpa using hab.1⟩
    · exact ⟨by simpa [pairTables] using rep_toTable h32 gB,
        by simpa [pairTables] using rep_toTable h32 gB⁻¹, by simpa using hab.2⟩

end Pair

end CFSG.KS.SporSch.MOC

end
