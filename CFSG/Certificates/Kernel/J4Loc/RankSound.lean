module

public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.KS.J4Loc

open CFSG.Sporadic.J4.QT

theorem compT_assoc' (a b c : List ℕ) : compT a (compT b c) = compT (compT a b) c := by
  unfold compT
  rw [List.map_map]
  exact List.map_congr_left fun x _ => (actT_comp a b x).symm

theorem compT_idT_right' {t : List ℕ} (ht : lenOK t = true) : compT t idT = t := by
  obtain ⟨hl, -⟩ := lenOK_iff ht
  unfold compT idT
  rw [List.map_map]
  refine List.ext_getElem (by simp [hl]) fun j hj _ => ?_
  have hj11 : j < 11 := by simpa using hj
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [actT_two_pow t hj11, List.getD_eq_getElem _ _ (by omega)]

theorem seqT_cons (i : ℕ) (l : List ℕ) : seqT (i :: l) = compT (kTab i) (seqT l) := rfl

theorem mem_tabL {s : List ℕ} (hs : s ∈ tabL) : ∃ e < 1024, s = seqT (pcSeq e) := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
  exact ⟨e, List.mem_range.1 he, rfl⟩

section Cert


theorem compT_seqT_mem : ∀ l : List ℕ, (∀ i ∈ l, i < 4) → ∀ t ∈ tabL, compT t (seqT l) ∈ tabL
  | [], _, t, ht => by
    change compT t idT ∈ tabL
    rw [compT_idT_right' (tabL_ok t ht)]
    exact ht
  | i :: l, hl, t, ht => by
    rw [seqT_cons, compT_assoc']
    exact compT_seqT_mem l (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _
      (tabL_closed t ht i (hl i List.mem_cons_self)).1

theorem tabL_comp {t s : List ℕ} (ht : t ∈ tabL) (hs : s ∈ tabL) : compT t s ∈ tabL := by
  obtain ⟨e, he, rfl⟩ := mem_tabL hs
  exact compT_seqT_mem _ (pcSeq_lt e he) t ht

variable (hinv : ∀ i < 4, compT (kInvTab i) (kTab i) = idT)
include hinv

theorem seqT_inj : ∀ l : List ℕ, (∀ i ∈ l, i < 4) → lenOK (seqT l) = true ∧
    ∀ c < 2 ^ 11, ∀ d < 2 ^ 11, actT (seqT l) c = actT (seqT l) d → c = d
  | [], _ => ⟨lenOK_idT, fun c hc d hd h => by
      change actT idT c = actT idT d at h
      rwa [actT_idT hc, actT_idT hd] at h⟩
  | i :: l, hl => by
    have hi := hl i List.mem_cons_self
    obtain ⟨h1, h2⟩ := seqT_inj l fun j hj => hl j (List.mem_cons_of_mem _ hj)
    refine ⟨lenOK_compT (kTab_ok i hi).1 h1, fun c hc d hd h => ?_⟩
    rw [seqT_cons, actT_comp, actT_comp] at h
    refine h2 c hc d hd ?_
    have e1 : ∀ x < 2 ^ 11, actT (kInvTab i) (actT (kTab i) x) = x := fun x hx => by
      rw [← actT_comp, hinv i hi, actT_idT hx]
    have h' := congrArg (actT (kInvTab i)) h
    rwa [e1 _ (actT_lt h1 c), e1 _ (actT_lt h1 d)] at h'

theorem tabL_inj {t : List ℕ} (ht : t ∈ tabL) {c d : ℕ} (hc : c < 2 ^ 11) (hd : d < 2 ^ 11)
    (h : actT t c = actT t d) : c = d := by
  obtain ⟨e, he, rfl⟩ := mem_tabL ht
  exact (seqT_inj hinv _ (pcSeq_lt e he)).2 c hc d hd h

end Cert

@[expose] def actF (t : List ℕ) (c : Fin 2048) : Fin 2048 := ⟨actT t c % 2048, Nat.mod_lt _ (by norm_num)⟩

theorem actF_val {t : List ℕ} (ht : lenOK t = true) (c : Fin 2048) : (actF t c).val = actT t c :=
  Nat.mod_eq_of_lt (actT_lt ht c)

section Perm

variable (hinv : ∀ i < 4, compT (kInvTab i) (kTab i) = idT)
include hinv

theorem actF_bij {t : List ℕ} (ht : t ∈ tabL) : Function.Bijective (actF t) := by
  refine Finite.injective_iff_bijective.1 fun c d h => Fin.ext ?_
  have h' := congrArg Fin.val h
  rw [actF_val (tabL_ok t ht), actF_val (tabL_ok t ht)] at h'
  exact tabL_inj hinv ht c.isLt d.isLt h'

open Classical in
noncomputable def permT (t : List ℕ) : Equiv.Perm (Fin 2048) :=
  if h : t ∈ tabL then Equiv.ofBijective _ (actF_bij hinv h) else 1

theorem permT_apply {t : List ℕ} (ht : t ∈ tabL) (c : Fin 2048) :
    (permT hinv t c).val = actT t c := by
  unfold permT
  rw [dif_pos ht, Equiv.ofBijective_apply, actF_val (tabL_ok t ht)]

theorem permT_comp {t s : List ℕ} (ht : t ∈ tabL) (hs : s ∈ tabL) :
    permT hinv (compT t s) = permT hinv t * permT hinv s := by
  ext c
  rw [permT_apply hinv (tabL_comp ht hs), Equiv.Perm.mul_apply, permT_apply hinv ht,
    permT_apply hinv hs, actT_comp]

theorem permT_idT : permT hinv idT = 1 := by
  ext c
  rw [permT_apply hinv idT_mem, actT_idT c.isLt]
  rfl

theorem permT_injOn {t s : List ℕ} (ht : t ∈ tabL) (hs : s ∈ tabL)
    (h : permT hinv t = permT hinv s) : t = s := by
  obtain ⟨hl, -⟩ := lenOK_iff (tabL_ok t ht)
  obtain ⟨hl', -⟩ := lenOK_iff (tabL_ok s hs)
  refine List.ext_getElem (hl.trans hl'.symm) fun j hj hj' => ?_
  have hj11 : j < 11 := by omega
  have h2 := congrArg (fun p : Equiv.Perm (Fin 2048) => (p ⟨2 ^ j, by
    calc 2 ^ j < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hj11
      _ = 2048 := by norm_num⟩).val) h
  simp only [permT_apply hinv ht, permT_apply hinv hs] at h2
  rw [actT_two_pow t hj11, actT_two_pow s hj11, List.getD_eq_getElem _ _ hj,
    List.getD_eq_getElem _ _ hj'] at h2
  exact h2

noncomputable def imgU : Finset (Equiv.Perm (Fin 2048)) := tabL.toFinset.image (permT hinv)

theorem mem_imgU {x : Equiv.Perm (Fin 2048)} : x ∈ imgU hinv ↔ ∃ t ∈ tabL, permT hinv t = x := by
  unfold imgU
  simp only [Finset.mem_image, List.mem_toFinset]

theorem permT_pow_mem {x : Equiv.Perm (Fin 2048)} (hx : x ∈ imgU hinv) :
    ∀ n : ℕ, x ^ n ∈ imgU hinv
  | 0 => (mem_imgU hinv).2 ⟨idT, idT_mem, by rw [pow_zero, permT_idT]⟩
  | n + 1 => by
    obtain ⟨t, ht, rfl⟩ := (mem_imgU hinv).1 hx
    obtain ⟨s, hs, hs'⟩ := (mem_imgU hinv).1 (permT_pow_mem hx n)
    exact (mem_imgU hinv).2
      ⟨compT t s, tabL_comp ht hs, by rw [permT_comp hinv ht hs, hs', pow_succ']⟩

noncomputable def permU : Subgroup (Equiv.Perm (Fin 2048)) where
  carrier := (imgU hinv : Set (Equiv.Perm (Fin 2048)))
  mul_mem' := by
    intro x y hx hy
    obtain ⟨t, ht, rfl⟩ := (mem_imgU hinv).1 hx
    obtain ⟨s, hs, rfl⟩ := (mem_imgU hinv).1 hy
    exact (mem_imgU hinv).2 ⟨compT t s, tabL_comp ht hs, permT_comp hinv ht hs⟩
  one_mem' := (mem_imgU hinv).2 ⟨idT, idT_mem, permT_idT hinv⟩
  inv_mem' := by
    intro x hx
    have hpos := orderOf_pos x
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [this]
    exact permT_pow_mem hinv hx _

theorem natCard_permU : Nat.card (permU hinv) = 2 ^ 10 := by
  have h1 : Nat.card (permU hinv) = (imgU hinv).card := by
    rw [← Set.ncard_coe_finset]
    exact Nat.card_coe_set_eq _
  rw [h1, imgU, Finset.card_image_of_injOn fun t ht s hs h =>
    permT_injOn hinv (List.mem_toFinset.1 ht) (List.mem_toFinset.1 hs) h,
    List.toFinset_card_of_nodup tabL_nodup, tabL_length]
  norm_num

@[expose] def powT (t : List ℕ) : ℕ → List ℕ
  | 0 => idT
  | n + 1 => compT t (powT t n)

omit hinv in
theorem powT_mem {t : List ℕ} (ht : t ∈ tabL) : ∀ n, powT t n ∈ tabL
  | 0 => idT_mem
  | n + 1 => tabL_comp ht (powT_mem ht n)

theorem permT_powT {t : List ℕ} (ht : t ∈ tabL) : ∀ n, permT hinv (powT t n) = permT hinv t ^ n
  | 0 => by rw [pow_zero]; exact permT_idT hinv
  | n + 1 => by
    change permT hinv (compT t (powT t n)) = _
    rw [permT_comp hinv ht (powT_mem ht n), permT_powT ht n, pow_succ']

theorem exists_inv_pow {t : List ℕ} (ht : t ∈ tabL) (hne : t ≠ idT) :
    ∃ m, compT (powT t m) (powT t m) = idT ∧ powT t m ≠ idT := by
  have hx : permT hinv t ∈ permU hinv := (mem_imgU hinv).2 ⟨t, ht, rfl⟩
  have hdvd : orderOf (permT hinv t) ∣ 2 ^ 10 := by
    rw [← natCard_permU hinv]
    exact Subgroup.orderOf_dvd_natCard _ hx
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hne1 : permT hinv t ≠ 1 := fun h =>
    hne (permT_injOn hinv ht idT_mem (h.trans (permT_idT hinv).symm))
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne1 (orderOf_eq_one_iff.1 (by simpa using hk))
  refine ⟨2 ^ (k - 1), permT_injOn hinv (tabL_comp (powT_mem ht _) (powT_mem ht _)) idT_mem ?_,
    fun h => ?_⟩
  · rw [permT_comp hinv (powT_mem ht _) (powT_mem ht _), permT_powT hinv ht, ← pow_add,
      permT_idT, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), ← hk,
      pow_orderOf_eq_one]
  · have h1 : permT hinv t ^ 2 ^ (k - 1) = 1 := by
      rw [← permT_powT hinv ht, h, permT_idT]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hk] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Perm

@[expose] def comF (t : List ℕ) (c : ℕ) : ℕ := actT t c ^^^ c

@[expose] def sumT (t : List ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumT t c n ^^^ actT (powT t n) c

theorem lenOK_powT {t : List ℕ} (ht : lenOK t = true) : ∀ n, lenOK (powT t n) = true
  | 0 => lenOK_idT
  | n + 1 => lenOK_compT ht (lenOK_powT ht n)

theorem sumT_lt {t : List ℕ} (ht : lenOK t = true) (c : ℕ) : ∀ n, sumT t c n < 2 ^ 11
  | 0 => by simp [sumT]
  | n + 1 => Nat.xor_lt_two_pow (sumT_lt ht c n) (actT_lt (lenOK_powT ht n) c)

theorem comF_sumT (t : List ℕ) {c : ℕ} (hc : c < 2 ^ 11) :
    ∀ n, comF t (sumT t c n) = comF (powT t n) c
  | 0 => by
    change actT t 0 ^^^ 0 = actT idT c ^^^ c
    rw [actT_zero, actT_idT hc]
    simp
  | n + 1 => by
    have ih := comF_sumT t hc n
    unfold comF at ih ⊢
    change actT t (sumT t c n ^^^ actT (powT t n) c) ^^^ (sumT t c n ^^^ actT (powT t n) c) =
      actT (compT t (powT t n)) c ^^^ c
    rw [actT_xor, actT_comp]
    calc actT t (sumT t c n) ^^^ actT t (actT (powT t n) c) ^^^ (sumT t c n ^^^ actT (powT t n) c)
        = (actT t (sumT t c n) ^^^ sumT t c n) ^^^ actT t (actT (powT t n) c) ^^^
            actT (powT t n) c := by ac_rfl
      _ = actT t (actT (powT t n) c) ^^^ c ^^^ (actT (powT t n) c ^^^ actT (powT t n) c) := by
          rw [ih]; ac_rfl
      _ = actT t (actT (powT t n) c) ^^^ c := by rw [Nat.xor_self, Nat.xor_zero]

theorem img_pow_sub {t : List ℕ} (ht : lenOK t = true) (n : ℕ) :
    (Finset.range 2048).image (comF (powT t n)) ⊆ (Finset.range 2048).image (comF t) := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hy
  have hc' : c < 2 ^ 11 := by simpa using hc
  exact Finset.mem_image.2 ⟨sumT t c n, by simpa using sumT_lt ht c n, comF_sumT t hc' n⟩

theorem fixCount_eq (t : List ℕ) :
    fixCount t = ((Finset.range 2048).filter fun c => (actT t c == c) = true).card := by
  unfold fixCount
  rfl

theorem card_le_fix_mul {t : List ℕ} (ht : lenOK t = true) :
    2048 ≤ fixCount t * ((Finset.range 2048).image (comF t)).card := by
  have h := Finset.card_le_mul_card_image (f := comF t) (Finset.range 2048) (fixCount t) ?_
  · simpa using h
  intro b hb
  obtain ⟨c0, hc0, rfl⟩ := Finset.mem_image.1 hb
  have hc0' : c0 < 2 ^ 11 := by simpa using hc0
  rw [fixCount_eq]
  refine Finset.card_le_card_of_injOn (fun x => x ^^^ c0) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, beq_iff_eq]
    refine ⟨by simpa using Nat.xor_lt_two_pow (by simpa using hx.1 : x < 2 ^ 11) hc0', ?_⟩
    have h2 := hx.2
    unfold comF at h2
    rw [actT_xor]
    have h3 : actT t x = actT t c0 ^^^ c0 ^^^ x := by
      rw [← h2, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [h3]
    calc actT t c0 ^^^ c0 ^^^ x ^^^ actT t c0 = (actT t c0 ^^^ actT t c0) ^^^ (x ^^^ c0) := by
          ac_rfl
      _ = x ^^^ c0 := by rw [Nat.xor_self, Nat.zero_xor]
  · intro x _ y _ h
    simpa using h

theorem rank_ge_of
    (hinv : ∀ i < 4, compT (kInvTab i) (kTab i) = idT) {t : List ℕ} (ht : t ∈ tabL)
    (hne : t ≠ idT) :
    16 ≤ ((Finset.range 2048).image fun c => actT t c ^^^ c).card := by
  obtain ⟨m, hm1, hm2⟩ := exists_inv_pow hinv ht hne
  have hu := powT_mem ht m
  have hfix := fixCount_le _ hu hm1 hm2
  have hcard := card_le_fix_mul (tabL_ok _ hu)
  have hsub := Finset.card_le_card (img_pow_sub (tabL_ok t ht) m)
  change 16 ≤ ((Finset.range 2048).image (comF t)).card
  have : 2048 ≤ 128 * ((Finset.range 2048).image (comF (powT t m))).card :=
    hcard.trans (Nat.mul_le_mul_right _ hfix)
  omega

end CFSG.KS.J4Loc

end
