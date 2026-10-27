module

public import CFSG.LargeExtraspecial.SMod20Basic
public import CFSG.LargeExtraspecial.S14SMGBits
public import Certificates.Certificate21265

public section

namespace CFSG.LargeExtraspecial.S14.SMK

open CFSG.SmithE CFSG.LargeExtraspecial.SMod20

theorem c8PtsCheck_holds : chkC8Pts = true :=
  Certificates.certificate21265.1

theorem c8FixCheck_holds : chkC8Fix = true :=
  Certificates.certificate21265.2.1

theorem c8RestrCheck_holds : chkC8Restr = true :=
  Certificates.certificate21265.2.2.1

theorem c8IrrCheck_holds : chkC8Irr = true :=
  Certificates.certificate21265.2.2.2.1

theorem rigidCheck_holds : chkRigid = true :=
  Certificates.certificate21265.2.2.2.2

theorem decode_code (v : V) : decode (SMG.code v) = v := by
  funext m
  rw [decode_apply, SMG.testBit_code]
  simp only [m.2, ↓reduceDIte]
  generalize v m = a
  revert a
  decide

theorem applyCols_tvCols_lt {k : Nat} (hk : k < 693) (c : Nat) :
    applyCols (tvCols k) c < 2 ^ 20 :=
  SMG.applyCols_lt (fun m hm => (tvInv_parts hk m (by rwa [size_tvCols] at hm)).1) c

theorem tvEquiv_decode_eq_iff {k c : Nat} (hk : k < 693)
    (hc : c < 2 ^ 20) : tvEquiv k (decode c) = decode c ↔ applyCols (tvCols k) c = c := by
  rw [tvEquiv_decode hk]
  exact ⟨eq_of_decode_eq (applyCols_tvCols_lt hk c) hc, fun h => by rw [h]⟩

@[expose] def C8 : Submodule (ZMod 2) V where
  carrier := {v | ∀ m : Fin 20, 8 ≤ m.val → v m = 0}
  add_mem' ha hb m hm := by rw [Pi.add_apply, ha m hm, hb m hm, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c v hv m hm := by rw [Pi.smul_apply, hv m hm, smul_zero]

theorem decode_mem_C8_iff {c : Nat} (hc : c < 2 ^ 20) : decode c ∈ C8 ↔ c < 256 := by
  constructor
  · intro h
    refine Nat.lt_pow_two_of_testBit c (n := 8) fun i hi => ?_
    by_cases hi20 : i < 20
    · have := h ⟨i, hi20⟩ hi
      rw [decode_apply] at this
      cases hb : c.testBit i
      · rfl
      · rw [hb] at this; exact absurd this (by decide)
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num)
        (by omega)))
  · intro h m hm
    have h8 : (256 : Nat) ≤ 2 ^ m.val :=
      calc (256 : Nat) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ m.val := Nat.pow_le_pow_right (by norm_num) hm
    rw [decode_apply, Nat.testBit_lt_two_pow (lt_of_lt_of_le h h8)]
    rfl

theorem mem_C8_iff (v : V) :
    v ∈ C8 ↔ tvEquiv 0 v = v ∧ tvEquiv 1 v = v := by
  have h := c8FixCheck_holds
  simp only [chkC8Fix, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hc := SMG.code_lt v
  rw [← decode_code v, decode_mem_C8_iff hc, tvEquiv_decode_eq_iff (by norm_num) hc,
    tvEquiv_decode_eq_iff (by norm_num) hc]
  have e := h _ hc
  constructor
  · intro hlt
    have : (applyCols (tvCols 0) (SMG.code v) == SMG.code v &&
        applyCols (tvCols 1) (SMG.code v) == SMG.code v) = true := by
      rw [← tvArr_get (by norm_num : 0 < 693), ← tvArr_get (by norm_num : 1 < 693), e]
      exact decide_eq_true hlt
    simpa using this
  · rintro ⟨h0, h1⟩
    have : decide (SMG.code v < 256) = true := by
      rw [← e, tvArr_get (by norm_num : 0 < 693), tvArr_get (by norm_num : 1 < 693), h0, h1]
      simp
    simpa using this

theorem commute_of_commuteB {a b : Nat} (ha : a < 693)
    (hb : b < 693) (h : commuteB tvArr[a]! tvArr[b]! = true) :
    Commute (tvEquiv a) (tvEquiv b) := by
  rw [tvArr_get ha, tvArr_get hb] at h
  simp only [commuteB, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  show tvEquiv a * tvEquiv b = tvEquiv b * tvEquiv a
  apply linearEquiv_ext_single
  intro m
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, tvEquiv_single hb, tvEquiv_decode ha,
    tvEquiv_single ha, tvEquiv_decode hb, h m m.2]

theorem commuteB_of_commute {a b : Nat} (ha : a < 693)
    (hb : b < 693) (h : Commute (tvEquiv a) (tvEquiv b)) : commuteB tvArr[a]! tvArr[b]! = true := by
  rw [tvArr_get ha, tvArr_get hb]
  simp only [commuteB, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro m hm
  have e := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (Pi.single ⟨m, hm⟩ 1)) h.eq
  simp only [LinearEquiv.mul_apply, tvEquiv_single ha, tvEquiv_single hb, tvEquiv_decode ha,
    tvEquiv_decode hb] at e
  exact eq_of_decode_eq (applyCols_tvCols_lt ha _) (applyCols_tvCols_lt hb _) e

theorem commute_c8Pts {r : Nat}
    (hr : r ∈ c8Pts) :
    r < 693 ∧ Commute (tvEquiv r) (tvEquiv 0) ∧ Commute (tvEquiv r) (tvEquiv 1) := by
  have h := c8PtsCheck_holds
  simp only [chkC8Pts, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hr0, h0⟩, h1⟩ := h.2 r hr
  exact ⟨hr0, commute_of_commuteB hr0 (by norm_num) h0, commute_of_commuteB hr0 (by norm_num) h1⟩

theorem c8Pts_size : c8Pts.size = 45 := by
  have h := c8PtsCheck_holds
  simp only [chkC8Pts, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem exists_mem_c8Pts : ∃ r, r ∈ c8Pts :=
  ⟨c8Pts[0]'(by rw [c8Pts_size]; norm_num), Array.getElem_mem _⟩

theorem eq_of_restr {s r : Nat}
    (hs : s < 693) (hs0 : Commute (tvEquiv s) (tvEquiv 0))
    (hs1 : Commute (tvEquiv s) (tvEquiv 1)) (hr : r ∈ c8Pts)
    (h : ∀ v ∈ C8, tvEquiv s v = tvEquiv r v) : s = r := by
  have hc := c8RestrCheck_holds
  simp only [chkC8Restr, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, Array.all_eq_true', beq_iff_eq] at hc
  have hr693 := (commute_c8Pts hr).1
  rcases hc s hs with h1 | h1
  · rcases h1 with h1 | h1
    · exact absurd (commuteB_of_commute hs (by norm_num) hs0) (by rw [h1]; decide)
    · exact absurd (commuteB_of_commute hs (by norm_num) hs1) (by rw [h1]; decide)
  · rcases h1 r hr with h2 | h2
    · exfalso
      revert h2
      rw [Bool.eq_false_iff, ne_eq, imp_false, not_not, List.all_eq_true]
      intro b hb
      rw [List.mem_range] at hb
      have hv : decode (2 ^ b) ∈ C8 := (decode_mem_C8_iff (Nat.pow_lt_pow_right (by norm_num)
        (by omega))).mpr (Nat.pow_lt_pow_right (by norm_num) hb |>.trans_le (by norm_num))
      have e := h _ hv
      rw [tvEquiv_decode hs, tvEquiv_decode hr693, SMG.applyCols_two_pow _ (by
        rw [size_tvCols]; omega), SMG.applyCols_two_pow _ (by rw [size_tvCols]; omega)] at e
      rw [tvArr_get hs, tvArr_get hr693, beq_iff_eq]
      exact eq_of_decode_eq (tvInv_parts hs b (by omega)).1 (tvInv_parts hr693 b (by omega)).1 e
    · exact h2

theorem c8Pts_get_mem {s : Nat} (hs : s < 90) :
    c8Pts[s / 2]! ∈ c8Pts := by
  have hlt : s / 2 < c8Pts.size := by rw [c8Pts_size]; omega
  rw [getElem!_pos c8Pts (s / 2) hlt]
  exact Array.getElem_mem hlt

theorem decode_c8Step_mem
    {N : Submodule (ZMod 2) V} (hN : ∀ r ∈ c8Pts, ∀ v ∈ N, tvEquiv r v ∈ N) {s : Nat}
    (hs : s < 90) {x : Nat} (hx : decode x ∈ N) : decode (c8Step s x) ∈ N := by
  have hr := c8Pts_get_mem hs
  have hr693 := (commute_c8Pts hr).1
  have hy : decode (applyCols tvArr[c8Pts[s / 2]!]! x) ∈ N := by
    rw [tvArr_get hr693, ← tvEquiv_decode hr693]
    exact hN _ hr _ hx
  unfold c8Step
  split_ifs
  · rw [decode_xor]
    exact N.add_mem hy hx
  · exact hy

theorem decode_c8Path_mem
    {N : Submodule (ZMod 2) V} (hN : ∀ r ∈ c8Pts, ∀ v ∈ N, tvEquiv r v ∈ N) {p : List Nat}
    (hp : ∀ s ∈ p, s < 90) {x : Nat} (hx : decode x ∈ N) : decode (c8Path p x) ∈ N := by
  induction p generalizing x with
  | nil => exact hx
  | cons s p ih =>
    have e : c8Path (s :: p) x = c8Path p (c8Step s x) := by
      simp only [c8Path, List.foldl_cons]
    rw [e]
    exact ih (fun s' h => hp s' (List.mem_cons_of_mem _ h))
      (decode_c8Step_mem hN (hp s List.mem_cons_self) hx)

theorem eq_sum_single (v : V) : v = ∑ m : Fin 20, v m • Pi.single m (1 : ZMod 2) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem c8_irreducible
    (N : Submodule (ZMod 2) V) (hN8 : N ≤ C8) (hN : ∀ r ∈ c8Pts, ∀ v ∈ N, tvEquiv r v ∈ N) :
    N = ⊥ ∨ N = C8 := by
  have h := c8IrrCheck_holds
  simp only [chkC8Irr, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hback⟩, hfwd⟩ := h
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  set d := SMG.code v with hd
  have hvd : decode d = v := decode_code v
  have hdC8 : decode d ∈ C8 := by rw [hvd]; exact hN8 hvN
  have hdN : decode d ∈ N := by rw [hvd]; exact hvN
  have hd256 : d < 256 := (decode_mem_C8_iff (SMG.code_lt v)).mp hdC8
  have hd0 : d ≠ 0 := fun h0 => hv0 (by rw [← hvd, h0, decode_zero])
  have hroot : decode c8Root ∈ N := by
    rcases hback d hd256 with h1 | ⟨h1, h2⟩
    · exact absurd h1 hd0
    · rw [← h2]
      exact decode_c8Path_mem hN h1 hdN
  have hbasis : ∀ b < 8, decode (2 ^ b) ∈ N := by
    intro b hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hfwd b hb
    rw [← h3, decode_xor]
    exact N.add_mem (decode_c8Path_mem hN h1 hroot) (decode_c8Path_mem hN h2 hroot)
  refine le_antisymm hN8 fun w hw => ?_
  rw [eq_sum_single w]
  refine N.sum_mem fun m _ => ?_
  by_cases hm : m.val < 8
  · rw [← decode_two_pow]
    exact N.smul_mem _ (hbasis m.val hm)
  · rw [hw m (by omega), zero_smul]
    exact N.zero_mem

theorem rigE0_lt : rigE0 < 2 ^ 20 := by
  show 256 < 2 ^ 20
  norm_num

theorem rigW_def (e : Nat) : rigW e = applyCols tvArr[0]! e ^^^ e := rfl

theorem rigW_lt {e : Nat} (he : e < 2 ^ 20) :
    rigW e < 2 ^ 20 := by
  rw [rigW_def, tvArr_get (by norm_num)]
  exact Nat.xor_lt_two_pow (applyCols_tvCols_lt (by norm_num) _) he

theorem decode_rigW (e : Nat) :
    decode (rigW e) = tvEquiv 0 (decode e) + decode e := by
  rw [rigW_def, decode_xor, tvArr_get (by norm_num), tvEquiv_decode (by norm_num)]

theorem commute_apply {A B : V ≃ₗ[ZMod 2] V} (h : Commute A B) (v : V) : A (B v) = B (A v) := by
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) h.eq
  simpa only [LinearEquiv.mul_apply] using this

theorem fix_tvWordApply {A : V ≃ₗ[ZMod 2] V} {w : List Nat}
    (hw : ∀ r ∈ w, r < 693 ∧ Commute A (tvEquiv r)) {x : Nat} (hx : A (decode x) = decode x) :
    A (decode (tvWordApply w x)) = decode (tvWordApply w x) := by
  induction w generalizing x with
  | nil => exact hx
  | cons r w ih =>
    obtain ⟨hr, hrA⟩ := hw r List.mem_cons_self
    have e : tvWordApply (r :: w) x = tvWordApply w (applyCols tvArr[r]! x) := by
      simp only [tvWordApply, List.foldl_cons]
    rw [e]
    refine ih (fun r' h => hw r' (List.mem_cons_of_mem _ h)) ?_
    rw [tvArr_get hr, ← tvEquiv_decode hr, commute_apply hrA, hx]

theorem eq_one_of_commute
    (A : V ≃ₗ[ZMod 2] V) (hA : ∀ r ∈ c8Pts, Commute A (tvEquiv r))
    (hA0 : Commute A (tvEquiv 0)) (hA1 : Commute A (tvEquiv 1))
    (hfix : ∀ v ∈ C8, A v = v) : A = 1 := by
  have h := rigidCheck_holds
  simp only [chkRigid, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, beq_iff_eq,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Array.contains_iff_mem, beq_iff_eq,
    Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hw0, hS⟩, hfixS⟩, hwsz⟩, hcsz⟩, hlet⟩, hspan⟩ := h
  have hletter : ∀ w ∈ rigWords, ∀ r ∈ w, r < 693 ∧ Commute A (tvEquiv r) := by
    intro w hw r hr
    rcases hlet w hw r hr with (h1 | h1) | h1
    · exact ⟨(commute_c8Pts h1).1, hA r h1⟩
    · subst h1; exact ⟨by norm_num, hA0⟩
    · subst h1; exact ⟨by norm_num, hA1⟩
  have hAw0 : A (decode (rigW rigE0)) = decode (rigW rigE0) := by
    set c := SMG.code (A (decode rigE0)) with hc
    have hcA : decode c = A (decode rigE0) := decode_code _
    have hc20 : c < 2 ^ 20 := SMG.code_lt _
    have hx20 : rigW c < 2 ^ 20 := rigW_lt hc20
    have hAw : A (decode (rigW rigE0)) = decode (rigW c) := by
      rw [decode_rigW rigE0, map_add, commute_apply hA0, ← hcA, decode_rigW c]
    have hfx : ∀ s ∈ rigS, applyCols tvArr[s]! (rigW c) = rigW c := by
      intro s hs
      obtain ⟨hsP, hsw⟩ := hS s hs
      have hs693 := (commute_c8Pts hsP).1
      rw [tvArr_get hs693, ← tvEquiv_decode_eq_iff hs693 hx20, ← hAw, ← commute_apply (hA s hsP)]
      rw [tvArr_get hs693] at hsw
      rw [(tvEquiv_decode_eq_iff hs693 (rigW_lt rigE0_lt)).mpr hsw]
    rcases hfixS c hc20 with (h1 | h1) | h1
    · exfalso
      rw [List.all_eq_false] at h1
      obtain ⟨s, hs, hne⟩ := h1
      rw [hfx s hs] at hne
      exact absurd hne (by simp)
    · exfalso
      apply hw0
      have h0 : A (decode (rigW rigE0)) = 0 := by rw [hAw, h1, decode_zero]
      have : decode (rigW rigE0) = decode 0 := by
        rw [decode_zero]
        exact A.injective (by rw [h0, map_zero])
      exact eq_of_decode_eq (rigW_lt rigE0_lt) (by norm_num) this
    · rw [hAw, h1]
  set cols := (rigWords.map fun w => tvWordApply w (rigW rigE0)) ++ #[1, 2, 4, 8, 16, 32, 64, 128]
    with hcols
  have hsz : cols.size = 20 := by
    rw [hcols, Array.size_append, Array.size_map, hwsz]
    rfl
  have hvec : ∀ x ∈ cols, A (decode x) = decode x := by
    intro x hx
    rw [hcols, Array.mem_append, Array.mem_map] at hx
    rcases hx with ⟨w, hw, rfl⟩ | hx
    · exact fix_tvWordApply (hletter w hw) hAw0
    · apply hfix
      have hx' : x < 256 := by
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      exact (decode_mem_C8_iff (lt_trans hx' (by norm_num))).mpr hx'
  have hmem : ∀ j : Fin 20, cols[j.val]! ∈ cols := fun j => by
    rw [getElem!_pos cols j.val (by rw [hsz]; exact j.2)]
    exact Array.getElem_mem _
  apply linearEquiv_ext_single
  intro m
  show A (Pi.single m 1) = Pi.single m 1
  have key : A (decode (applyCols cols rigCoef[m.val]!)) =
      decode (applyCols cols rigCoef[m.val]!) := by
    rw [decode_applyCols hsz, colsLin_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hvec _ (hmem j)]
  rw [hspan m.val m.2, decode_two_pow] at key
  exact key

end CFSG.LargeExtraspecial.S14.SMK
