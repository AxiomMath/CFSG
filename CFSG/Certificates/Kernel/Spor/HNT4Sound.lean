module

public import Certificates.Data.Kernel.Spor.HNT4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNTests
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace CFSG.KS.HNT4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.BaseEq CFSG.KS.HNA CFSG.KC.BfsPin
open CFSG.ComponentClassification.RankTwoSporadic.HN CFSG.Monster.B.Co2.Native
open CFSG.ONSchreier.Native

@[expose] noncomputable def poolRec (WN P : Nat → Nat) (j : Nat) : List Int × List Int :=
  (wordAt WN (P j + 1) (WN (P j)), wordAt WN (P j + 2 + WN (P j)) (WN (P j + 1 + WN (P j))))

@[expose] noncomputable def t4Wit (WN P : Nat → Nat) (j : Nat) : T4Wit :=
  if WN (P j) = 0 then .skip
  else if WN (P j) = 1 then
    .ord4 (listUp (fun t => WN (P j + 2 + t)) (WN (P j + 1))) (WN (P j + 2 + WN (P j + 1)))
  else if WN (P j) = 2 then .faith (WN (P j + 1)) (WN (P j + 2))
  else .noInv (WN (P j + 1))

private theorem bAnd_t4 (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

private theorem strictN_t4 (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem forIn_iter_t4 {β : Type} (g : ℕ → β → Id (ForInStep β))
    (hg : ∀ x s, g x s = pure (ForInStep.yield (g 0 s).value)) :
    ∀ (a m : ℕ) (b : β), forIn (m := Id) (List.range' a m) b g =
      pure ((fun s => (g 0 s).value)^[m] b)
  | _, 0, _ => rfl
  | a, m + 1, b => by
    rw [List.range'_succ, List.forIn_cons, hg, pure_bind, Function.iterate_succ_apply]
    exact forIn_iter_t4 g hg (a + 1) m _

private theorem iterate_reach_t4 {β : Type} {F : β → β} (S : ℕ → β) {K M : ℕ} {b0 : β}
    (h0 : S 0 = b0) (hstep : ∀ j < K, F (S j) = S (j + 1)) (hfix : F (S K) = S K)
    (hKM : K ≤ M) : F^[M] b0 = S K := by
  subst h0
  have h1 : ∀ j ≤ K, F^[j] (S 0) = S j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih (by omega), hstep j (by omega)]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKM
  rw [Nat.add_comm K d, Function.iterate_add_apply, h1 K le_rfl, Function.iterate_fixed hfix]

private theorem pos_bounds_t4 {P : ℕ → ℕ} {N K : ℕ} (hPK : P K = N)
    (hlt : ∀ j < K, P j < P (j + 1)) : K ≤ N ∧ ∀ j < K, P (j + 1) ≤ N := by
  have hle : ∀ i j, j + i ≤ K → P j ≤ P (j + i) := by
    intro i
    induction i with
    | zero => intro j _; exact le_rfl
    | succ i ih =>
      intro j hj
      have h1 := ih j (by omega)
      have h2 := hlt (j + i) (by omega)
      rw [← Nat.add_assoc]
      omega
  have hge : ∀ j ≤ K, j ≤ P j := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
      have := ih (by omega)
      have := hlt j (by omega)
      omega
  refine ⟨hPK ▸ hge K le_rfl, fun j hj => ?_⟩
  have := hle (K - (j + 1)) (j + 1) (by omega)
  rwa [Nat.add_sub_cancel' hj, hPK] at this

private theorem arr_size_t4 (WN : ℕ → ℕ) (N : ℕ) : ((List.range N).map WN).toArray.size = N := by
  simp

private theorem arr_get_t4 {WN : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    ((List.range N).map WN).toArray[i]! = WN i := by
  simp [hi]

private theorem arr_extract_t4 {WN : ℕ → ℕ} {N a l : ℕ} (h : a + l ≤ N) :
    (((List.range N).map WN).toArray.extract a (a + l)).toList = (List.range' a l).map WN := by
  apply List.ext_getElem
  · simp
    omega
  · intro i h1 h2
    simp [List.getElem_range']

private theorem listUp_from_t4 (F : ℕ → ℕ) : ∀ (k j : ℕ),
    Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun _ ih j => List.cons (F j) (ih (Nat.succ j))) k j = (List.range' j k).map F
  | 0, _ => rfl
  | k + 1, j => by
    rw [List.range'_succ, List.map_cons, ← listUp_from_t4 F k (j + 1)]

private theorem listUp_shift_t4 (WN : ℕ → ℕ) (s L : ℕ) :
    listUp (fun t => WN (s + t)) L = (List.range' s L).map WN := by
  unfold listUp
  rw [listUp_from_t4, List.range'_eq_map_range, List.range'_eq_map_range, List.map_map,
    List.map_map]
  simp only [Function.comp_def, Nat.zero_add]

private theorem wordAt_t4 (WN : ℕ → ℕ) (s L : ℕ) :
    wordAt WN s L = ((List.range' s L).map WN).map fun x => (x : ℤ) - 11 := by
  unfold wordAt listUp
  rw [listUp_from_t4]
  simp only [bind_pure_comp, List.map_eq_map, List.map_map, List.range'_eq_map_range]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, Int.subNatNat_eq_coe, Nat.add_eq, Nat.zero_add]
  rfl

private theorem poolPos_spec {WN P : ℕ → ℕ} {N K : ℕ} (h : poolPosK WN P N K = true) :
    P 0 = 0 ∧ P K = N ∧ ∀ j < K, P (j + 1) = P j + 2 + WN (P j) + WN (P j + 1 + WN (P j)) := by
  unfold poolPosK at h
  rw [bAnd_t4, Bool.and_eq_true, bAnd_t4, Bool.and_eq_true, CFSG.KC.BfsPin.allN_eq',
    List.all_eq_true] at h
  obtain ⟨h0, hK, hs⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true hK, fun j hj => ?_⟩
  have e : poolLen WN (P j) = 2 + WN (P j) + WN (P j + 1 + WN (P j)) := by
    unfold poolLen
    rw [strictN_t4]
    rfl
  have := Nat.eq_of_beq_eq_true (hs j (List.mem_range.2 hj))
  change P (j + 1) = P j + poolLen WN (P j) at this
  rw [this, e]
  omega

private theorem t4Pos_spec {WN P : ℕ → ℕ} {N K : ℕ} (h : t4PosK WN P N K = true) :
    P 0 = 0 ∧ P K = N ∧ ∀ j < K, P (j + 1) = P j + t4Len WN (P j) := by
  unfold t4PosK at h
  rw [bAnd_t4, Bool.and_eq_true, bAnd_t4, Bool.and_eq_true, CFSG.KC.BfsPin.allN_eq',
    List.all_eq_true] at h
  obtain ⟨h0, hK, hs⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true hK,
    fun j hj => Nat.eq_of_beq_eq_true (hs j (List.mem_range.2 hj))⟩

private theorem t4Len_t4 (WN : ℕ → ℕ) (s : ℕ) :
    t4Len WN s = if WN s = 0 then 1 else if WN s = 1 then 3 + WN (s + 1)
      else if WN s = 2 then 3 else 2 := by
  unfold t4Len
  rw [strictN_t4]
  rcases WN s with _ | _ | _ | c <;> rfl

private theorem beq_true_t4 {a b : ℕ} (h : a = b) : (a == b) = true := by simp [h]

private theorem beq_false_t4 {a b : ℕ} (h : ¬ a = b) : ¬ ((a == b) = true) := by simp [h]

theorem decodePoolT4_sound {s : String} {WN P : Nat → Nat} {N K : Nat}
    (hs : parseNatsHN s = ((List.range N).map WN).toArray) (h : poolPosK WN P N K = true) :
    decodePoolT4 s = Array.ofFn (n := K) fun j => poolRec WN P j.val := by
  obtain ⟨hP0, hPK, hst⟩ := poolPos_spec h
  have hlt : ∀ j < K, P j < P (j + 1) := fun j hj => by rw [hst j hj]; omega
  obtain ⟨hKN, hPN⟩ := pos_bounds_t4 hPK hlt
  unfold decodePoolT4
  simp only [Id.run, hs, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [forIn_iter_t4,
    iterate_reach_t4 (fun j => ((Array.ofFn (n := j) fun i => poolRec WN P i.val), P j)) (K := K)]
  · rfl
  · rw [hP0]
    rfl
  · intro j hj
    have hPj : P j < N := lt_of_lt_of_le (hlt j hj) (hPN j hj)
    have hj1 := hst j hj
    have hj2 := hPN j hj
    dsimp only
    rw [if_pos (show P j < (List.map WN (List.range N)).toArray.size by
        rw [arr_size_t4]; exact hPj),
      arr_get_t4 hPj, arr_get_t4 (show P j + 1 + WN (P j) < N by omega),
      arr_extract_t4 (show P j + 1 + WN (P j) ≤ N by omega),
      arr_extract_t4 (show P j + 2 + WN (P j) + WN (P j + 1 + WN (P j)) ≤ N by omega)]
    show ((Array.ofFn fun i : Fin j => poolRec WN P i.val).push _, _) = _
    rw [Array.ofFn_succ, hj1]
    simp only [Fin.coe_castSucc, poolRec, wordAt_t4]
  · dsimp only
    rw [if_neg (show ¬ P K < (List.map WN (List.range N)).toArray.size by
      rw [arr_size_t4, hPK]; exact Nat.lt_irrefl N)]
    rfl
  · rw [arr_size_t4]
    exact hKN
  · intro x s
    split_ifs <;> rfl

theorem decodeT4_sound {s : String} {WN P : Nat → Nat} {N K : Nat}
    (hs : parseNatsHN s = ((List.range N).map WN).toArray) (h : t4PosK WN P N K = true) :
    decodeT4 s = Array.ofFn (n := K) fun j => t4Wit WN P j.val := by
  obtain ⟨hP0, hPK, hst⟩ := t4Pos_spec h
  have hlt : ∀ j < K, P j < P (j + 1) := fun j hj => by
    have := hst j hj
    rw [t4Len_t4] at this
    split_ifs at this <;> omega
  obtain ⟨hKN, hPN⟩ := pos_bounds_t4 hPK hlt
  unfold decodeT4
  simp only [Id.run, hs, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [forIn_iter_t4,
    iterate_reach_t4 (fun j => ((Array.ofFn (n := j) fun i => t4Wit WN P i.val), P j)) (K := K)]
  · rfl
  · rw [hP0]
    rfl
  · intro j hj
    have hPj : P j < N := lt_of_lt_of_le (hlt j hj) (hPN j hj)
    have hj1 := hst j hj
    have hj2 := hPN j hj
    rw [t4Len_t4] at hj1
    dsimp only
    rw [if_pos (show P j < (List.map WN (List.range N)).toArray.size by
        rw [arr_size_t4]; exact hPj),
      arr_get_t4 hPj]
    by_cases c0 : WN (P j) = 0
    · rw [if_pos (beq_true_t4 c0)]
      rw [if_pos c0] at hj1
      show ((Array.ofFn fun i : Fin j => t4Wit WN P i.val).push _, _) = _
      rw [Array.ofFn_succ, hj1]
      simp only [Fin.coe_castSucc, t4Wit, if_pos c0]
    rw [if_neg (beq_false_t4 c0)]
    rw [if_neg c0] at hj1
    by_cases c1 : WN (P j) = 1
    · rw [if_pos (beq_true_t4 c1)]
      rw [if_pos c1] at hj1
      rw [arr_get_t4 (show P j + 1 < N by omega),
        arr_extract_t4 (show P j + 2 + WN (P j + 1) ≤ N by omega),
        arr_get_t4 (show P j + 2 + WN (P j + 1) < N by omega)]
      show ((Array.ofFn fun i : Fin j => t4Wit WN P i.val).push _, _) = _
      rw [Array.ofFn_succ, show P (j + 1) = P j + 3 + WN (P j + 1) by omega]
      simp only [Fin.coe_castSucc, t4Wit, if_neg c0, if_pos c1, listUp_shift_t4]
    rw [if_neg (beq_false_t4 c1)]
    rw [if_neg c1] at hj1
    by_cases c2 : WN (P j) = 2
    · rw [if_pos (beq_true_t4 c2)]
      rw [if_pos c2] at hj1
      rw [arr_get_t4 (show P j + 1 < N by omega), arr_get_t4 (show P j + 2 < N by omega)]
      show ((Array.ofFn fun i : Fin j => t4Wit WN P i.val).push _, _) = _
      rw [Array.ofFn_succ, hj1]
      simp only [Fin.coe_castSucc, t4Wit, if_neg c0, if_neg c1, if_pos c2]
    rw [if_neg (beq_false_t4 c2)]
    rw [if_neg c2] at hj1
    rw [arr_get_t4 (show P j + 1 < N by omega)]
    show ((Array.ofFn fun i : Fin j => t4Wit WN P i.val).push _, _) = _
    rw [Array.ofFn_succ, hj1]
    simp only [Fin.coe_castSucc, t4Wit, if_neg c0, if_neg c1, if_neg c2]
  · dsimp only
    rw [if_neg (show ¬ P K < (List.map WN (List.range N)).toArray.size by
      rw [arr_size_t4, hPK]; exact Nat.lt_irrefl N)]
    rfl
  · rw [arr_size_t4]
    exact hKN
  · intro x s
    split_ifs <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bIf_eq' (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by cases c <;> rfl

theorem bAnd_eq' (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem allL_iff' : ∀ (L : List Nat) (f : Nat → Bool), allL L f = true ↔ ∀ x ∈ L, f x = true
  | [], _ => by simp [allL]
  | x :: L, f => by
    have ih := allL_iff' L f
    change bAnd(f x, allL L f) = true ↔ _
    rw [bAnd_eq', Bool.and_eq_true, ih]
    simp

theorem t4WK_spec {ps : List Nat} {WN P T CP CQ : Nat → Nat} {I nc k : Nat}
    (h : t4WK ps WN P T CP CQ I nc k = true) :
    (WN (P k) = 0 ∧ (k = 0 ∨ sqFixK 10 (mask 10) ps (T k) = false)) ∨
    (WN (P k) = 1 ∧ (∀ f ∈ listUp (fun t => WN (P k + 2 + t)) (WN (P k + 1)), f < nc) ∧
      ord4K 800 10 I (ppow 800 10 (mask 10) I
        (prodL I ((listUp (fun t => WN (P k + 2 + t)) (WN (P k + 1))).map
          fun f => zP (T k) (CP f) (CQ f))) (WN (P k + 2 + WN (P k + 1)))) = true) ∨
    (WN (P k) = 2 ∧ WN (P k + 1) < nc ∧ WN (P k + 2) < 1140000 ∧
      pcomp 800 10 (mask 10) (zP (T k) (CP (WN (P k + 1))) (CQ (WN (P k + 1))))
        (zP (T k) (CP (WN (P k + 1))) (CQ (WN (P k + 1)))) = I) ∨
    (WN (P k) = 3 ∧ WN (P k + 1) < 1140000) := by
  unfold t4WK at h
  simp only [strictB_eq', bIf_eq', Nat.add_eq, Nat.succ_eq_add_one] at h
  rcases hc : WN (P k) with _ | _ | _ | _ | c <;> simp only [hc] at h
  · refine Or.inl ⟨rfl, ?_⟩
    by_cases k0 : k = 0
    · exact Or.inl k0
    · simpa [k0] using h
  · have e0 : Nat.beq (0 + 1) 0 = false := rfl
    have e1 : Nat.beq (0 + 1) 1 = true := rfl
    simp only [e0, e1, Bool.false_eq_true, if_false, if_true] at h
    split_ifs at h with h1
    · exact Or.inr (Or.inl ⟨rfl, fun f hf => Nat.blt_eq.mp ((allL_iff' _ _).1 h1 f hf), h⟩)
  · have e0 : Nat.beq (0 + 1 + 1) 0 = false := rfl
    have e1 : Nat.beq (0 + 1 + 1) 1 = false := rfl
    have e2 : Nat.beq (0 + 1 + 1) 2 = true := rfl
    simp only [e0, e1, e2, Bool.false_eq_true, if_false, if_true] at h
    split_ifs at h with h1 h2
    exact Or.inr (Or.inr (Or.inl ⟨rfl, Nat.blt_eq.mp h1, Nat.blt_eq.mp h2,
      Nat.eq_of_beq_eq_true h⟩))
  · have e0 : Nat.beq (0 + 1 + 1 + 1) 0 = false := rfl
    have e1 : Nat.beq (0 + 1 + 1 + 1) 1 = false := rfl
    have e2 : Nat.beq (0 + 1 + 1 + 1) 2 = false := rfl
    have e3 : Nat.beq (0 + 1 + 1 + 1) 3 = true := rfl
    simp only [e0, e1, e2, e3, Bool.false_eq_true, if_false, if_true] at h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, Nat.blt_eq.mp h⟩))
  · have e0 : Nat.beq (c + 1 + 1 + 1 + 1) 0 = false := rfl
    have e1 : Nat.beq (c + 1 + 1 + 1 + 1) 1 = false := rfl
    have e2 : Nat.beq (c + 1 + 1 + 1 + 1) 2 = false := rfl
    have e3 : Nat.beq (c + 1 + 1 + 1 + 1) 3 = false := rfl
    simp only [e0, e1, e2, e3, Bool.false_eq_true, if_false] at h

abbrev Cn (p : Nat) : Prop := canonK 800 10 (mask 10) (800 * 10) p = true

theorem cn_pcomp {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pcomp 800 10 (mask 10) p q) :=
  canonK_pcomp hp hq

theorem sz800 : szOK 800 10 = true := by decide

theorem cn_id : Cn (pidn 800 10) := (PP.id sz800).1

theorem pid_unpack : pid 800 = unpack 800 10 (pidn 800 10) :=
  (idK_sound (idK_of_szOK sz800)).symm

theorem pcomp_unpack {p q : Nat} (hp : Cn p) (hq : Cn q) :
    CFSG.ONSchreier.Native.pcomp 800 (unpack 800 10 p) (unpack 800 10 q) =
      unpack 800 10 (pcomp 800 10 (mask 10) p q) :=
  compA_unpack hp hq

theorem peq_unpack {p q : Nat} (hp : Cn p) (hq : Cn q) :
    peq 800 (unpack 800 10 p) (unpack 800 10 q) = Nat.beq p q :=
  eqA_unpack hp hq

theorem cn_zP {e a b : Nat} (he : Cn e) (ha : Cn a) (hb : Cn b) : Cn (zP e a b) :=
  cn_pcomp (cn_pcomp he ha) (cn_pcomp he hb)

theorem zT4_unpack {e a b : Nat} (he : Cn e) (ha : Cn a) (hb : Cn b) :
    zT4 (unpack 800 10 e) (unpack 800 10 a, unpack 800 10 b) = unpack 800 10 (zP e a b) := by
  unfold zT4 zP
  rw [pcomp_unpack he ha, pcomp_unpack he hb, pcomp_unpack (cn_pcomp he ha) (cn_pcomp he hb)]

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem prodL_cons (I a : Nat) (l : List Nat) :
    prodL I (a :: l) = pcomp 800 10 (mask 10) a (prodL I l) :=
  strictN_eq' _ _

theorem prodP_nil : prodP 800 [] = pid 800 := List.foldr_nil

theorem prodP_cons (x : Array Nat) (l : List (Array Nat)) :
    prodP 800 (x :: l) = CFSG.ONSchreier.Native.pcomp 800 x (prodP 800 l) := List.foldr_cons

theorem prodL_nil (I : Nat) : prodL I [] = I := rfl

theorem powP_zero (a : Array Nat) : powP 800 a 0 = pid 800 := prodP_nil

theorem powP_succ (a : Array Nat) (m : Nat) :
    powP 800 a (m + 1) = CFSG.ONSchreier.Native.pcomp 800 a (powP 800 a m) := by
  unfold powP
  rw [List.replicate_succ, prodP_cons]

theorem ppow_zero (I p : Nat) : ppow 800 10 (mask 10) I p 0 = I := rfl

theorem prodP_unpack : ∀ l : List Nat, (∀ a ∈ l, Cn a) →
    prodP 800 (l.map (unpack 800 10)) = unpack 800 10 (prodL (pidn 800 10) l) ∧
      Cn (prodL (pidn 800 10) l)
  | [], _ => by
    rw [List.map_nil, prodP_nil, prodL_nil]
    exact ⟨pid_unpack, cn_id⟩
  | a :: l, h => by
    obtain ⟨ih, hc⟩ := prodP_unpack l fun b hb => h b (List.mem_cons_of_mem a hb)
    have ha := h a List.mem_cons_self
    rw [prodL_cons]
    refine ⟨?_, cn_pcomp ha hc⟩
    rw [List.map_cons, prodP_cons, ih, pcomp_unpack ha hc]

theorem ppow_succ (I p k : Nat) :
    ppow 800 10 (mask 10) I p (k + 1) = pcomp 800 10 (mask 10) p (ppow 800 10 (mask 10) I p k) :=
  strictN_eq' _ _

theorem powP_unpack {p : Nat} (hp : Cn p) : ∀ m : Nat,
    powP 800 (unpack 800 10 p) m = unpack 800 10 (ppow 800 10 (mask 10) (pidn 800 10) p m) ∧
      Cn (ppow 800 10 (mask 10) (pidn 800 10) p m)
  | 0 => by
    rw [powP_zero, ppow_zero]
    exact ⟨pid_unpack, cn_id⟩
  | m + 1 => by
    obtain ⟨ih, hc⟩ := powP_unpack hp m
    rw [ppow_succ]
    refine ⟨?_, cn_pcomp hp hc⟩
    rw [powP_succ, ih, pcomp_unpack hp hc]

theorem ord4P_unpack {y : Nat} (hy : Cn y)
    (h : ord4K 800 10 (pidn 800 10) y = true) : ord4P 800 (unpack 800 10 y) = true := by
  unfold ord4K at h
  rw [strictB_eq', bAnd_eq'] at h
  have h2 := cn_pcomp hy hy
  unfold ord4P
  rw [pcomp_unpack hy hy, pid_unpack, peq_unpack h2 cn_id, pcomp_unpack h2 h2,
    peq_unpack (cn_pcomp h2 h2) cn_id]
  exact h

end CFSG.KS.HNT4

end
