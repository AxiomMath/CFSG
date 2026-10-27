module

public import Certificates.Data.Kernel.SporSch.LyFiveTb
public import CFSG.RankThree.Native.LyFiveImagesInputs
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.LyFiveTb

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyFiveTb CFSG.RankThree.Native

@[expose] noncomputable def dec (x : Nat) : Array (ZMod 5) := Array.ofFn (n := 16) fun t => ((dig8 x t.val : Nat) : ZMod 5)

theorem dig8_eq (x t : Nat) : dig8 x t = x / 8 ^ t % 8 := by
  unfold dig8
  change (x >>> (3 * t)) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem enc8_cons (v : Nat) (l : List Nat) : enc8 (v :: l) = v + 8 * enc8 l := rfl

theorem enc8_digit : ∀ (l : List Nat), (∀ v ∈ l, v < 8) → ∀ s < l.length,
    enc8 l / 8 ^ s % 8 = l.getD s 0
  | [], _, s, hs => absurd hs (by simp)
  | v :: l, h, s, hs => by
    rw [enc8_cons]
    have hv : v < 8 := h v (by simp)
    cases s with
    | zero =>
      simp only [pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    | succ s =>
      have e : (v + 8 * enc8 l) / 8 = enc8 l := by omega
      rw [pow_succ', ← Nat.div_div_eq_div_mul, e, List.getD_cons_succ]
      exact enc8_digit l (fun w hw => h w (by simp [hw])) s (by simpa using hs)

theorem ent4_eq (m y t : Nat) : ent4 m y t =
    (dig8 m (4 * (t / 4)) * dig8 y (t % 4) + dig8 m (4 * (t / 4) + 1) * dig8 y (4 + t % 4) +
      dig8 m (4 * (t / 4) + 2) * dig8 y (8 + t % 4) + dig8 m (4 * (t / 4) + 3) * dig8 y (12 + t % 4))
      % 5 := rfl

theorem ent4_lt (m y t : Nat) : ent4 m y t < 5 := by
  unfold ent4
  exact Nat.mod_lt _ (by norm_num)

theorem dig8_mul4K (m y : Nat) {t : Nat} (ht : t < 16) : dig8 (mul4K m y) t = ent4 m y t := by
  rw [dig8_eq]
  unfold mul4K
  have h := enc8_digit (ents4 m y) (by
    intro v hv
    unfold ents4 at hv
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hv
    exact Nat.lt_of_lt_of_le (ent4_lt m y u) (by norm_num)) t (by simpa [ents4] using ht)
  rw [h]
  unfold ents4
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  simp

theorem dec_get {x i : Nat} (hi : i < 16) : (dec x)[i]! = ((dig8 x i : Nat) : ZMod 5) := by
  unfold dec
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem fiveMul4_dec (m y : Nat) : fiveMul4 (dec m) (dec y) = dec (mul4K m y) := by
  apply Array.ext
  · simp [fiveMul4, dec]
  · intro t h1 _
    have ht : t < 16 := by simpa [fiveMul4] using h1
    have lhs : (fiveMul4 (dec m) (dec y))[t] =
        ∑ l : Fin 4, (dec m)[4 * (t / 4) + l.val]! * (dec y)[4 * l.val + t % 4]! := by
      simp only [fiveMul4, Array.getElem_ofFn]
    have rhs : (dec (mul4K m y))[t] = ((dig8 (mul4K m y) t : Nat) : ZMod 5) := by
      simp only [dec, Array.getElem_ofFn]
    refine lhs.trans (Eq.trans ?_ rhs.symm)
    rw [Fin.sum_univ_four, dig8_mul4K m y ht, ent4_eq, ZMod.natCast_mod]
    have e0 : ((0 : Fin 4) : Nat) = 0 := rfl
    have e1 : ((1 : Fin 4) : Nat) = 1 := rfl
    have e2 : ((2 : Fin 4) : Nat) = 2 := rfl
    have e3 : ((3 : Fin 4) : Nat) = 3 := rfl
    rw [e0, e1, e2, e3, dec_get (by omega), dec_get (by omega), dec_get (by omega),
      dec_get (by omega), dec_get (by omega), dec_get (by omega), dec_get (by omega),
      dec_get (by omega)]
    push_cast
    ring_nf

theorem recompose : ∀ (n x : Nat), x < 8 ^ n → x = enc8 ((List.range n).map fun t => x / 8 ^ t % 8)
  | 0, x, h => by simp at h; subst h; rfl
  | n + 1, x, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, enc8_cons]
    have ih := recompose n (x / 8) (by rw [pow_succ] at h; omega)
    have e : ((fun t => x / 8 ^ t % 8) ∘ Nat.succ) = fun t => x / 8 / 8 ^ t % 8 := by
      funext t
      simp only [Function.comp, pow_succ, Nat.div_div_eq_div_mul, mul_comm]
    rw [e, ← ih]
    simp only [pow_zero, Nat.div_one]
    omega

@[expose] def Red (x : Nat) : Prop := x < 8 ^ 16 ∧ ∀ t < 16, dig8 x t < 5

theorem dec_inj {x y : Nat} (hx : Red x) (hy : Red y) (h : dec x = dec y) : x = y := by
  have hd : ∀ t < 16, x / 8 ^ t % 8 = y / 8 ^ t % 8 := by
    intro t ht
    have e := congrArg (fun a => a[t]!) h
    simp only [dec_get ht] at e
    have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
    rw [Nat.mod_eq_of_lt (hx.2 t ht), Nat.mod_eq_of_lt (hy.2 t ht)] at this
    rwa [dig8_eq, dig8_eq] at this
  rw [recompose 16 x hx.1, recompose 16 y hy.1]
  congr 1
  exact List.map_congr_left fun t ht => hd t (List.mem_range.1 ht)

theorem key48_lt (T k : Nat) : key48 T k < 8 ^ 16 := by
  unfold key48
  change (T >>> (48 * k)) &&& (2 ^ 48 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)

theorem red_mul4K_key {m y : Nat} (T k : Nat) (h : key48 T k = mul4K m y) : Red (key48 T k) :=
  ⟨key48_lt T k, fun t ht => by rw [h, dig8_mul4K m y ht]; exact ent4_lt m y t⟩

theorem red_id4K : ∀ t < 16, dig8 id4K t < 5 := by decide

theorem andOf {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h Bool.false_ne_true

theorem fold_push {α : Type} (f : Nat → Array α → α) :
    ∀ n, (Nat.fold n (fun k _ acc => acc.push (f k acc)) #[]).size = n
  | 0 => by rw [Nat.fold_zero]; rfl
  | n + 1 => by rw [Nat.fold_succ, Array.size_push, fold_push f n]

theorem fold_push_get {α : Type} [Inhabited α] (f : Nat → Array α → α) :
    ∀ n, ∀ k < n, (Nat.fold n (fun k _ acc => acc.push (f k acc)) #[])[k]! =
      f k (Nat.fold k (fun k _ acc => acc.push (f k acc)) #[])
  | 0, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hk => by
    rw [Nat.fold_succ]
    have hs := fold_push f n
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
    · rw [getElem!_pos _ k (by rw [Array.size_push]; omega), Array.getElem_push_lt (by omega),
        ← getElem!_pos _ k (by omega)]
      exact fold_push_get f n k h
    · rw [getElem!_pos _ k (by rw [Array.size_push]; omega)]
      simp [Array.getElem_push, hs]

theorem unpack_get {n w P i : Nat} (hi : i < n) :
    (CFSG.KS.Raw.unpack n w P)[i]! = pg w (mask w) P i := by
  unfold CFSG.KS.Raw.unpack
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem tbArr_eq {G0 G1 PAR GEN KS : Nat} (hA : fiveArr4 lyFiveAbar = dec G0)
    (hB : fiveArr4 lyFiveBbar = dec G1) (hI : fiveArr4 1 = dec id4K)
    (hP : lyFiveParArr = CFSG.KS.Raw.unpack 2880 12 PAR)
    (hG : lyFiveGenArr = CFSG.KS.Raw.unpack 2880 12 GEN)
    (htb : tbOK G0 G1 PAR GEN KS = true) :
    ∀ n ≤ 2880, ∀ k < n,
      (Nat.fold n (fun k _ acc => acc.push (lyFiveTbStep k acc)) #[])[k]! = dec (key48 KS k) := by
  have hat : ∀ k < 2880, tbAt G0 G1 PAR GEN KS k = true := CFSG.KC.Pack.allN_spec htb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn k hk
    rw [fold_push_get _ n k hk]
    have hk' : k < 2880 := by omega
    have h := hat k hk'
    unfold tbAt at h
    by_cases h0 : k = 0
    · subst h0
      simp only [Nat.beq_refl] at h
      unfold lyFiveTbStep
      rw [if_pos rfl, hI, Nat.eq_of_beq_eq_true h]
    · have hb : Nat.beq k 0 = false := Bool.eq_false_iff.mpr fun e => h0 (Nat.eq_of_beq_eq_true e)
      rw [hb] at h
      simp only at h
      obtain ⟨h1, h2⟩ := andOf h
      obtain ⟨h2, h3⟩ := andOf h2
      have hpk := Nat.blt_eq.mp h1
      have ep : lyFiveParArr[k]! = pg 12 (mask 12) PAR k := by rw [hP, unpack_get hk']
      have eg : lyFiveGenArr[k]! = pg 12 (mask 12) GEN k := by rw [hG, unpack_get hk']
      have es : ∀ acc, lyFiveTbStep k acc = fiveMul4 (fiveArr4 (if lyFiveGenArr[k]! = 1 then
          lyFiveBbar else lyFiveAbar)) acc[lyFiveParArr[k]!]! := fun acc => by
        unfold lyFiveTbStep
        rw [if_neg h0]
      rw [es, ep, eg, ih k hk (by omega) _ hpk, Nat.eq_of_beq_eq_true h3]
      by_cases hg : pg 12 (mask 12) GEN k = 1
      · rw [if_pos hg, hB, fiveMul4_dec]
        have : Nat.beq (pg 12 (mask 12) GEN k) 1 = true := by rw [hg]; rfl
        rw [this]
      · rw [if_neg hg, hA, fiveMul4_dec]
        have : Nat.beq (pg 12 (mask 12) GEN k) 1 = false :=
          Bool.eq_false_iff.mpr fun e => hg (Nat.eq_of_beq_eq_true e)
        rw [this]

theorem red_key {G0 G1 PAR GEN KS : Nat} (htb : tbOK G0 G1 PAR GEN KS = true) {k : Nat}
    (hk : k < 2880) : Red (key48 KS k) := by
  have h : tbAt G0 G1 PAR GEN KS k = true := CFSG.KC.Pack.allN_spec htb k hk
  unfold tbAt at h
  by_cases h0 : k = 0
  · subst h0
    simp only [Nat.beq_refl] at h
    rw [Nat.eq_of_beq_eq_true h]
    exact ⟨by decide, red_id4K⟩
  · have hb : Nat.beq k 0 = false := Bool.eq_false_iff.mpr fun e => h0 (Nat.eq_of_beq_eq_true e)
    rw [hb] at h
    simp only at h
    obtain ⟨-, h2⟩ := andOf h
    obtain ⟨-, h3⟩ := andOf h2
    exact red_mul4K_key KS k (Nat.eq_of_beq_eq_true h3)

theorem key_injOn {SK RHO KS : Nat} (hs : sortOK SK RHO KS = true) :
    Set.InjOn (key48 KS) (Finset.range 2880 : Set Nat) := by
  classical
  have hat : ∀ i < 2880, sortAt SK RHO KS i = true := CFSG.KC.Pack.allN_spec hs
  have hsucc : ∀ i, i + 1 < 2880 → key48 SK i < key48 SK (i + 1) := by
    intro i hi
    have h := hat i (by omega)
    unfold sortAt at h
    obtain ⟨h1, -⟩ := andOf h
    have hb : Nat.blt (Nat.succ i) 2880 = true := Nat.blt_eq.mpr hi
    rw [hb] at h1
    exact Nat.blt_eq.mp h1
  have hmono : ∀ i j, i < j → j < 2880 → key48 SK i < key48 SK j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact lt_trans (ih h (by omega)) (hsucc j hj)
      · exact hsucc i hj
  have hSinj : Set.InjOn (key48 SK) (Finset.range 2880 : Set Nat) := by
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd e (ne_of_lt (hmono i j h hj))
    · exact absurd e (ne_of_gt (hmono j i h hi))
  have hsub : (Finset.range 2880).image (key48 SK) ⊆ (Finset.range 2880).image (key48 KS) := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
    have h := hat i (Finset.mem_range.1 hi)
    unfold sortAt at h
    obtain ⟨-, h2⟩ := andOf h
    obtain ⟨h2, h3⟩ := andOf h2
    exact Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.blt_eq.mp h2), Nat.eq_of_beq_eq_true h3⟩
  have hc1 := Finset.card_image_of_injOn hSinj
  have hc2 := Finset.card_le_card hsub
  have hc3 := Finset.card_image_le (s := Finset.range 2880) (f := key48 KS)
  rw [hc1] at hc2
  exact Finset.card_image_iff.1 (le_antisymm hc3 hc2)

theorem tb_nodup {G0 G1 PAR GEN KS SK RHO : Nat} (hA : fiveArr4 lyFiveAbar = dec G0)
    (hB : fiveArr4 lyFiveBbar = dec G1) (hI : fiveArr4 1 = dec id4K)
    (hP : lyFiveParArr = CFSG.KS.Raw.unpack 2880 12 PAR)
    (hG : lyFiveGenArr = CFSG.KS.Raw.unpack 2880 12 GEN)
    (htb : tbOK G0 G1 PAR GEN KS = true) (hs : sortOK SK RHO KS = true) :
    lyFiveTbArr.toList.Nodup := by
  have hsz : lyFiveTbArr.size = 2880 := fold_push _ 2880
  have hget := tbArr_eq hA hB hI hP hG htb 2880 le_rfl
  have hinj := key_injOn hs
  rw [List.nodup_iff_injective_get]
  intro a b e
  have ha : a.val < 2880 := by simpa [hsz] using a.isLt
  have hb : b.val < 2880 := by simpa [hsz] using b.isLt
  simp only [Array.getElem_toList, List.get_eq_getElem] at e
  rw [← getElem!_pos _ _ (by simpa using a.isLt), ← getElem!_pos _ _ (by simpa using b.isLt)] at e
  have e1 : lyFiveTbArr[a.val]! = dec (key48 KS a.val) := hget a.val ha
  have e2 : lyFiveTbArr[b.val]! = dec (key48 KS b.val) := hget b.val hb
  rw [e1, e2] at e
  have := hinj (by simpa using ha) (by simpa using hb)
    (dec_inj (red_key htb ha) (red_key htb hb) e)
  exact Fin.ext this

end CFSG.KS.LyFiveTb

end
