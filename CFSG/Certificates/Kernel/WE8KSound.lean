module

public import Certificates.Data.Kernel.WE8K.Tab
public import CFSG.RankThree.Chevalley.SteinbergBIWE8Orbit
public import CFSG.RankThree.Chevalley.SteinbergBIWE8Enum
public import CFSG.Certificates.Kernel.Fi22LH.Lanes

public section

namespace CFSG.KC.WE8K

open CFSG.KC.Loop CFSG.LieType.Chevalley.WE8.Native CFSG.RankThree.Chevalley.WeylE8
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


def ConjOK (P N D M : ℕ) : Prop :=
  ∀ j (hj : j < 8) (w : W8), conjK P N D M j (keyI (code w)) = keyI (conjI j (code w))

theorem strictL_eq (y : ℕ) (k : ℕ → List ℕ) : strictL y k = k y := by
  cases y <;> rfl

theorem mem_kidsK (P N D M x m : ℕ) (acc : List ℕ) : ∀ n, ∀ y ∈ (Nat.rec (motive := fun _ => List ℕ)
    acc (fun j ih => Bool.rec (motive := fun _ => List ℕ) ih
      (strictL (conjK P N D M j x) fun y => y :: ih) (Nat.beq (fld(m, j, 1)) 1)) n : List ℕ),
    y ∈ acc ∨ ∃ j < n, y = conjK P N D M j x
  | 0 => fun y hy => Or.inl hy
  | n + 1 => by
    intro y
    have ih := mem_kidsK P N D M x m acc n
    revert ih
    change (∀ y ∈ _, _) → y ∈ Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq (fld(m, n, 1)) 1) → _
    cases Nat.beq (fld(m, n, 1)) 1
    · intro ih hy
      exact (ih y hy).imp_right fun ⟨j, hj, e⟩ => ⟨j, by omega, e⟩
    · intro ih hy
      change y ∈ strictL (conjK P N D M n x) (fun y => y :: _) at hy
      rw [strictL_eq, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Or.inr ⟨n, by omega, rfl⟩
      · exact (ih y hy).imp_right fun ⟨j, hj, e⟩ => ⟨j, by omega, e⟩

theorem mem_nextK (P N D M : ℕ) : ∀ (L : List ℕ) (m : ℕ), ∀ y ∈ nextK P N D M L m,
    ∃ x ∈ L, ∃ j < 8, y = conjK P N D M j x
  | [], _, y, hy => absurd hy List.not_mem_nil
  | x :: L, m, y, hy => by
    change y ∈ kidsK P N D M x (Nat.land m 255) (nextK P N D M L (Nat.shiftRight m 8)) at hy
    rcases mem_kidsK P N D M x (Nat.land m 255) _ 8 y hy with hy | ⟨j, hj, e⟩
    · obtain ⟨x', hx', j, hj, e⟩ := mem_nextK P N D M L _ y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', j, hj, e⟩
    · exact ⟨x, List.mem_cons_self .., j, hj, e⟩

theorem appK_eq : ∀ L R : List ℕ, appK L R = L ++ R
  | [], _ => rfl
  | x :: L, R => congrArg (x :: ·) (appK_eq L R)

theorem mem_orbK {P N D M : ℕ} (h : ConjOK P N D M) (t : W8) : ∀ (Ms L : List ℕ),
    (∀ x ∈ L, ∃ u : W8, IsConj t u ∧ x = keyI (code u)) →
    ∀ y ∈ orbK P N D M Ms L, ∃ u : W8, IsConj t u ∧ y = keyI (code u)
  | [], _, hL => hL
  | m :: Ms, L, hL => by
    intro y hy
    change y ∈ appK L (orbK P N D M Ms (nextK P N D M L m)) at hy
    rw [appK_eq, List.mem_append] at hy
    rcases hy with hy | hy
    · exact hL y hy
    · refine mem_orbK h t Ms _ (fun x hx => ?_) y hy
      obtain ⟨x', hx', j, hj, rfl⟩ := mem_nextK P N D M L m x hx
      obtain ⟨u, hu, rfl⟩ := hL x' hx'
      refine ⟨_, hu.trans (isConj_conj_simple ⟨j, hj⟩ u), ?_⟩
      rw [h j hj, code_conj' hj]

theorem mergeK_cons_nil (x : ℕ) (xs : List ℕ) : mergeK (x :: xs) [] = x :: mergeK xs [] := rfl

theorem mergeK_cons_cons (x y : ℕ) (xs ys : List ℕ) : mergeK (x :: xs) (y :: ys) =
    Bool.rec (motive := fun _ => List ℕ) (x :: mergeK xs (y :: ys)) (y :: mergeK (x :: xs) ys)
      (Nat.blt y x) := rfl

theorem mem_mergeK : ∀ (xs ys : List ℕ), ∀ z ∈ mergeK xs ys, z ∈ xs ∨ z ∈ ys
  | [], _, _, hz => Or.inr hz
  | x :: xs, [], z, hz => by
    rw [mergeK_cons_nil, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Or.inl (List.mem_cons_self ..)
    · exact Or.inl (List.mem_cons_of_mem _ ((mem_mergeK xs [] z hz).resolve_right
        List.not_mem_nil))
  | x :: xs, y :: ys, z, hz => by
    rw [mergeK_cons_cons] at hz
    revert hz
    cases Nat.blt y x
    · intro hz
      change z ∈ x :: mergeK xs (y :: ys) at hz
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl (List.mem_cons_self ..)
      · exact (mem_mergeK xs (y :: ys) z hz).imp_left (List.mem_cons_of_mem _)
    · intro hz
      change z ∈ y :: mergeK (x :: xs) ys at hz
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inr (List.mem_cons_self ..)
      · exact (mem_mergeK (x :: xs) ys z hz).imp_right (List.mem_cons_of_mem _)

theorem mem_pairsK_aux : ∀ (ls : List (List ℕ)) (hd : List ℕ) (b : Bool),
    ∀ r ∈ (List.rec (motive := fun _ => List ℕ → Bool → List (List ℕ))
      (fun h b => Bool.rec (motive := fun _ => List (List ℕ)) [] [h] b)
      (fun l _ ih h b => Bool.rec (motive := fun _ => List (List ℕ)) (ih l true)
        (mergeK h l :: ih [] false) b) ls hd b : List (List ℕ)),
    ∀ y ∈ r, y ∈ hd ∨ ∃ l ∈ ls, y ∈ l
  | [], hd, false, r, hr, _, _ => absurd hr List.not_mem_nil
  | [], hd, true, r, hr, y, hy => by
    change r ∈ [hd] at hr
    rw [List.mem_singleton] at hr
    exact Or.inl (hr ▸ hy)
  | l :: ls, hd, false, r, hr, y, hy => by
    rcases mem_pairsK_aux ls l true r hr y hy with hy | ⟨l', hl', hy⟩
    · exact Or.inr ⟨l, List.mem_cons_self .., hy⟩
    · exact Or.inr ⟨l', List.mem_cons_of_mem _ hl', hy⟩
  | l :: ls, hd, true, r, hr, y, hy => by
    change r ∈ mergeK hd l :: _ at hr
    rw [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact (mem_mergeK hd l y hy).imp_right fun hy => ⟨l, List.mem_cons_self .., hy⟩
    · rcases mem_pairsK_aux ls [] false r hr y hy with hy | ⟨l', hl', hy⟩
      · exact absurd hy List.not_mem_nil
      · exact Or.inr ⟨l', List.mem_cons_of_mem _ hl', hy⟩

theorem mem_pairsK (ls : List (List ℕ)) : ∀ r ∈ pairsK ls, ∀ y ∈ r, ∃ l ∈ ls, y ∈ l :=
  fun r hr y hy => (mem_pairsK_aux ls [] false r hr y hy).resolve_left List.not_mem_nil

theorem mem_singlesK : ∀ (L : List ℕ), ∀ r ∈ singlesK L, ∀ y ∈ r, y ∈ L
  | [], _, hr, _, _ => absurd hr List.not_mem_nil
  | x :: L, r, hr, y, hy => by
    change r ∈ [x] :: singlesK L at hr
    rw [List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [List.mem_singleton.1 hy]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_singlesK L r hr y hy)

theorem mem_sortK (L : List ℕ) : ∀ y ∈ sortK L, y ∈ L := by
  have key : ∀ k (ls : List (List ℕ)), (∀ r ∈ ls, ∀ y ∈ r, y ∈ L) →
      ∀ r ∈ (Nat.rec (motive := fun _ => List (List ℕ) → List (List ℕ)) (fun ls => ls)
        (fun _ ih ls => ih (pairsK ls)) k ls : List (List ℕ)), ∀ y ∈ r, y ∈ L := by
    intro k
    induction k with
    | zero => exact fun ls h => h
    | succ k ih =>
      intro ls h
      refine ih (pairsK ls) fun r hr y hy => ?_
      obtain ⟨l, hl, hy⟩ := mem_pairsK ls r hr y hy
      exact h l hl y hy
  intro y hy
  have hall := key 18 (singlesK L) (mem_singlesK L)
  revert hy
  change y ∈ headK _ → _
  generalize (Nat.rec (motive := fun _ => List (List ℕ) → List (List ℕ)) (fun ls => ls)
    (fun _ ih ls => ih (pairsK ls)) 18 (singlesK L) : List (List ℕ)) = ls at hall
  cases ls with
  | nil => exact fun hy => absurd hy List.not_mem_nil
  | cons l ls => exact fun hy => hall l (List.mem_cons_self ..) y hy

theorem strictLen_spec : ∀ (L : List ℕ) (lo c : ℕ), strictLen L lo c = 0 ∨
    (strictLen L lo c = c + L.length ∧ L.Pairwise (· < ·) ∧ ∀ x ∈ L, lo ≤ x)
  | [], _, c => Or.inr ⟨rfl, List.Pairwise.nil, fun _ hx => absurd hx List.not_mem_nil⟩
  | x :: L, lo, c => by
    have hc : strictLen (x :: L) lo c =
        Bool.rec (motive := fun _ => ℕ) 0 (strictLen L (x + 1) (c + 1)) (Nat.ble lo x) := rfl
    rw [hc]
    cases hb : Nat.ble lo x
    · exact Or.inl rfl
    · change strictLen L (x + 1) (c + 1) = 0 ∨ (strictLen L (x + 1) (c + 1) = _ ∧ _)
      rcases strictLen_spec L (x + 1) (c + 1) with h0 | ⟨h1, h2, h3⟩
      · exact Or.inl h0
      · refine Or.inr ⟨by rw [h1, List.length_cons]; omega,
          List.pairwise_cons.2 ⟨fun y hy => by have := h3 y hy; omega, h2⟩, fun y hy => ?_⟩
        have hlo := Nat.le_of_ble_eq_true hb
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hlo
        · have := h3 y hy
          omega

theorem orbOK_le_of {P N D M : ℕ} (h : ConjOK P N D M) (t : W8) {Ms : List ℕ} {n : ℕ}
    (ho : orbOK P N D M (keyI (code t)) Ms n = true) : n ≤ Nat.card {u : W8 // IsConj t u} := by
  classical
  have hn : strictLen (sortK (orbK P N D M Ms [keyI (code t)])) 0 0 = n := Nat.eq_of_beq_eq_true ho
  set S := sortK (orbK P N D M Ms [keyI (code t)])
  have hS : ∀ y ∈ S, ∃ u : W8, IsConj t u ∧ y = keyI (code u) := fun y hy =>
    mem_orbK h t Ms [keyI (code t)] (fun x hx => ⟨t, IsConj.refl t, List.mem_singleton.1 hx⟩) y
      (mem_sortK _ y hy)
  rcases strictLen_spec S 0 0 with h0 | ⟨h1, h2, -⟩
  · rw [← hn, h0]
    exact Nat.zero_le _
  have hnd : S.Nodup := h2.imp fun hab => Nat.ne_of_lt hab
  let f : S.toFinset → {u : W8 // IsConj t u} := fun y =>
    ⟨(hS y.1 (List.mem_toFinset.1 y.2)).choose, (hS y.1 (List.mem_toFinset.1 y.2)).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have ha := (hS a.1 (List.mem_toFinset.1 a.2)).choose_spec.2
    have hb := (hS b.1 (List.mem_toFinset.1 b.2)).choose_spec.2
    have e : (hS a.1 (List.mem_toFinset.1 a.2)).choose = (hS b.1 (List.mem_toFinset.1 b.2)).choose :=
      congrArg Subtype.val hab
    exact Subtype.ext (by rw [ha, hb, e])
  calc n = S.toFinset.card := by rw [List.toFinset_card_of_nodup hnd, ← hn, h1, Nat.zero_add]
    _ = Nat.card S.toFinset := (Nat.card_eq_finsetCard _).symm
    _ ≤ _ := Nat.card_le_card_of_injective f hf

theorem keyI_cons (a : ℕ) (l : List ℕ) : keyI (a :: l) = keyI l * 256 + a := rfl

theorem keyI_inj : ∀ l₁ l₂ : List ℕ, l₁.length = l₂.length → (∀ c ∈ l₁, c < 256) →
    (∀ c ∈ l₂, c < 256) → keyI l₁ = keyI l₂ → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _, _ => absurd hl (by simp)
  | a :: l₁, b :: l₂, hl, h₁, h₂, he => by
    rw [keyI_cons, keyI_cons] at he
    have ha := h₁ a (List.mem_cons_self ..)
    have hb := h₂ b (List.mem_cons_self ..)
    have hab : a = b := by omega
    have hk : keyI l₁ = keyI l₂ := by omega
    rw [hab, keyI_inj l₁ l₂ (by simpa using hl) (fun c hc => h₁ c (List.mem_cons_of_mem _ hc))
      (fun c hc => h₂ c (List.mem_cons_of_mem _ hc)) hk]

theorem code_lt (w : W8) : ∀ c ∈ code w, c < 256 := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
  have := rootIdx_lt (isRoot_col w i)
  omega

theorem keyI_code_inj {a b : W8} (h : keyI (code a) = keyI (code b)) : a = b :=
  code_injective (keyI_inj _ _ (by rw [length_code, length_code]) (code_lt a) (code_lt b) h)

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem walkK_keyI {P N D M : ℕ} (h : ConjOK P N D M) : ∀ (w : List ℕ), lt8K w = true →
    ∀ v : W8, ∃ g : W8, walkK P N D M w (keyI (code v)) = keyI (code (g * v * g⁻¹))
  | [], _, v => ⟨1, by
      change keyI (code v) = _
      rw [one_mul, inv_one, mul_one]⟩
  | j :: w, hw, v => by
    change Bool.rec (motive := fun _ => Bool) false (lt8K w) (Nat.blt j 8) = true at hw
    cases hj : Nat.blt j 8
    · rw [hj] at hw
      exact Bool.noConfusion hw
    rw [hj] at hw
    have hj8 : j < 8 := Nat.blt_eq.mp hj
    obtain ⟨g, hg⟩ := walkK_keyI h w hw (simple .E8 ⟨j, hj8⟩ * v * simple .E8 ⟨j, hj8⟩)
    refine ⟨g * simple .E8 ⟨j, hj8⟩, ?_⟩
    change strictN (conjK P N D M j (keyI (code v))) (walkK P N D M w) = _
    rw [strictN_eq, h j hj8, code_conj' hj8, hg, mul_inv_rev,
      (coxeterSystem .E8).inv_simple]
    congr 2
    group

theorem recAnd_spec (g : ℕ → Bool) : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun k ih => bAnd(g k, ih)) n = true → ∀ k < n, g k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(g k, ih)) n) (g n) = true at h
    cases hg : g n
    · rw [hg] at h
      exact Bool.noConfusion h
    · rw [hg] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact recAnd_spec g n h k hk
      · exact hg

theorem all8_spec {f : ℕ → Bool} (h : all8 f = true) : ∀ k < 8, f k = true := recAnd_spec f 8 h

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi) :
    ∀ i < m, f i = true := by
  intro i him
  have h1 := recAnd_spec (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
    bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) hi h
    (i / 64) (by omega)
  have h2 := recAnd_spec (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  change Bool.rec (motive := fun _ => Bool) true (f (Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64)))
    (Nat.blt (Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64)) m) = true at h2
  rw [e, Nat.blt_eq.mpr him] at h2
  exact h2

theorem byteAt_eq (x i : ℕ) : byteAt x i = x / 256 ^ i % 256 := by
  change (x >>> (i <<< 3)) &&& (2 ^ 8 - 1) = _
  have e : 2 ^ (i * 2 ^ 3) = 256 ^ i := by
    rw [pow_mul']
    norm_num
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, e]

theorem keyI_ofFn_byte : ∀ n x, x < 256 ^ n →
    keyI (List.ofFn fun i : Fin n => x / 256 ^ (i : ℕ) % 256) = x
  | 0, x, hx => by
    rw [pow_zero, Nat.lt_one_iff] at hx
    rw [hx]
    rfl
  | n + 1, x, hx => by
    rw [List.ofFn_succ, keyI_cons]
    have e : (fun i : Fin n => x / 256 ^ ((i.succ : Fin (n + 1)) : ℕ) % 256) =
        fun i : Fin n => x / 256 / 256 ^ (i : ℕ) % 256 :=
      funext fun i => by rw [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
    have hlt : x / 256 < 256 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]
      exact hx
    rw [e, keyI_ofFn_byte n (x / 256) hlt, show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl, pow_zero,
      Nat.div_one]
    exact Nat.div_add_mod' x 256

theorem start_key {S : List ℕ} (h : startsOK S = true) {k : ℕ} (hk : k < 10) :
    nthN S k = keyI (List.ofFn fun i : Fin 8 => rootIdx (startCol k i)) := by
  have hf := allBelow_spec h (by norm_num) k hk
  change (fun x => bAnd(Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 64)),
      all8 fun i => (fun c => bAnd(Nat.blt c (nat_lit 240),
        (rootsL ()).getD c [] == startCol k i)) (byteAt x i))) (nthN S k) = true at hf
  generalize nthN S k = x at hf ⊢
  change Bool.rec (motive := fun _ => Bool) false (all8 fun i => (fun c => bAnd(Nat.blt c 240,
    (rootsL ()).getD c [] == startCol k i)) (byteAt x i)) (Nat.blt x (Nat.shiftLeft 1 64)) = true at hf
  cases hx : Nat.blt x (Nat.shiftLeft 1 64)
  · rw [hx] at hf
    exact Bool.noConfusion hf
  rw [hx] at hf
  have hx64 : x < 256 ^ 8 := by
    have := Nat.blt_eq.mp hx
    change x < 1 <<< 64 at this
    rw [Nat.shiftLeft_eq] at this
    simpa using this
  have hcol : ∀ i < 8, rootIdx (startCol k i) = byteAt x i := by
    intro i hi
    have hb := all8_spec hf i hi
    change Bool.rec (motive := fun _ => Bool) false ((rootsL ()).getD (byteAt x i) [] == startCol k i)
      (Nat.blt (byteAt x i) 240) = true at hb
    cases hc : Nat.blt (byteAt x i) 240
    · rw [hc] at hb
      exact Bool.noConfusion hb
    rw [hc] at hb
    have hlt : byteAt x i < rootsL.length := by
      rw [length_rootsL]
      exact Nat.blt_eq.mp hc
    rw [← beq_iff_eq.mp hb, rootIdx, List.getD_eq_getElem _ _ hlt]
    exact List.Nodup.idxOf_getElem nodup_rootsL _ _
  have ef : (fun i : Fin 8 => rootIdx (startCol k i)) = fun i : Fin 8 => x / 256 ^ (i : ℕ) % 256 :=
    funext fun i => by rw [hcol i i.2, byteAt_eq]
  rw [ef]
  exact (keyI_ofFn_byte 8 x hx64).symm

theorem startsOK_spec {S : List ℕ} (h : startsOK S = true) :
    (∀ k < 9, nthN S k = keyI (frameCode ((frameData ()).getD k []))) ∧
      nthN S 9 = keyI (wordCode y0Word) := by
  refine ⟨fun k hk => ?_, start_key h (by norm_num)⟩
  rw [start_key h (by omega)]
  have e : ∀ i : ℕ, startCol k i = ((frameData ()).getD k []).foldr rRefl (basisV i) := by
    intro i
    unfold startCol
    rw [Nat.blt_eq.mpr hk]
  simp only [e]
  rfl

theorem bAnd_spec {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact Bool.noConfusion h
  · exact ⟨rfl, h⟩

theorem nthN_eq : ∀ (ls : List ℕ) (k : ℕ), nthN ls k = ls.getD k 0
  | [], _ => by simp [nthN]
  | _ :: _, 0 => rfl
  | l :: ls, k + 1 => by
    change nthN ls k = _
    rw [nthN_eq ls k, List.getD_cons_succ]

theorem dg_eq (c k : ℕ) : dg c k = c / 16 ^ k % 16 := by
  change (c >>> (k <<< 2)) &&& (2 ^ 4 - 1) = _
  have e : 2 ^ (k * 2 ^ 2) = 16 ^ k := by
    rw [pow_mul']
    norm_num
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, e]

theorem length_rootCodes : (rootCodes ()).length = 240 := by
  have := length_rootsL
  rwa [rootsL, List.length_map] at this

theorem rootsL_getD {a : ℕ} (ha : a < 240) : rootsL.getD a [] =
    List.ofFn fun k : Fin 8 => ((dg ((rootCodes ()).getD a 0) k : ℕ) : ℤ) - 8 := by
  have hl : a < (rootCodes ()).length := by rw [length_rootCodes]; exact ha
  rw [rootsL, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map,
    CFSG.LieType.Chevalley.WE8.Native.decodeVec, List.getD_eq_getElem _ _ hl]
  simp only [dg_eq]

theorem rt_spec {T M : ℕ} (h : rtOK T M = true) {a : ℕ} (ha : a < 240) {i : ℕ} (hi : i < 8) :
    dgT T a i = dg ((rootCodes ()).getD a 0) i := by
  have h1 := allBelow_spec h (by norm_num) a ha
  unfold rtF at h1
  beta_reduce at h1
  have h2 := (bAnd_spec (all8_spec h1 i hi)).1
  rw [← nthN_eq]
  exact Nat.eq_of_beq_eq_true h2

theorem getD_ofFn8 (f : Fin 8 → ℤ) (k : Fin 8) : (List.ofFn f).getD k 0 = f k := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]

theorem rootIdx_getD {b : ℕ} (hb : b < 240) : rootIdx (rootsL.getD b []) = b := by
  have hlt : b < rootsL.length := by rw [length_rootsL]; exact hb
  rw [rootIdx, List.getD_eq_getElem _ _ hlt]
  exact List.Nodup.idxOf_getElem nodup_rootsL _ _

theorem negP_spec {T P N D M : ℕ} (h : tabOK T P N D M = true) {a : ℕ} (ha : a < 240) :
    byteAt N a = negT.getD a 0 := by
  simp only [tabOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hrt, -⟩, -⟩, hN⟩, -⟩ := h
  have h1 := allBelow_spec hN (by norm_num) a ha
  beta_reduce at h1
  obtain ⟨hb, hk⟩ := bAnd_spec h1
  have hb' : byteAt N a < 240 := Nat.blt_eq.mp hb
  rw [negT_getD ha]
  have e : vneg (rootsL.getD a []) = rootsL.getD (byteAt N a) [] := by
    rw [rootsL_getD ha, rootsL_getD hb', vneg]
    refine congrArg List.ofFn (funext fun k => ?_)
    rw [getD_ofFn8]
    have h16 : dgT T (byteAt N a) k + dgT T a k = 16 := Nat.eq_of_beq_eq_true (all8_spec hk k k.2)
    rw [rt_spec hrt hb' k.2, rt_spec hrt ha k.2] at h16
    omega
  rw [e, rootIdx_getD hb']

theorem keyI_ofFn_sum : ∀ (n : ℕ) (g : ℕ → ℕ),
    keyI (List.ofFn fun i : Fin n => g i) = ∑ i ∈ Finset.range n, g i * 256 ^ i
  | 0, _ => rfl
  | n + 1, g => by
    rw [List.ofFn_succ, keyI_cons]
    have e : (List.ofFn fun i : Fin n => g ((i.succ : Fin (n + 1)) : ℕ)) =
        List.ofFn fun i : Fin n => (fun j => g (j + 1)) i := by
      simp only [Fin.val_succ]
    rw [e, keyI_ofFn_sum n (fun j => g (j + 1)), Finset.sum_range_succ', Finset.sum_mul]
    simp only [Fin.val_zero, pow_zero, mul_one, pow_succ, mul_assoc]

theorem byteRec_eq (f : ℕ → ℕ) (hf : ∀ i, f i < 256) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => Nat.lor (Nat.shiftLeft (f i) (Nat.shiftLeft i 3)) acc) n =
        ∑ i ∈ Finset.range n, f i * 256 ^ i ∧
      ∑ i ∈ Finset.range n, f i * 256 ^ i < 256 ^ n
  | 0 => ⟨rfl, by simp⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := byteRec_eq f hf n
    have e8 : (2 : ℕ) ^ (n <<< 3) = 256 ^ n := by
      rw [Nat.shiftLeft_eq, pow_mul']
      norm_num
    refine ⟨?_, ?_⟩
    · change f n <<< (n <<< 3) ||| Nat.rec (motive := fun _ => ℕ) 0
        (fun i acc => Nat.lor (Nat.shiftLeft (f i) (Nat.shiftLeft i 3)) acc) n = _
      rw [h1, ← Nat.shiftLeft_add_eq_or_of_lt (by rw [e8]; exact h2), Nat.shiftLeft_eq, e8,
        Finset.sum_range_succ, Nat.add_comm]
    · rw [Finset.sum_range_succ, pow_succ]
      have := hf n
      nlinarith

theorem byteAt_lt (x i : ℕ) : byteAt x i < 256 := by
  rw [byteAt_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem code_eq_bytes (w : W8) :
    code w = List.ofFn fun i : Fin 8 => byteAt (keyI (code w)) i := by
  have hx : keyI (code w) < 256 ^ 8 := by
    have e : code w = List.ofFn fun i : Fin 8 => (code w).getD i 0 := by
      refine List.ext_getElem (by rw [List.length_ofFn, length_code]) fun i h1 h2 => ?_
      rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h1]
    have hk := keyI_ofFn_sum 8 (fun j => (code w).getD j 0)
    rw [e, hk]
    have hb := byteRec_eq (fun i => (code w).getD i 0 % 256) (fun i => Nat.mod_lt _ (by norm_num)) 8
    have e2 : ∀ i ∈ Finset.range 8, (code w).getD i 0 * 256 ^ i =
        (code w).getD i 0 % 256 * 256 ^ i := fun i hi => by
      rw [Nat.mod_eq_of_lt (by
        have := getD_code_lt w ⟨i, Finset.mem_range.1 hi⟩
        simp only at this
        omega)]
    rw [Finset.sum_congr rfl e2]
    exact hb.2
  refine keyI_inj _ _ (by rw [length_code, List.length_ofFn]) (code_lt w) (fun c hc => ?_) ?_
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    exact byteAt_lt _ _
  · simp only [byteAt_eq]
    exact (keyI_ofFn_byte 8 _ hx).symm

theorem negK_keyI {T P N D M : ℕ} (h : tabOK T P N D M = true) (w : W8) :
    negK N (keyI (code w)) = keyI (negI (code w)) := by
  have hrec := (byteRec_eq (fun i => byteAt N (byteAt (keyI (code w)) i))
    (fun i => byteAt_lt _ _) 8).1
  change Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor (Nat.shiftLeft
    (byteAt N (byteAt (keyI (code w)) i)) (Nat.shiftLeft i 3)) acc) 8 = _
  have hk := keyI_ofFn_sum 8 (fun i => byteAt N (byteAt (keyI (code w)) i))
  rw [hrec, ← hk, negI]
  conv_rhs => rw [code_eq_bytes w]
  rw [List.map_ofFn]
  refine congrArg keyI (congrArg List.ofFn (funext fun i => ?_))
  simp only [Function.comp_apply]
  have hc : byteAt (keyI (code w)) i < 240 := by
    have e : (code w).getD i 0 = (List.ofFn fun i : Fin 8 => byteAt (keyI (code w)) i).getD i 0 :=
      congrArg (fun l => l.getD i 0) (code_eq_bytes w)
    rw [List.getD_eq_getElem (List.ofFn _) _ (by rw [List.length_ofFn]; exact i.2),
      List.getElem_ofFn] at e
    rw [← e]
    exact getD_code_lt w i
  exact negP_spec h hc

theorem sum8_eq (f : ℕ → ℕ) : sum8 f = ∑ k ∈ Finset.range 8, f k := by
  have key : ∀ n, Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => Nat.add (f k) ih) n =
      ∑ k ∈ Finset.range n, f k := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change f n + Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => Nat.add (f k) ih) n = _
      rw [ih, Finset.sum_range_succ, Nat.add_comm]
  exact key 8

theorem adjB_val : ∀ j < 8, ∀ k < 8, adjB adjC j k = if cart j k = -1 then 1 else 0 := by
  decide +kernel

theorem pair_digits {j : ℕ} (hj : j < 8) (d : ℕ → ℕ) :
    pair j (List.ofFn fun k : Fin 8 => ((d k : ℕ) : ℤ) - 8) =
      2 * ((d j : ℤ) - 8) - ∑ k ∈ Finset.range 8, ((adjB adjC j k : ℕ) : ℤ) * ((d k : ℤ) - 8) := by
  have e : ∀ k ∈ Finset.range 8, ((adjB adjC j k : ℕ) : ℤ) * ((d k : ℤ) - 8) =
      (if cart j k = -1 then 1 else 0) * ((d k : ℤ) - 8) := fun k hk => by
    rw [adjB_val j hj k (Finset.mem_range.1 hk)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e, pair, List.sum_ofFn]
  simp only [getD_ofFn8]
  rw [Fin.sum_univ_eq_sum_range (fun k => cart j k * ((d k : ℤ) - 8))]
  interval_cases j <;> simp [Finset.sum_range_succ, cart] <;> ring

theorem permP_spec {T P N D M : ℕ} (h : tabOK T P N D M = true) {j a : ℕ} (hj : j < 8)
    (ha : a < 240) : byteAt P (Nat.add (Nat.mul (nat_lit 240) j) a) < 240 ∧
      byteAt P (Nat.add (Nat.mul (nat_lit 240) j) a) = (permT.getD j #[]).getD a 0 := by
  simp only [tabOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hrt, hM⟩, hP⟩, -⟩, -⟩ := h
  have hM' : M = adjC := Nat.eq_of_beq_eq_true hM
  subst hM'
  have h1 := allBelow_spec (allBelow_spec hP (by norm_num) j hj) (by norm_num) a ha
  beta_reduce at h1
  obtain ⟨hb, hk⟩ := bAnd_spec h1
  set b := byteAt P (Nat.add (Nat.mul (nat_lit 240) j) a)
  have hb' : b < 240 := Nat.blt_eq.mp hb
  refine ⟨hb', ?_⟩
  have hr := allBelow_spec hrt (by norm_num) a ha
  unfold rtF at hr
  beta_reduce at hr
  have hpj := (bAnd_spec (bAnd_spec (all8_spec hr j hj)).2).2
  have hpj' : pT T a j + 16 + ∑ k ∈ Finset.range 8, adjB adjC j k * dgT T a k =
      2 * dgT T a j + 8 * ∑ k ∈ Finset.range 8, adjB adjC j k + 2 := by
    have := Nat.eq_of_beq_eq_true hpj
    rw [sum8_eq, sum8_eq] at this
    exact this
  have hsum : ∀ k ∈ Finset.range 8, adjB adjC j k * dgT T a k =
      adjB adjC j k * dg ((rootCodes ()).getD a 0) k := fun k hk => by
    rw [rt_spec hrt ha (Finset.mem_range.1 hk)]
  rw [Finset.sum_congr rfl hsum, rt_spec hrt ha hj] at hpj'
  rw [permT_getD ⟨j, hj⟩ ha]
  have e : sRefl j (rootsL.getD a []) = rootsL.getD b [] := by
    rw [rootsL_getD ha, rootsL_getD hb', sRefl]
    refine congrArg List.ofFn (funext fun k => ?_)
    have hkk := all8_spec hk k k.2
    rw [getD_ofFn8, pair_digits hj]
    by_cases hkj : (k : ℕ) = j
    · rw [if_pos hkj]
      rw [show Nat.beq k j = true from Nat.beq_eq_true_eq _ _ ▸ hkj] at hkk
      have h3 : dgT T b j + pT T a j = dgT T a j + 2 := Nat.eq_of_beq_eq_true hkk
      rw [rt_spec hrt hb' hj, rt_spec hrt ha hj] at h3
      rw [hkj]
      have hcast : (∑ k ∈ Finset.range 8, ((adjB adjC j k : ℕ) : ℤ) *
          ((dg ((rootCodes ()).getD a 0) k : ℤ) - 8)) =
          ((∑ k ∈ Finset.range 8, adjB adjC j k * dg ((rootCodes ()).getD a 0) k : ℕ) : ℤ) -
            8 * ((∑ k ∈ Finset.range 8, adjB adjC j k : ℕ) : ℤ) := by
        push_cast
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hcast]
      omega
    · rw [if_neg hkj]
      rw [show Nat.beq k j = false from Bool.eq_false_iff.2 fun h => hkj (Nat.eq_of_beq_eq_true h)] at hkk
      have h3 : dgT T b k = dgT T a k := Nat.eq_of_beq_eq_true hkk
      rw [rt_spec hrt hb' k.2, rt_spec hrt ha k.2] at h3
      rw [h3]
  have e' : ((⟨j, hj⟩ : Fin 8) : ℕ) = j := rfl
  rw [e', e, rootIdx_getD hb']

theorem l16_eq (x i : ℕ) : l16 x i = x / 2 ^ (16 * i) % 2 ^ 16 := by
  change (x >>> (i <<< 4)) &&& (2 ^ 16 - 1) = _
  have e : i <<< 4 = 16 * i := by
    rw [Nat.shiftLeft_eq]
    ring
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, e]

theorem fld112_eq (x : ℕ) : fld(x, nat_lit 112, nat_lit 0xFFFF) = x / 2 ^ 112 % 2 ^ 16 := by
  change (x >>> 112) &&& (2 ^ 16 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fld128_lt (x o : ℕ) :
    fld(x, o, nat_lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) < 2 ^ 128 := by
  change (x >>> o) &&& (2 ^ 128 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem sum_l16 {x : ℕ} (hx : x < 2 ^ 128) :
    x = ∑ i ∈ Finset.range 8, l16 x i * 2 ^ (16 * i) := by
  have key : ∀ n, x % 2 ^ (16 * n) = ∑ i ∈ Finset.range n, l16 x i * 2 ^ (16 * i) := by
    intro n
    induction n with
    | zero => simp only [Nat.mul_zero, pow_zero, Nat.mod_one, Finset.range_zero, Finset.sum_empty]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, l16_eq, Nat.mul_succ, pow_add, Nat.mod_mul]
      ring
  rw [← key 8]
  exact (Nat.mod_eq_of_lt hx).symm

theorem div_lane (l c h : ℕ) (hl : l < 2 ^ 112) (hc : c < 2 ^ 16) :
    (l + c * 2 ^ 112 + h * 2 ^ 128) / 2 ^ 112 % 2 ^ 16 = c := by
  omega

theorem lane7 {u v : ℕ} (x y : ℕ → ℕ) (hu : u = ∑ i ∈ Finset.range 8, x i * 2 ^ (16 * i))
    (hv : v = ∑ k ∈ Finset.range 8, y k * 2 ^ (16 * k)) (hx : ∀ i < 8, x i ≤ 15)
    (hy : ∀ k < 8, y k ≤ 4) :
    fld(Nat.mul u v, nat_lit 112, nat_lit 0xFFFF) = ∑ i ∈ Finset.range 8, x i * y (7 - i) := by
  subst hu hv
  rw [fld112_eq]
  have e : (∑ i ∈ Finset.range 8, x i * 2 ^ (16 * i)) * (∑ k ∈ Finset.range 8, y k * 2 ^ (16 * k)) =
      (x 0 * y 0 * 1 + x 0 * y 1 * 65536 + x 0 * y 2 * 4294967296 + x 0 * y 3 * 281474976710656 +
          x 0 * y 4 * 18446744073709551616 + x 0 * y 5 * 1208925819614629174706176 +
          x 0 * y 6 * 79228162514264337593543950336 + x 1 * y 0 * 65536 + x 1 * y 1 * 4294967296 +
          x 1 * y 2 * 281474976710656 + x 1 * y 3 * 18446744073709551616 +
          x 1 * y 4 * 1208925819614629174706176 + x 1 * y 5 * 79228162514264337593543950336 +
          x 2 * y 0 * 4294967296 + x 2 * y 1 * 281474976710656 + x 2 * y 2 * 18446744073709551616 +
          x 2 * y 3 * 1208925819614629174706176 + x 2 * y 4 * 79228162514264337593543950336 +
          x 3 * y 0 * 281474976710656 + x 3 * y 1 * 18446744073709551616 +
          x 3 * y 2 * 1208925819614629174706176 + x 3 * y 3 * 79228162514264337593543950336 +
          x 4 * y 0 * 18446744073709551616 + x 4 * y 1 * 1208925819614629174706176 +
          x 4 * y 2 * 79228162514264337593543950336 + x 5 * y 0 * 1208925819614629174706176 +
          x 5 * y 1 * 79228162514264337593543950336 + x 6 * y 0 * 79228162514264337593543950336) +
      (x 0 * y 7 + x 1 * y 6 + x 2 * y 5 + x 3 * y 4 + x 4 * y 3 + x 5 * y 2 + x 6 * y 1 +
          x 7 * y 0) * 2 ^ 112 +
      (x 1 * y 7 * 1 + x 2 * y 6 * 1 + x 2 * y 7 * 65536 + x 3 * y 5 * 1 + x 3 * y 6 * 65536 +
          x 3 * y 7 * 4294967296 + x 4 * y 4 * 1 + x 4 * y 5 * 65536 + x 4 * y 6 * 4294967296 +
          x 4 * y 7 * 281474976710656 + x 5 * y 3 * 1 + x 5 * y 4 * 65536 + x 5 * y 5 * 4294967296 +
          x 5 * y 6 * 281474976710656 + x 5 * y 7 * 18446744073709551616 + x 6 * y 2 * 1 +
          x 6 * y 3 * 65536 + x 6 * y 4 * 4294967296 + x 6 * y 5 * 281474976710656 +
          x 6 * y 6 * 18446744073709551616 + x 6 * y 7 * 1208925819614629174706176 + x 7 * y 1 * 1 +
          x 7 * y 2 * 65536 + x 7 * y 3 * 4294967296 + x 7 * y 4 * 281474976710656 +
          x 7 * y 5 * 18446744073709551616 + x 7 * y 6 * 1208925819614629174706176 +
          x 7 * y 7 * 79228162514264337593543950336) * 2 ^ 128 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have ec : ∑ i ∈ Finset.range 8, x i * y (7 - i) = x 0 * y 7 + x 1 * y 6 + x 2 * y 5 + x 3 * y 4 +
      x 4 * y 3 + x 5 * y 2 + x 6 * y 1 + x 7 * y 0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, zero_add]
  rw [Nat.mul_eq, e, ec]
  have b : ∀ i < 8, ∀ k < 8, x i * y k ≤ 60 := fun i hi k hk =>
    (Nat.mul_le_mul (hx i hi) (hy k hk)).trans (by norm_num)
  have b00 := b 0 (by norm_num) 0 (by norm_num)
  have b01 := b 0 (by norm_num) 1 (by norm_num)
  have b02 := b 0 (by norm_num) 2 (by norm_num)
  have b03 := b 0 (by norm_num) 3 (by norm_num)
  have b04 := b 0 (by norm_num) 4 (by norm_num)
  have b05 := b 0 (by norm_num) 5 (by norm_num)
  have b06 := b 0 (by norm_num) 6 (by norm_num)
  have b07 := b 0 (by norm_num) 7 (by norm_num)
  have b10 := b 1 (by norm_num) 0 (by norm_num)
  have b11 := b 1 (by norm_num) 1 (by norm_num)
  have b12 := b 1 (by norm_num) 2 (by norm_num)
  have b13 := b 1 (by norm_num) 3 (by norm_num)
  have b14 := b 1 (by norm_num) 4 (by norm_num)
  have b15 := b 1 (by norm_num) 5 (by norm_num)
  have b16 := b 1 (by norm_num) 6 (by norm_num)
  have b20 := b 2 (by norm_num) 0 (by norm_num)
  have b21 := b 2 (by norm_num) 1 (by norm_num)
  have b22 := b 2 (by norm_num) 2 (by norm_num)
  have b23 := b 2 (by norm_num) 3 (by norm_num)
  have b24 := b 2 (by norm_num) 4 (by norm_num)
  have b25 := b 2 (by norm_num) 5 (by norm_num)
  have b30 := b 3 (by norm_num) 0 (by norm_num)
  have b31 := b 3 (by norm_num) 1 (by norm_num)
  have b32 := b 3 (by norm_num) 2 (by norm_num)
  have b33 := b 3 (by norm_num) 3 (by norm_num)
  have b34 := b 3 (by norm_num) 4 (by norm_num)
  have b40 := b 4 (by norm_num) 0 (by norm_num)
  have b41 := b 4 (by norm_num) 1 (by norm_num)
  have b42 := b 4 (by norm_num) 2 (by norm_num)
  have b43 := b 4 (by norm_num) 3 (by norm_num)
  have b50 := b 5 (by norm_num) 0 (by norm_num)
  have b51 := b 5 (by norm_num) 1 (by norm_num)
  have b52 := b 5 (by norm_num) 2 (by norm_num)
  have b60 := b 6 (by norm_num) 0 (by norm_num)
  have b61 := b 6 (by norm_num) 1 (by norm_num)
  have b70 := b 7 (by norm_num) 0 (by norm_num)
  exact div_lane _ _ _ (by omega) (by omega)

theorem REP16_eq : REP16 = ∑ k ∈ Finset.range 8, (fun _ => 1) k * 2 ^ (16 * k) := by
  simp only [REP16, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem rtF_spec {T M : ℕ} (h : rtOK T M = true) {a : ℕ} (ha : a < 240) {i : ℕ} (hi : i < 8) :
    dgT T a i = dg ((rootCodes ()).getD a 0) i ∧ pT T a i ≤ 4 ∧
      pT T a i + 16 + ∑ k ∈ Finset.range 8, adjB M i k * dgT T a k =
        2 * dgT T a i + 8 * ∑ k ∈ Finset.range 8, adjB M i k + 2 := by
  have h1 := allBelow_spec h (by norm_num) a ha
  unfold rtF at h1
  beta_reduce at h1
  obtain ⟨h2, h3⟩ := bAnd_spec (all8_spec h1 i hi)
  obtain ⟨h4, h5⟩ := bAnd_spec h3
  refine ⟨?_, Nat.le_of_ble_eq_true h4, ?_⟩
  · rw [← nthN_eq]
    exact Nat.eq_of_beq_eq_true h2
  · have e := Nat.eq_of_beq_eq_true h5
    rw [sum8_eq, sum8_eq] at e
    exact e

theorem getD_ofFn8' (f : Fin 8 → ℤ) {i : ℕ} (hi : i < 8) : (List.ofFn f).getD i 0 = f ⟨i, hi⟩ :=
  getD_ofFn8 f ⟨i, hi⟩

theorem pair_root {T M : ℕ} (hrt : rtOK T M = true) (hM : M = adjC) {b : ℕ} (hb : b < 240) {i : ℕ}
    (hi : i < 8) : pair i (rootsL.getD b []) = (pT T b i : ℤ) - 2 := by
  subst hM
  obtain ⟨-, -, hp⟩ := rtF_spec hrt hb hi
  have hsum : ∀ k ∈ Finset.range 8, adjB adjC i k * dgT T b k =
      adjB adjC i k * dg ((rootCodes ()).getD b 0) k := fun k hk => by
    rw [rt_spec hrt hb (Finset.mem_range.1 hk)]
  rw [Finset.sum_congr rfl hsum, rt_spec hrt hb hi] at hp
  rw [rootsL_getD hb, pair_digits hi]
  have hcast : (∑ k ∈ Finset.range 8, ((adjB adjC i k : ℕ) : ℤ) *
      ((dg ((rootCodes ()).getD b 0) k : ℤ) - 8)) =
      ((∑ k ∈ Finset.range 8, adjB adjC i k * dg ((rootCodes ()).getD b 0) k : ℕ) : ℤ) -
        8 * ((∑ k ∈ Finset.range 8, adjB adjC i k : ℕ) : ℤ) := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hcast]
  omega

theorem dgT_le {T M : ℕ} (hrt : rtOK T M = true) {a : ℕ} (ha : a < 240) :
    ∀ i < 8, dgT T a i ≤ 15 := fun i hi => by
  rw [rt_spec hrt ha hi, dg_eq]
  omega

theorem l16_vA_le {T M : ℕ} (hrt : rtOK T M = true) {b : ℕ} (hb : b < 240) :
    ∀ k < 8, l16 (vA T b) k ≤ 4 := fun k hk => by
  have h4 := (rtF_spec hrt hb (i := 7 - k) (by omega)).2.1
  change l16 (vA T b) (7 - (7 - k)) ≤ 4 at h4
  rwa [Nat.sub_sub_self (by omega)] at h4

theorem dotT_eq {T M : ℕ} (hrt : rtOK T M = true) {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    dotT T a b = ∑ i ∈ Finset.range 8, dgT T a i * pT T b i :=
  lane7 (dgT T a) (fun k => l16 (vA T b) k) (sum_l16 (fld128_lt T _)) (sum_l16 (fld128_lt T _))
    (dgT_le hrt ha) (l16_vA_le hrt hb)

theorem sdT_eq {T M : ℕ} (hrt : rtOK T M = true) {a : ℕ} (ha : a < 240) :
    sdT T a = ∑ i ∈ Finset.range 8, dgT T a i := by
  have e := lane7 (dgT T a) (fun _ => 1) (sum_l16 (fld128_lt T _)) REP16_eq (dgT_le hrt ha)
    (fun _ _ => by norm_num)
  simp only [mul_one] at e
  exact e

theorem spT_eq {T M : ℕ} (hrt : rtOK T M = true) {b : ℕ} (hb : b < 240) :
    spT T b = ∑ i ∈ Finset.range 8, pT T b i := by
  have e := lane7 (fun k => l16 (vA T b) k) (fun _ => 1) (sum_l16 (fld128_lt T _)) REP16_eq
    (fun k hk => (l16_vA_le hrt hb k hk).trans (by norm_num)) (fun _ _ => by norm_num)
  simp only [mul_one] at e
  change spT T b = _ at e
  rw [e, ← Finset.sum_range_reflect (fun i => pT T b i) 8]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  change l16 (vA T b) k = l16 (vA T b) (7 - (8 - 1 - k))
  congr 1
  omega

theorem ip_eq {T M : ℕ} (hrt : rtOK T M = true) (hM' : M = adjC) {a b : ℕ} (ha : a < 240)
    (hb : b < 240) : ip (rootsL.getD a []) (rootsL.getD b []) =
      ∑ i ∈ Finset.range 8, ((dgT T a i : ℤ) - 8) * ((pT T b i : ℤ) - 2) := by
  rw [ip, List.sum_ofFn, Fin.sum_univ_eq_sum_range
    (fun i => (rootsL.getD a []).getD i 0 * pair i (rootsL.getD b [])) 8]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi8 := Finset.mem_range.1 hi
  rw [pair_root hrt hM' hb hi8, rootsL_getD ha, getD_ofFn8' _ hi8]
  beta_reduce
  rw [← rt_spec hrt ha hi8]

theorem ipIs_of_ip {T M : ℕ} (hrt : rtOK T M = true) (hM' : M = adjC) {a b : ℕ} (ha : a < 240)
    (hb : b < 240) (hip : ip (rootsL.getD a []) (rootsL.getD b []) = -1) :
    ipIs T a b (nat_lit 0) (nat_lit 1) = true := by
  have key : Nat.add (Nat.add (dotT T a b) (nat_lit 128)) (nat_lit 1) =
      Nat.add (Nat.add (Nat.mul (nat_lit 2) (sdT T a)) (Nat.mul (nat_lit 8) (spT T b))) (nat_lit 0) := by
    rw [dotT_eq hrt ha hb, sdT_eq hrt ha, spT_eq hrt hb]
    simp only [Nat.add_eq, Nat.mul_eq]
    rw [ip_eq hrt hM' ha hb] at hip
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hip ⊢
    push_cast at hip
    zify
    linarith
  unfold ipIs
  rw [key]
  exact Nat.beq_refl _

theorem tabDRow_of {T D : ℕ} (hD : allBelow 8 1 (tabDF T D) = true) {a : ℕ} (ha : a < 240) :
    tabDRow T D a = true := by
  have h0 : tabDF T D (a / 30) = true := allBelow_spec hD (by norm_num) (a / 30) (by omega)
  unfold tabDF at h0
  have h1 := allBelow_spec h0 (by norm_num) (a % 30) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h1
  have e : Nat.add (Nat.mul (nat_lit 30) (a / 30)) (a % 30) = a := Nat.div_add_mod a 30
  rwa [e] at h1

theorem tabD_cellG {T a : ℕ} {C : ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {BD : ℕ → ℕ} {DG : ℕ → ℕ → ℕ}
    {A8 : (ℕ → Bool) → Bool}
    (hrow : allBelow (nat_lit 240) (nat_lit 4) (fun b => bIf(C T a b (nat_lit 0) (nat_lit 1),
      (fun e => bAnd(Nat.blt e (nat_lit 240),
        A8 fun k => Nat.beq (Nat.add (DG e k) (nat_lit 8)) (Nat.add (DG a k) (DG b k))))
        (BD (Nat.add (Nat.mul (nat_lit 240) a) b)), true)) = true) {b : ℕ} (hb : b < 240)
    (hip : C T a b (nat_lit 0) (nat_lit 1) = true) :
    BD (Nat.add (Nat.mul (nat_lit 240) a) b) < 240 ∧
      A8 (fun k => Nat.beq (Nat.add (DG (BD (Nat.add (Nat.mul (nat_lit 240) a) b)) k)
        (nat_lit 8)) (Nat.add (DG a k) (DG b k))) = true := by
  have h1 := allBelow_spec hrow (by norm_num) b hb
  beta_reduce at h1
  rw [hip] at h1
  exact ⟨Nat.blt_eq.mp (bAnd_spec h1).1, (bAnd_spec h1).2⟩

theorem tabD_cell {T D a : ℕ} (hrow : tabDRow T D a = true) {b : ℕ} (hb : b < 240)
    (hip : ipIs T a b (nat_lit 0) (nat_lit 1) = true) :
    byteAt D (Nat.add (Nat.mul (nat_lit 240) a) b) < 240 ∧
      all8 (fun k => Nat.beq (Nat.add (dgT T (byteAt D (Nat.add (Nat.mul (nat_lit 240) a) b)) k)
        (nat_lit 8)) (Nat.add (dgT T a k) (dgT T b k))) = true :=
  tabD_cellG (C := ipIs) (BD := byteAt D) (DG := dgT T) (A8 := all8) hrow hb hip

theorem vadd_idx {T M a b E : ℕ} (hrt : rtOK T M = true) (ha : a < 240) (hb : b < 240)
    (he' : E < 240) (hk : all8 (fun k => Nat.beq (Nat.add (dgT T E k) (nat_lit 8))
      (Nat.add (dgT T a k) (dgT T b k))) = true) :
    E = rootIdx (vadd (rootsL.getD a []) (rootsL.getD b [])) := by
  have ev : vadd (rootsL.getD a []) (rootsL.getD b []) = rootsL.getD E [] := by
    rw [rootsL_getD ha, rootsL_getD hb, rootsL_getD he', vadd]
    refine congrArg List.ofFn (funext fun k => ?_)
    rw [getD_ofFn8, getD_ofFn8]
    have h8 : dgT T E k + 8 = dgT T a k + dgT T b k := Nat.eq_of_beq_eq_true (all8_spec hk k k.2)
    rw [rt_spec hrt he' k.2, rt_spec hrt ha k.2, rt_spec hrt hb k.2] at h8
    omega
  rw [ev, rootIdx_getD he']

theorem addP_spec {T P N D M : ℕ} (h : tabOK T P N D M = true) {a b : ℕ} (ha : a < 240)
    (hb : b < 240) (hip : ip (rootsL.getD a []) (rootsL.getD b []) = -1) :
    byteAt D (Nat.add (Nat.mul (nat_lit 240) a) b) < 240 ∧
      byteAt D (Nat.add (Nat.mul (nat_lit 240) a) b) = (addT.getD a #[]).getD b 0 := by
  simp only [tabOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hrt, hM⟩, -⟩, -⟩, hD⟩ := h
  have hM' : M = adjC := Nat.eq_of_beq_eq_true hM
  obtain ⟨he', hk⟩ := tabD_cell (tabDRow_of hD ha) hb (ipIs_of_ip hrt hM' ha hb hip)
  refine ⟨he', ?_⟩
  rw [addT_getD ha hb, hip]
  simp only [beq_self_eq_true, if_true]
  generalize byteAt D (Nat.add (Nat.mul (nat_lit 240) a) b) = E at he' hk ⊢
  exact vadd_idx hrt ha hb he' hk

theorem adjC_spec : ∀ j < 8, ∀ i < 8,
    (Nat.beq (fld(adjC, Nat.add (Nat.shiftLeft j (nat_lit 3)) i, nat_lit 1)) (nat_lit 1) = true ↔
      cart j i = -1) := by
  decide +kernel

theorem colK_lt (P N D M j cj x i : ℕ) : colK P N D M j cj x i < 256 := by
  unfold colK
  cases Nat.beq i j
  · cases Nat.beq (fld(M, Nat.add (Nat.shiftLeft j (nat_lit 3)) i, nat_lit 1)) (nat_lit 1)
    · exact byteAt_lt _ _
    · exact byteAt_lt _ _
  · exact byteAt_lt _ _

theorem conjK_keyI {T P N D M : ℕ} (h : tabOK T P N D M = true) {j : ℕ} (hj : j < 8) (w : W8) :
    conjK P N D M j (keyI (code w)) = keyI (conjI j (code w)) := by
  have hM : M = adjC := by
    have h' := h
    simp only [tabOK, Bool.and_eq_true] at h'
    exact Nat.eq_of_beq_eq_true h'.1.1.1.2
  have hcx : ∀ i : Fin 8, byteAt (keyI (code w)) i = (code w).getD i 0 := fun i => by
    have e : (code w).getD i 0 = (List.ofFn fun i : Fin 8 => byteAt (keyI (code w)) i).getD i 0 :=
      congrArg (fun l => l.getD i 0) (code_eq_bytes w)
    rw [List.getD_eq_getElem (List.ofFn _) _ (by rw [List.length_ofFn]; exact i.2),
      List.getElem_ofFn] at e
    exact e.symm
  change strictN (byteAt (keyI (code w)) j) (fun cj => Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor (Nat.shiftLeft (colK P N D M j cj (keyI (code w)) i)
      (Nat.shiftLeft i 3)) acc) 8) = _
  rw [strictN_eq, (byteRec_eq _ (fun i => colK_lt P N D M j _ (keyI (code w)) i) 8).1, conjI,
    keyI_ofFn_sum 8 (fun i => if i = j then negT.getD ((permT.getD j #[]).getD ((code w).getD j 0) 0) 0
      else if cart j i = -1 then
        (permT.getD j #[]).getD ((addT.getD ((code w).getD i 0) #[]).getD ((code w).getD j 0) 0) 0
      else (permT.getD j #[]).getD ((code w).getD i 0) 0)]
  refine Finset.sum_congr rfl fun i hi => congrArg (· * 256 ^ i) ?_
  have hi8 : i < 8 := Finset.mem_range.1 hi
  have hcj : byteAt (keyI (code w)) j = (code w).getD j 0 := hcx ⟨j, hj⟩
  have hci : byteAt (keyI (code w)) i = (code w).getD i 0 := hcx ⟨i, hi8⟩
  have hlj : (code w).getD j 0 < 240 := getD_code_lt w ⟨j, hj⟩
  have hli : (code w).getD i 0 < 240 := getD_code_lt w ⟨i, hi8⟩
  unfold colK
  rw [hcj, hci]
  cases hb : Nat.beq i j
  · have hij : i ≠ j := Nat.ne_of_beq_eq_false hb
    rw [if_neg hij]
    cases hm : Nat.beq (fld(M, Nat.add (Nat.shiftLeft j (nat_lit 3)) i, nat_lit 1)) (nat_lit 1)
    · have hc : ¬ cart j i = -1 := fun hc => by
        rw [hM, (adjC_spec j hj i hi8).2 hc] at hm
        exact Bool.noConfusion hm
      rw [if_neg hc]
      exact (permP_spec h hj hli).2
    · have hc : cart j i = -1 := (adjC_spec j hj i hi8).1 (by rw [← hM]; exact hm)
      rw [if_pos hc]
      have hip : ip (rootsL.getD ((code w).getD i 0) []) (rootsL.getD ((code w).getD j 0) []) =
          -1 := by
        have e := cart_eq ⟨j, hj⟩ ⟨i, hi8⟩
        change cart j i = _ at e
        rw [hc] at e
        have hc0 := col_code w ⟨i, hi8⟩
        have hc1 := col_code w ⟨j, hj⟩
        change rootsL.getD ((code w).getD i 0) [] = _ at hc0
        change rootsL.getD ((code w).getD j 0) [] = _ at hc1
        rw [hc0, hc1, ip_toL, iform_smul, iform_eb, cartan_symm, ← e]
      obtain ⟨hd, hd'⟩ := addP_spec h hli hlj hip
      rw [hd']
      rw [hd'] at hd
      exact (permP_spec h hj hd).2
  · have hij : i = j := Nat.eq_of_beq_eq_true hb
    subst hij
    rw [if_pos rfl]
    obtain ⟨hp, hp'⟩ := permP_spec h hj hlj
    change byteAt N (byteAt P (Nat.add (Nat.mul (nat_lit 240) i) ((code w).getD i 0))) = _
    rw [negP_spec h hp, hp']

theorem orbOK_le {T P N D M : ℕ} (h : tabOK T P N D M = true) (t : W8) {Ms : List ℕ} {n : ℕ}
    (ho : orbOK P N D M (keyI (code t)) Ms n = true) : n ≤ Nat.card {u : W8 // IsConj t u} :=
  orbOK_le_of (fun j hj w => conjK_keyI h hj w) t ho

theorem zwOK_isConj {T P N D M : ℕ} (h : tabOK T P N D M = true) {z : W8}
    (hz : ∀ v : L8, z • v = -v) (t u : W8) {w : List ℕ}
    (hw : zwOK P N D M (keyI (code t)) w (keyI (code u)) = true) : IsConj u (z * t) := by
  change Bool.rec (motive := fun _ => Bool) false
    (Nat.beq (walkK P N D M w (negK N (keyI (code t)))) (keyI (code u))) (lt8K w) = true at hw
  cases hl : lt8K w
  · rw [hl] at hw
    exact Bool.noConfusion hw
  rw [hl] at hw
  have he := Nat.eq_of_beq_eq_true hw
  rw [negK_keyI h, ← code_neg hz] at he
  obtain ⟨g, hg⟩ := walkK_keyI (fun j hj w => conjK_keyI h hj w) w hl (z * t)
  rw [hg] at he
  exact (isConj_iff.2 ⟨g, keyI_code_inj he⟩).symm

theorem foldBits_add (g : ℕ → ℕ) : ∀ (d x base acc : ℕ), x < 2 ^ 2 ^ d →
    foldBits (fun b acc => Nat.add acc (g b)) d x base acc =
      acc + ∑ i ∈ Finset.range (2 ^ d), if x.testBit i then g (base + i) else 0
  | 0, x, base, acc, hx => by
    change Bool.rec (motive := fun _ => ℕ) (Nat.add acc (g base)) acc (Nat.beq x 0) = _
    have h2 : (2 : ℕ) ^ 2 ^ 0 = 2 := by norm_num
    rw [h2] at hx
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with h | rfl
    · obtain rfl : x = 0 := by omega
      have h00 : Nat.beq 0 0 = true := rfl
      rw [h00]
      simp
    · have h10 : Nat.beq 1 0 = false := rfl
      rw [h10]
      simp [Nat.add_eq]
  | d + 1, x, base, acc, hx => by
    change Bool.rec (motive := fun _ => ℕ) (strictN (foldBits (fun b acc => Nat.add acc (g b)) d
        (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 d)) 1)) base acc)
      fun a => foldBits (fun b acc => Nat.add acc (g b)) d (Nat.shiftRight x (Nat.shiftLeft 1 d))
        (Nat.add base (Nat.shiftLeft 1 d)) a) acc (Nat.beq x 0) = _
    have hw : Nat.shiftLeft 1 d = 2 ^ d := by
      change 1 <<< d = _
      rw [Nat.shiftLeft_eq, one_mul]
    have hm : Nat.land x (Nat.sub (Nat.shiftLeft 1 (2 ^ d)) 1) = x % 2 ^ 2 ^ d := by
      change x &&& ((1 <<< 2 ^ d) - 1) = _
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.and_two_pow_sub_one_eq_mod x _
    rw [hw, hm]
    cases hx0 : Nat.beq x 0
    · have hx0' : x ≠ 0 := Nat.ne_of_beq_eq_false hx0
      change strictN _ _ = _
      have hlo : x % 2 ^ 2 ^ d < 2 ^ 2 ^ d := Nat.mod_lt _ (by positivity)
      have hhi : Nat.shiftRight x (2 ^ d) < 2 ^ 2 ^ d := by
        change x >>> 2 ^ d < _
        rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
          ← two_mul, ← pow_succ']
        exact hx
      rw [strictN_eq, foldBits_add g d _ _ _ hhi, foldBits_add g d _ _ _ hlo, pow_succ, mul_two,
        Finset.sum_range_add, Nat.add_eq]
      have e1 : ∀ i ∈ Finset.range (2 ^ d), (if (x % 2 ^ 2 ^ d).testBit i then g (base + i) else 0) =
          if x.testBit i then g (base + i) else 0 := fun i hi => by
        rw [Nat.testBit_mod_two_pow]
        have : i < 2 ^ d := Finset.mem_range.1 hi
        simp [this]
      have e2 : ∀ i ∈ Finset.range (2 ^ d),
          (if (Nat.shiftRight x (2 ^ d)).testBit i then g (base + 2 ^ d + i) else 0) =
          if x.testBit (2 ^ d + i) then g (base + (2 ^ d + i)) else 0 := fun i _ => by
        change (if (x >>> 2 ^ d).testBit i then _ else 0) = _
        rw [Nat.testBit_shiftRight, Nat.add_assoc]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
      ring
    · have hx0' : x = 0 := Nat.eq_of_beq_eq_true hx0
      subst hx0'
      simp

theorem land_mask64_lt (y : ℕ) : Nat.land y (nat_lit 0xFFFFFFFFFFFFFFFF) < 2 ^ 64 := by
  change y &&& (2 ^ 64 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem segK_xor_and (X R S n : ℕ) (hS : S < 2 ^ 64) :
    segK (Nat.xor (Nat.land X R) S) n = Nat.land (segK X n) (segK R n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((((X &&& R) ^^^ S) >>> (64 + 240 * n)) &&& (2 ^ 240 - 1)).testBit i =
    (((X >>> (64 + 240 * n)) &&& (2 ^ 240 - 1)) &&& ((R >>> (64 + 240 * n)) &&& (2 ^ 240 - 1))).testBit i
  have hs : S.testBit (64 + 240 * n + i) = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor, hs, Bool.xor_false]
  cases X.testBit (64 + 240 * n + i) <;> cases R.testBit (64 + 240 * n + i) <;> simp

theorem segK_cutK (X R n : ℕ) : segK (cutK X R) n = Nat.land (segK X n) (segK R n) :=
  segK_xor_and X R _ n (land_mask64_lt _)

open CFSG.KS.Fi22LH (lanes lanes_succ lanes_lt lanes_split lanes_trunc pair_bits pair_mask
  pair_addShift lanes_mul_ones psum psum_le)

theorem sum_pairs8 (f : ℕ → ℕ) : ∀ n,
    ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) = ∑ j ∈ Finset.range (2 * n), f j
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_pairs8 f n, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_assoc]

theorem psum_eq8 (f : ℕ → ℕ) (j : ℕ) : ∀ m, m ≤ j + 1 →
    psum f m j = ∑ t ∈ Finset.range m, f (j - t)
  | 0, _ => rfl
  | m + 1, hm => by
    rw [psum, psum_eq8 f j m (by omega), if_pos (by omega), Finset.sum_range_succ]

theorem lanes_top8 {w : ℕ} {f : ℕ → ℕ} {n : ℕ} (hf : ∀ i < n + 1, f i < 2 ^ w) :
    lanes w f (n + 1) / 2 ^ (w * n) = f n := by
  rw [lanes_succ, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (lanes_lt n fun i hi => hf i (by omega)), Nat.add_zero]

theorem pop240_gen {x m1 m2 m4 o : ℕ} (hx : x < 2 ^ 240)
    (h1 : m1 = lanes 2 (fun _ => 1) 120) (h2 : m2 = lanes (2 * 2) (fun _ => 2 ^ 2 - 1) 60)
    (h4 : m4 = lanes (2 * 4) (fun _ => 2 ^ 4 - 1) 30) (ho : o = lanes 8 (fun _ => 1) 30) :
    (fun a => (fun b => (fun c => ((c * o) >>> 232) &&& 255) ((b + (b >>> 4)) &&& m4))
      ((a &&& m2) + ((a >>> 2) &&& m2))) (x - ((x >>> 1) &&& m1)) =
      ∑ i ∈ Finset.range 240, (x.testBit i).toNat := by
  subst h1 h2 h4 ho
  beta_reduce
  have ha : x - ((x >>> 1) &&& lanes 2 (fun _ => 1) 120) =
      lanes 2 (fun j => (x.testBit (2 * j)).toNat + (x.testBit (2 * j + 1)).toNat) (2 * 60) :=
    pair_bits (n := 120) hx
  rw [ha]
  set g1 : ℕ → ℕ := fun j => (x.testBit (2 * j)).toNat + (x.testBit (2 * j + 1)).toNat with hg1d
  have hg1 : ∀ i, g1 i ≤ 2 := fun i => by
    simp only [hg1d]
    cases x.testBit (2 * i) <;> cases x.testBit (2 * i + 1) <;> decide
  rw [pair_mask (w := 2) (n := 60) (by norm_num) fun i _ => by have := hg1 i; omega]
  set g2 : ℕ → ℕ := fun j => g1 (2 * j) + g1 (2 * j + 1) with hg2d
  have hg2 : ∀ i, g2 i ≤ 4 := fun i => by
    have := hg1 (2 * i)
    have := hg1 (2 * i + 1)
    simp only [hg2d]
    omega
  rw [show (2 * 2 : ℕ) = 4 from rfl, show (60 : ℕ) = 2 * 30 from rfl,
    pair_addShift (w := 4) (n := 30) (by norm_num) fun i _ => by
      have := hg2 i
      have := hg2 (i + 1)
      split <;> omega]
  set g3 : ℕ → ℕ := fun j => g2 (2 * j) + g2 (2 * j + 1) with hg3d
  have hg3 : ∀ i, g3 i ≤ 8 := fun i => by
    have := hg2 (2 * i)
    have := hg2 (2 * i + 1)
    simp only [hg3d]
    omega
  have hm := lanes_mul_ones (w := 8) (n := 30) hg3 (by norm_num) 30 le_rfl
  rw [show (2 * 4 : ℕ) = 8 from rfl, Nat.shiftRight_eq_div_pow,
    show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    ← Nat.mod_mul_right_div_self, ← pow_add, show 232 + 8 = 8 * 30 from rfl, hm,
    show (232 : ℕ) = 8 * 29 from rfl, lanes_top8 fun i _ =>
      Nat.lt_of_le_of_lt (psum_le hg3 30 i) (by norm_num), psum_eq8 g3 29 30 le_rfl]
  rw [Finset.sum_range_reflect g3 30]
  simp only [hg3d, hg2d, hg1d]
  rw [sum_pairs8 (fun j => g2 j) 30]
  simp only [hg2d]
  rw [sum_pairs8 (fun j => g1 j) 60]
  simp only [hg1d]
  rw [sum_pairs8 (fun j => (x.testBit j).toNat) 120]

theorem pop240_eq {x : ℕ} (hx : x < 2 ^ 240) :
    pop240 x = ∑ i ∈ Finset.range 240, (x.testBit i).toNat :=
  pop240_gen (m1 := 0x555555555555555555555555555555555555555555555555555555555555)
    (m2 := 0x333333333333333333333333333333333333333333333333333333333333)
    (m4 := 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)
    (o := 0x010101010101010101010101010101010101010101010101010101010101) hx
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem setK_bits (f : ℕ → Bool) (a : ℕ) : (setK f).testBit a = (decide (a < 240) && f a) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => ℕ) 0
      (fun a ih => nIf(f a, Nat.lor ih (Nat.shiftLeft 1 a), ih)) n).testBit a =
        (decide (a < n) && f a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      change (nIf(f n, Nat.lor (Nat.rec (motive := fun _ => ℕ) 0
        (fun a ih => nIf(f a, Nat.lor ih (Nat.shiftLeft 1 a), ih)) n) (Nat.shiftLeft 1 n),
        Nat.rec (motive := fun _ => ℕ) 0
          (fun a ih => nIf(f a, Nat.lor ih (Nat.shiftLeft 1 a), ih)) n)).testBit a = _
      generalize Nat.rec (motive := fun _ => ℕ) 0
        (fun a ih => nIf(f a, Nat.lor ih (Nat.shiftLeft 1 a), ih)) n = R at ih ⊢
      cases hfn : f n
      · change R.testBit a = _
        rw [ih]
        rcases lt_trichotomy a n with h | rfl | h
        · simp [h, show a < n + 1 by omega]
        · simp [hfn]
        · simp [show ¬ a < n by omega, show ¬ a < n + 1 by omega]
      · change (R ||| 1 <<< n).testBit a = _
        rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
        rcases lt_trichotomy a n with h | rfl | h
        · simp [h, show a < n + 1 by omega, show n ≠ a by omega]
        · simp [hfn]
        · simp [show ¬ a < n by omega, show ¬ a < n + 1 by omega, show n ≠ a by omega]
  exact key 240

theorem lanes_eq_sum (w : ℕ) (c : ℕ → ℕ) : ∀ N, lanes w c N = ∑ i ∈ Finset.range N, 2 ^ (w * i) * c i
  | 0 => rfl
  | N + 1 => by rw [lanes_succ, lanes_eq_sum w c N, Finset.sum_range_succ]

theorem lanes_digit {w : ℕ} {c : ℕ → ℕ} {N t : ℕ} (hc : ∀ i < N, c i < 2 ^ w) (ht : t < N) :
    lanes w c N / 2 ^ (w * t) % 2 ^ w = c t := by
  obtain ⟨k, rfl⟩ : ∃ k, N = t + (1 + k) := ⟨N - t - 1, by omega⟩
  rw [lanes_split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (lanes_lt t fun i hi => hc i (by omega)), Nat.zero_add]
  have := lanes_trunc (w := w) (g := fun i => c (t + i)) (n := 1) (fun i hi => hc _ (by omega)) k
  rw [Nat.mul_one] at this
  rw [this]
  simp [lanes]

theorem sum_five (F : ℕ → ℕ) : ∀ N,
    ∑ n ∈ Finset.range N, ∑ v ∈ Finset.range 5, F (5 * n + v) = ∑ t ∈ Finset.range (5 * N), F t
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_five F N, show 5 * (N + 1) = 5 * N + 5 by ring,
      Finset.sum_range_add]

theorem selT_eq (T : ℕ) :
    selT T = lanes 240 (fun t => setK fun a => Nat.beq (pT T a (t / 5)) (t % 5)) 40 := by
  have inner : ∀ n m, Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun v ih => Nat.add
      (Nat.shiftLeft (setK fun a => Nat.beq (pT T a n) v)
        (Nat.mul (nat_lit 240) (Nat.add (Nat.mul (nat_lit 5) n) v))) ih) m =
      ∑ v ∈ Finset.range m, 2 ^ (240 * (5 * n + v)) * setK (fun a => Nat.beq (pT T a n) v) := by
    intro n m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      change (setK fun a => Nat.beq (pT T a n) m) <<< (240 * (5 * n + m)) + _ = _
      rw [Nat.shiftLeft_eq]
      ring
  unfold selT
  rw [sum8_eq, lanes_eq_sum, show (40 : ℕ) = 5 * 8 from rfl, ← sum_five]
  refine Finset.sum_congr rfl fun n _ => ?_
  refine (inner n 5).trans (Finset.sum_congr rfl fun v hv => ?_)
  have hv5 := Finset.mem_range.1 hv
  rw [show (5 * n + v) / 5 = n by omega, show (5 * n + v) % 5 = v by omega]

theorem setK_lt (f : ℕ → Bool) : setK f < 2 ^ 240 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by rw [setK_bits]; simp [show ¬ i < 240 by omega]

theorem fld240 (S o : ℕ) : fld(S, o, ones240) = S / 2 ^ o % 2 ^ 240 := by
  change (S >>> o) &&& ((1 <<< 240) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem sel_bits (T : ℕ) {m v : ℕ} (hm : m < 8) (hv : v ≤ 4) (a : ℕ) :
    (selK (selT T) m v).testBit a = (decide (a < 240) && Nat.beq (pT T a m) v) := by
  have hb : Nat.ble v 4 = true := by
    rw [Nat.ble_eq]
    exact hv
  unfold selK
  rw [hb]
  change (fld(selT T, Nat.mul (nat_lit 240) (Nat.add (Nat.mul (nat_lit 5) m) v), ones240)).testBit a = _
  rw [fld240, selT_eq, show Nat.mul (nat_lit 240) (Nat.add (Nat.mul (nat_lit 5) m) v) =
    240 * (5 * m + v) from rfl,
    lanes_digit (t := 5 * m + v) (N := 40) (fun i _ => setK_lt _) (by omega), setK_bits,
    show (5 * m + v) / 5 = m by omega, show (5 * m + v) % 5 = v by omega]

def okC (sgn : ℤ) (pre : List ℕ) (n' a : ℕ) : Bool :=
  ((pairT.getD a #[]).getD n' 0 == sgn * (pairT.getD a #[]).getD n' 0) &&
    okFrom sgn a n' (pairT.getD a #[]) 0 pre

def rowC (sgn : ℤ) (m b n' a : ℕ) : Bool :=
  ((ipT.getD b #[]).getD a 0 == cart m n' &&
    (pairT.getD a #[]).getD m 0 == sgn * (pairT.getD b #[]).getD n' 0)

theorem okFrom_append (sgn : ℤ) (a n : ℕ) (pa : Array ℤ) : ∀ (l₁ l₂ : List ℕ) (j : ℕ),
    okFrom sgn a n pa j (l₁ ++ l₂) =
      (okFrom sgn a n pa j l₁ && okFrom sgn a n pa (j + l₁.length) l₂)
  | [], l₂, j => by simp [okFrom]
  | b :: l₁, l₂, j => by
    rw [List.cons_append, okFrom, okFrom, okFrom_append sgn a n pa l₁ l₂ (j + 1),
      List.length_cons, show j + 1 + l₁.length = j + (l₁.length + 1) by omega]
    simp only [Bool.and_assoc]

theorem okC_append (sgn : ℤ) (pre : List ℕ) (b n' a : ℕ) :
    okC sgn (pre ++ [b]) n' a = (okC sgn pre n' a && rowC sgn pre.length b n' a) := by
  unfold okC rowC
  rw [okFrom_append, Nat.zero_add]
  simp only [okFrom, Bool.and_true, Bool.and_assoc]

def extN (sgn : ℤ) : ℕ → List ℕ → List (List ℕ)
  | 0, pre => [pre]
  | k + 1, pre => (extend sgn pre).flatMap (extN sgn k)

theorem extN_flatMap (sgn : ℤ) : ∀ (k : ℕ) (pre : List ℕ),
    (extN sgn k pre).flatMap (extend sgn) = extN sgn (k + 1) pre
  | 0, pre => by simp [extN]
  | k + 1, pre => by
    rw [extN, List.flatMap_assoc]
    simp only [extN_flatMap sgn k]
    rfl

theorem enum_eq_extN (sgn : ℤ) : ∀ n, enum sgn n = extN sgn n []
  | 0 => rfl
  | n + 1 => by rw [enum, enum_eq_extN sgn n, extN_flatMap]

theorem sum_filter_range (p : ℕ → Bool) (g : ℕ → ℕ) : ∀ N,
    (((List.range N).filter p).map g).sum = ∑ a ∈ Finset.range N, if p a then g a else 0
  | 0 => rfl
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      sum_filter_range p g N, Finset.sum_range_succ]
    cases h : p N <;> simp [h]

theorem extN_length_succ (sgn : ℤ) (k : ℕ) (pre : List ℕ) :
    (extN sgn (k + 1) pre).length = ∑ a ∈ Finset.range 240,
      if okC sgn pre pre.length a then (extN sgn k (pre ++ [a])).length else 0 := by
  rw [extN, List.length_flatMap, extend]
  simp only [List.map_map, Function.comp_def]
  exact sum_filter_range (okC sgn pre pre.length) (fun a => (extN sgn k (pre ++ [a])).length) 240

def SegOK (X n : ℕ) (p : ℕ → Bool) : Prop :=
  ∀ a, (segK X n).testBit a = (decide (a < 240) && p a)

theorem segK_lt (X n : ℕ) : segK X n < 2 ^ 240 := by
  change (X >>> (64 + 240 * n)) &&& ((1 <<< 240) - 1) < _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem segK_land (X Y n : ℕ) : segK (Nat.land X Y) n = Nat.land (segK X n) (segK Y n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (((X &&& Y) >>> (64 + 240 * n)) &&& ((1 <<< 240) - 1)).testBit i =
    (((X >>> (64 + 240 * n)) &&& ((1 <<< 240) - 1)) &&&
      ((Y >>> (64 + 240 * n)) &&& ((1 <<< 240) - 1))).testBit i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight]
  cases X.testBit (64 + 240 * n + i) <;> cases Y.testBit (64 + 240 * n + i) <;> simp

def RowOK (sgn : ℤ) (Q m : ℕ) : Prop :=
  ∀ b < 240, ∀ n', m < n' → n' < 8 → SegOK (fld(Q, Nat.mul (nat_lit 1984) b,
    Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1984)) (nat_lit 1))) n' (rowC sgn m b n')

theorem cut_seg {sgn : ℤ} {X R m b n' : ℕ} {pre : List ℕ} (hX : SegOK X n' (okC sgn pre n'))
    (hR : SegOK R n' (rowC sgn m b n')) (hpre : pre.length = m) :
    SegOK (cutK X R) n' (okC sgn (pre ++ [b]) n') := by
  intro a
  rw [segK_cutK]
  change ((segK X n') &&& (segK R n')).testBit a = _
  rw [Nat.testBit_and, hX a, hR a, okC_append, hpre]
  cases decide (a < 240) <;> cases okC sgn pre n' a <;> cases rowC sgn m b n' a <;> rfl

theorem sum256 (G : ℕ → ℕ) (c : ℕ → Bool) (hc : ∀ i, 240 ≤ i → c i = false) :
    ∑ i ∈ Finset.range (2 ^ 8), (if c i then G i else 0) =
      ∑ i ∈ Finset.range 240, (if c i then G i else 0) := by
  rw [show 2 ^ 8 = 240 + 16 from rfl, Finset.sum_range_add]
  have h0 : ∑ i ∈ Finset.range 16, (if c (240 + i) then G (240 + i) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hc _ (by omega)]; rfl
  rw [h0, Nat.add_zero]

theorem dfs_spec (sgn : ℤ) : ∀ (L : List ℕ) (m : ℕ) (pre : List ℕ) (X : ℕ) (r : ℕ → Bool),
    m + L.length = 7 → pre.length = m → (∀ i (hi : i < L.length), RowOK sgn L[i] (m + i)) →
    SegOK X m (fun a => okC sgn pre m a && r a) →
    (∀ n', m < n' → n' < 8 → SegOK X n' (okC sgn pre n')) →
    dfsK L m X = ∑ a ∈ Finset.range 240,
      if (okC sgn pre m a && r a) then (extN sgn (7 - m) (pre ++ [a])).length else 0
  | [], m, pre, X, r, hm, _, _, hX, _ => by
    obtain rfl : m = 7 := by simpa using hm
    change pop240 (segK X 7) = _
    rw [pop240_eq (segK_lt X 7)]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hX a, decide_eq_true (Finset.mem_range.1 ha), Bool.true_and]
    beta_reduce
    cases okC sgn pre 7 a && r a <;> rfl
  | Q :: L, m, pre, X, r, hm, hpre, hrow, hX, hX' => by
    simp only [List.length_cons] at hm
    have e : dfsK (Q :: L) m X = foldBits (fun b acc => Nat.add acc (dfsK L (m + 1)
        (cutK X (fld(Q, Nat.mul (nat_lit 1984) b,
          Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1984)) (nat_lit 1)))))) 8 (segK X m) 0 0 :=
      rfl
    have hlt : segK X m < 2 ^ 2 ^ 8 := lt_of_lt_of_le (segK_lt X m) (by norm_num)
    rw [e, foldBits_add _ 8 _ 0 0 hlt, Nat.zero_add, sum256]
    · refine Finset.sum_congr rfl fun b hb => ?_
      have hb' := Finset.mem_range.1 hb
      have hXb : (segK X m).testBit b = (okC sgn pre m b && r b) := by
        rw [hX b]
        simp [hb']
      rw [hXb, Nat.zero_add]
      cases hc : (okC sgn pre m b && r b)
      · rfl
      rw [if_pos rfl, if_pos rfl]
      have hrowQ : RowOK sgn Q m := hrow 0 (by simp)
      refine (dfs_spec sgn L (m + 1) (pre ++ [b]) _ (fun _ => true) (by omega) (by simp [hpre])
        (fun i hi => ?_) (fun a => ?_) (fun n' h1 h2 => ?_)).trans ?_
      · have := hrow (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
      · beta_reduce
        rw [cut_seg (hX' (m + 1) (by omega) (by omega)) (hrowQ b hb' (m + 1) (by omega) (by omega))
          hpre a, Bool.and_true]
      · exact cut_seg (hX' n' (by omega) h2) (hrowQ b hb' n' (by omega) h2) hpre
      · rw [show 7 - m = (7 - (m + 1)) + 1 by omega, extN_length_succ]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Bool.and_true, List.length_append, List.length_singleton, hpre]
    · intro i hi
      rw [hX i]
      simp
      omega

set_option exponentiation.threshold 2048 in
theorem segK_mask {lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ 240) {n : ℕ} (hn : n < 8) (a : ℕ) :
    (segK ((1 <<< 1984) - 1 - (((1 <<< 240) - 1) <<< 64) + ((1 <<< hi) - (1 <<< lo)) <<< 64)
      n).testBit a =
      (decide (a < 240) && (n != 0 || (decide (lo ≤ a) && decide (a < hi)))) := by
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hQP : 2 ^ lo ≤ 2 ^ hi := Nat.pow_le_pow_right (by norm_num) hlo
  have hP : 2 ^ hi ≤ 2 ^ 240 := Nat.pow_le_pow_right (by norm_num) hhi
  have hQ : 1 ≤ 2 ^ lo := Nat.one_le_two_pow
  have hPQ : 2 ^ hi - 2 ^ lo < 2 ^ 240 := by omega
  have hpow : (2 : ℕ) ^ 1984 = 2 ^ 1680 * 2 ^ 240 * 2 ^ 64 := by rw [← pow_add, ← pow_add]
  rw [hpow]
  have hY : 2 ^ 1680 * 2 ^ 240 * 2 ^ 64 - 1 - (2 ^ 240 - 1) * 2 ^ 64 + (2 ^ hi - 2 ^ lo) * 2 ^ 64 =
      2 ^ 64 * (2 ^ 240 * (2 ^ 1680 - 1) + (2 ^ hi - 2 ^ lo)) + (2 ^ 64 - 1) := by
    have hF : 0 < (2 : ℕ) ^ 1680 := by positivity
    generalize (2 : ℕ) ^ 1680 = F at hF ⊢
    generalize (2 : ℕ) ^ hi = P at hQP hP hPQ ⊢
    generalize (2 : ℕ) ^ lo = Q at hQP hQ hPQ ⊢
    norm_num at hP hPQ ⊢
    omega
  change ((_ >>> (64 + 240 * n)) &&& ((1 <<< 240) - 1)).testBit a = _
  rw [hY, Nat.testBit_and, Nat.testBit_shiftRight, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_mul_add _ (Nat.sub_lt (by positivity) one_pos), if_neg (by omega),
    show 64 + 240 * n + a - 64 = 240 * n + a by omega, Nat.testBit_two_pow_mul_add _ hPQ]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have e : 2 ^ hi - 2 ^ lo = (2 ^ (hi - lo) - 1) <<< lo := by
      rw [Nat.shiftLeft_eq, Nat.sub_mul, ← pow_add, Nat.sub_add_cancel hlo, one_mul]
    by_cases ha : a < 240
    · rw [if_pos (by omega), Nat.mul_zero, Nat.zero_add, e, Nat.testBit_shiftLeft,
        Nat.testBit_two_pow_sub_one]
      by_cases h1 : lo ≤ a <;> by_cases h2 : a < hi <;> simp [h1, h2, ha] <;> omega
    · simp [ha]
  · rw [if_neg (by omega), Nat.testBit_two_pow_sub_one]
    by_cases ha : a < 240
    · rw [decide_eq_true (show 240 * n + a - 240 < 1680 by omega)]
      simp [ha, show n ≠ 0 by omega]
    · simp [ha]

theorem chunk_spec {sgn : ℤ} {Qs : List ℕ} {X lo hi : ℕ} (hlen : Qs.length = 7)
    (hrow : ∀ i (hi : i < Qs.length), RowOK sgn Qs[i] i)
    (hX : ∀ n' < 8, SegOK X n' (okC sgn [] n')) (hlo : lo ≤ hi) (hhi : hi ≤ 240) :
    chunkK Qs X lo hi = ∑ a ∈ Finset.range 240,
      if (okC sgn [] 0 a && (decide (lo ≤ a) && decide (a < hi))) then
        (extN sgn 7 [a]).length else 0 := by
  change dfsK Qs 0 (Nat.land X ((1 <<< 1984) - 1 - (((1 <<< 240) - 1) <<< 64) +
    ((1 <<< hi) - (1 <<< lo)) <<< 64)) = _
  refine dfs_spec sgn Qs 0 [] _ (fun a => decide (lo ≤ a) && decide (a < hi)) (by omega) rfl
    (fun i hi => by simpa using hrow i hi) (fun a => ?_) (fun n' h1 h2 a => ?_)
  · rw [segK_land]
    change ((segK X 0) &&& _).testBit a = _
    rw [Nat.testBit_and, hX 0 (by omega) a, segK_mask hlo hhi (by omega) a]
    cases decide (a < 240) <;> simp
  · rw [segK_land]
    change ((segK X n') &&& _).testBit a = _
    rw [Nat.testBit_and, hX n' h2 a, segK_mask hlo hhi h2 a]
    cases decide (a < 240) <;> simp [show n' ≠ 0 by omega]

theorem byte_mono {B n : ℕ} (hB : ∀ k < n, byteAt B k < byteAt B (k + 1)) :
    ∀ j k, j ≤ k → k ≤ n → byteAt B j ≤ byteAt B k := by
  intro j k hjk hkn
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact le_trans (ih (by omega)) (le_of_lt (hB k (by omega)))

theorem sum_ite_range {lo hi : ℕ} (hhi : hi ≤ 240) (G : ℕ → ℕ) :
    ∑ a ∈ Finset.range 240, (if (decide (lo ≤ a) && decide (a < hi)) then G a else 0) =
      ∑ a ∈ Finset.Ico lo hi, G a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem chunks_sum (G : ℕ → ℕ) {B n : ℕ} (h0 : byteAt B 0 = 0) (hn : byteAt B n = 240)
    (hB : ∀ k < n, byteAt B k < byteAt B (k + 1)) :
    ∑ k ∈ Finset.range n, ∑ a ∈ Finset.range 240,
      (if (decide (byteAt B k ≤ a) && decide (a < byteAt B (k + 1))) then G a else 0) =
      ∑ a ∈ Finset.range 240, G a := by
  have hle : ∀ k ≤ n, byteAt B k ≤ 240 := fun k hk => hn ▸ byte_mono hB k n hk le_rfl
  have key : ∀ k ≤ n, ∑ j ∈ Finset.range k, ∑ a ∈ Finset.Ico (byteAt B j) (byteAt B (j + 1)), G a =
      ∑ a ∈ Finset.Ico (byteAt B 0) (byteAt B k), G a := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega), Finset.sum_Ico_consecutive _
        (byte_mono hB 0 k (by omega) (by omega)) (le_of_lt (hB k (by omega)))]
  rw [Finset.sum_congr rfl fun k hk => sum_ite_range (hle (k + 1) (by
    have := Finset.mem_range.1 hk; omega)) G, key n le_rfl, h0, hn, Finset.range_eq_Ico]

theorem listRec_and_spec {α : Type} (G : α → ℕ → Bool) : ∀ (L : List α) (k : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun Q _ ih n => bAnd(G Q n, ih (Nat.succ n))) L k = true →
    ∀ i (hi : i < L.length), G L[i] (k + i) = true
  | [], _, _, i, hi => absurd hi (by simp)
  | Q :: L, k, h, i, hi => by
    have h' := bAnd_spec (b := List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun Q _ ih n => bAnd(G Q n, ih (Nat.succ n))) L (Nat.succ k)) h
    rcases i with _ | i
    · exact h'.1
    · have := listRec_and_spec G L (k + 1) h'.2 i (by simpa using hi)
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact this

theorem lenK_eq : ∀ L : List ℕ, lenK L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenK L) = _
    rw [lenK_eq L, List.length_cons]

theorem cart_off : ∀ j < 8, ∀ k < 8, j ≠ k → cart j k = 0 ∨ cart j k = -1 := by
  decide +kernel

theorem nland_testBit (x y q : ℕ) : (Nat.land x y).testBit q = (x.testBit q && y.testBit q) :=
  Nat.testBit_and x y q

theorem ones240_bits (a : ℕ) : ones240.testBit a = decide (a < 240) := by
  change ((1 <<< 240) - 1).testBit a = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem pairT_pT {T M : ℕ} (hrt : rtOK T M = true) (hM : M = adjC) {a k : ℕ} (ha : a < 240)
    (hk : k < 8) : (pairT.getD a #[]).getD k 0 = (pT T a k : ℤ) - 2 :=
  (pairT_getD ha ⟨k, hk⟩).trans (pair_root hrt hM ha hk)

theorem ipIs_iff {T M : ℕ} (hrt : rtOK T M = true) (hM : M = adjC) {a b : ℕ} (ha : a < 240)
    (hb : b < 240) (xp xm : ℕ) :
    ipIs T b a xp xm = true ↔ (ipT.getD b #[]).getD a 0 = (xp : ℤ) - xm := by
  have key : (ipT.getD b #[]).getD a 0 =
      (dotT T b a : ℤ) + 128 - 2 * sdT T b - 8 * spT T a := by
    rw [ipT_getD ha hb, ip_eq hrt hM hb ha, dotT_eq hrt hb ha, sdT_eq hrt hb, spT_eq hrt ha]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  change Nat.beq (dotT T b a + 128 + xm) (2 * sdT T b + 8 * spT T a + xp) = true ↔ _
  rw [Nat.beq_eq, key]
  omega

theorem qOK_facts {sgn : ℤ} {T P N D M : ℕ} {Qs : List ℕ} {X : ℕ} (ht : tabOK T P N D M = true)
    (hq : qOK sgn Qs X T = true) :
    Qs.length = 7 ∧ (∀ n' < 8, SegOK X n' (okC sgn [] n')) ∧
      ∀ i (hi : i < Qs.length), RowOK sgn Qs[i] i := by
  simp only [tabOK, Bool.and_eq_true] at ht
  obtain ⟨⟨⟨⟨hrt, hM⟩, -⟩, -⟩, -⟩ := ht
  have hM' : M = adjC := Nat.eq_of_beq_eq_true hM
  unfold qOK at hq
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨⟨hs, hl⟩, hqX⟩, hqF⟩ := hq
  have hsgn : sgn = 1 ∨ sgn = -1 := by simpa using hs
  refine ⟨by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true hl, fun n' hn' a => ?_, ?_⟩
  ·
    have h1 := Nat.eq_of_beq_eq_true (all8_spec hqX n' hn')
    rw [h1]
    unfold okC
    simp only [okFrom, Bool.and_true]
    by_cases ha : a < 240
    · rw [pairT_pT hrt hM' ha hn']
      rcases hsgn with rfl | rfl
      · change ones240.testBit a = _
        rw [ones240_bits]
        simp
      · change (setK fun a => Nat.beq (pT T a n') 2).testBit a = _
        rw [setK_bits]
        simp only [ha, decide_true, Bool.true_and]
        rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
        omega
    · have :(nIf((sgn == -1), setK fun a => Nat.beq (pT T a n') 2, ones240)).testBit a = false := by
        rcases hsgn with rfl | rfl
        · change ones240.testBit a = false
          rw [ones240_bits]
          simpa using ha
        · change (setK _).testBit a = false
          rw [setK_bits]
          simp [ha]
      rw [this]
      simp [ha]
  ·
    intro i hi b hb n' h1 h2 a
    have hk : qF (sgn == -1) Qs T (b / 30) = true := allBelow_spec hqF (by norm_num) _ (by omega)
    unfold qF at hk
    beta_reduce at hk
    have hk2 := allBelow_spec hk (by norm_num) (b % 30) (Nat.mod_lt _ (by norm_num))
    beta_reduce at hk2
    have e : Nat.add (Nat.mul (nat_lit 30) (b / 30)) (b % 30) = b := Nat.div_add_mod b 30
    rw [e] at hk2
    have hG := listRec_and_spec (fun Q n => all8 fun n' => Nat.beq
        (segK (fld(Q, Nat.mul (nat_lit 1984) b,
          Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1984)) (nat_lit 1))) n')
        (nIf(Nat.ble n' n, ones240, Nat.land (nIf(Nat.beq (adjB adjC n n') (nat_lit 1),
          setK fun a => ipIs T b a (nat_lit 0) (nat_lit 1),
          setK fun a => ipIs T b a (nat_lit 0) (nat_lit 0)))
          (nIf((sgn == -1), nIf(Nat.ble (pT T b n') (nat_lit 4),
            selK (selT T) n (Nat.sub (nat_lit 4) (pT T b n')), nat_lit 0),
            selK (selT T) n (pT T b n')))))) Qs 0 hk2 i hi
    beta_reduce at hG
    rw [Nat.zero_add] at hG
    have hseg := Nat.eq_of_beq_eq_true (all8_spec hG n' h2)
    rw [hseg]
    have hble : Nat.ble n' i = false := by
      cases h : Nat.ble n' i
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) (by omega)
    rw [hble]
    change (Nat.land _ _).testBit a = _
    rw [nland_testBit]
    have hpb := (rtF_spec hrt hb (i := n') h2).2.1
    by_cases ha : a < 240
    · unfold rowC
      rw [pairT_pT hrt hM' ha (by omega : i < 8), pairT_pT hrt hM' hb h2]
      have hcart : (nIf(Nat.beq (adjB adjC i n') (nat_lit 1),
          setK fun a => ipIs T b a (nat_lit 0) (nat_lit 1),
          setK fun a => ipIs T b a (nat_lit 0) (nat_lit 0))).testBit a =
          ((ipT.getD b #[]).getD a 0 == cart i n') := by
        rw [adjB_val i (by omega) n' h2]
        rcases cart_off i (by omega) n' h2 (by omega) with hc | hc
        · rw [hc, if_neg (by decide)]
          change (setK fun a => ipIs T b a 0 0).testBit a = _
          rw [setK_bits, decide_eq_true ha, Bool.true_and, Bool.eq_iff_iff, ipIs_iff hrt hM' ha hb,
            beq_iff_eq]
          simp
        · rw [hc, if_pos rfl]
          change (setK fun a => ipIs T b a 0 1).testBit a = _
          rw [setK_bits, decide_eq_true ha, Bool.true_and, Bool.eq_iff_iff, ipIs_iff hrt hM' ha hb,
            beq_iff_eq]
          simp
      rw [hcart, decide_eq_true ha, Bool.true_and]
      congr 1
      rcases hsgn with rfl | rfl
      · change (selK (selT T) i (pT T b n')).testBit a = _
        rw [sel_bits T (by omega) hpb, decide_eq_true ha, Bool.true_and, Bool.eq_iff_iff,
          Nat.beq_eq, beq_iff_eq]
        omega
      · have h4 : Nat.ble (pT T b n') 4 = true := by
          rw [Nat.ble_eq]
          exact hpb
        change (nIf(Nat.ble (pT T b n') (nat_lit 4),
          selK (selT T) i (Nat.sub (nat_lit 4) (pT T b n')), nat_lit 0)).testBit a = _
        rw [h4]
        change (selK (selT T) i (4 - pT T b n')).testBit a = _
        rw [sel_bits T (by omega) (by omega), decide_eq_true ha, Bool.true_and, Bool.eq_iff_iff,
          Nat.beq_eq, beq_iff_eq]
        omega
    · have hz : ∀ f : ℕ → Bool, (setK f).testBit a = false := fun f => by
        rw [setK_bits]
        simp [ha]
      have hc : (nIf(Nat.beq (adjB adjC i n') (nat_lit 1),
          setK fun a => ipIs T b a (nat_lit 0) (nat_lit 1),
          setK fun a => ipIs T b a (nat_lit 0) (nat_lit 0))).testBit a = false := by
        cases Nat.beq (adjB adjC i n') 1
        · exact hz _
        · exact hz _
      rw [hc]
      simp [ha]

theorem card_sgnSym_le (sgn : ℤ) {T P N D M : ℕ} (ht : tabOK T P N D M = true) {Qs : List ℕ}
    {X B C n Nb : ℕ} (hq : qOK sgn Qs X T = true) (h0 : byteAt B 0 = 0) (hn : byteAt B n = 240)
    (hB : ∀ k < n, byteAt B k < byteAt B (k + 1))
    (hs : ∑ k ∈ Finset.range n, fld(C, Nat.shiftLeft k 4, 0xFFFF) = Nb)
    (hk : ∀ k < n, symF Qs X B C k = true) :
    Nat.card {w : W8 // SgnSym sgn w} ≤ Nb := by
  obtain ⟨hlen, hX, hrow⟩ := qOK_facts ht hq
  refine le_trans (card_le_enum sgn) (le_of_eq ?_)
  rw [enum_eq_extN, extN_length_succ, ← hs]
  have hch : ∀ k < n, fld(C, Nat.shiftLeft k 4, 0xFFFF) = ∑ a ∈ Finset.range 240,
      if (okC sgn [] 0 a && (decide (byteAt B k ≤ a) && decide (a < byteAt B (k + 1)))) then
        (extN sgn 7 [a]).length else 0 := fun k hkn => by
    have e := Nat.eq_of_beq_eq_true (show Nat.beq (chunkK Qs X (byteAt B k) (byteAt B (k + 1)))
      (fld(C, Nat.shiftLeft k 4, 0xFFFF)) = true from hk k hkn)
    rw [← e, chunk_spec hlen hrow hX (le_of_lt (hB k hkn))
      (hn ▸ byte_mono hB (k + 1) n (by omega) le_rfl)]
  simp only [List.length_nil, List.nil_append]
  rw [Finset.sum_congr rfl fun k hk => hch k (Finset.mem_range.1 hk),
    ← chunks_sum (fun a => if okC sgn [] 0 a then (extN sgn 7 [a]).length else 0) h0 hn hB]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  cases okC sgn [] 0 a <;> simp

end CFSG.KC.WE8K

end
