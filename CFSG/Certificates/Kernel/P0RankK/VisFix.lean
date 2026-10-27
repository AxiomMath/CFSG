module

public import CFSG.Certificates.Kernel.P0RankK.VisTab
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb CFSG.Monster.B.TwoA.Sp8.P0Rank MonsterB.P0Rank

theorem rowOf_cons (p x : ℕ) (xs : List ℕ) :
    rowOf p (x :: xs) = pAct 16 65535 16 p x ||| rowOf p xs <<< 16 := rfl

theorem or_shl16_eq {a r : ℕ} (ha : a < 2 ^ 16) : a ||| r <<< 16 = a + 2 ^ 16 * r := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha r, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm]

theorem fields_rowOf (p : ℕ) : ∀ xs : List ℕ,
    fields 16 65535 (rowOf p xs) xs.length = xs.map (pAct 16 65535 16 p)
  | [] => rfl
  | x :: xs => by
    have ha : pAct 16 65535 16 p x < 2 ^ 16 := pAct_lt (w := 16) 16 p x
    rw [List.length_cons, fields, rowOf_cons, or_shl16_eq ha, List.map_cons]
    congr 1
    · change (pAct 16 65535 16 p x + 2 ^ 16 * rowOf p xs) &&& (2 ^ 16 - 1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    · rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 16),
        Nat.div_eq_of_lt ha, Nat.zero_add]
      exact fields_rowOf p xs

private theorem id_fields16 :
    fields 16 65535 ((List.range 16).foldl (fun a j => a ||| 2 ^ (17 * j)) 0) 16 =
      colsOf 16 id := by decide +kernel

theorem aAct_eq (AT κ : ℕ) {x : ℕ} (hx : x < 2 ^ 16) :
    aAct AT κ x = colsAct (fields 16 65535 (fld AT (256 * κ) m256) 16) x :=
  pAct_eq_colsAct 16 65535 16 _ x hx

theorem aAct_eq_actK {AT : ℕ} {GC : List (List ℕ)} (h0 : at0OK AT GC = true)
    (hrows : ∀ t < 10, atOK AT GC t = true) (hGC : ∀ cs ∈ GC, ∀ c ∈ cs, c < 2 ^ 16) :
    ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, aAct AT κ x = actK GC κ x := by
  rw [at0OK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h0
  have hid := Nat.eq_of_beq_eq_true h0.1.1.1
  have hlen : GC.length = 10 := Nat.eq_of_beq_eq_true h0.1.1.2
  have hcols : ∀ cs ∈ GC, cs.length = 16 := fun cs hcs =>
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 h0.1.2 cs hcs)
  have key : ∀ t ≤ 10, ∀ κ < 2 ^ t, ∀ x < 2 ^ 16, aAct AT κ x = actK GC κ x := by
    intro t
    induction t with
    | zero =>
      intro _ κ hκ x hx
      have : κ = 0 := by simpa using hκ
      subst this
      rw [aAct_eq _ _ hx, Nat.mul_zero, hid, id_fields16,
        colsAct_colsOf (f := id) (fun _ _ => rfl) hx, actK_zero_left]
      rfl
    | succ t ih =>
      intro ht κ hκ x hx
      by_cases hlo : κ < 2 ^ t
      · exact ih (by omega) κ hlo x hx
      obtain ⟨κ', rfl⟩ : ∃ κ', κ = κ' + 2 ^ t := ⟨κ - 2 ^ t, by omega⟩
      have hκ' : κ' < 2 ^ t := by rw [pow_succ] at hκ; omega
      have hrow := hrows t (by omega)
      simp only [atOK, List.all_eq_true, List.mem_range, Nat.beq_eq] at hrow
      have hr := hrow κ' hκ'
      have hGCt : GC.getD t [] ∈ GC := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      have hlen16 : (GC.getD t []).length = 16 := by
        have := hcols _ hGCt
        simpa using this
      have hcs := hGC _ hGCt
      have hcol_lt : colsAct (GC.getD t []) x < 2 ^ 16 := colsAct_lt hcs x
      have hf := fields_rowOf (fld AT (256 * κ') m256) (GC.getD t [])
      rw [hlen16] at hf
      rw [aAct_eq _ _ hx, hr, hf]
      let g := colsAct (fields 16 65535 (fld AT (256 * κ') m256) 16)
      have hmap : (GC.getD t []).map (pAct 16 65535 16 (fld AT (256 * κ') m256)) =
          (GC.getD t []).map g :=
        List.map_congr_left fun c hc => pAct_eq_colsAct 16 65535 16 _ c (hcs c hc)
      rw [hmap, colsAct_map (colsAct_zero _) (colsAct_xor _), ← aAct_eq _ _ hcol_lt,
        ih (by omega) κ' hκ' _ hcol_lt, actK_add_two_pow GC hκ' (by omega)]
  exact key 10 le_rfl

theorem testBit_maskB (f : ℕ → Bool) : ∀ n k, (maskB f n).testBit k = (decide (k < n) && f k)
  | 0, k => by simp [maskB]
  | n + 1, k => by
    change (maskB f n ||| (bif f n then 1 <<< n else 0)).testBit k = _
    rw [Nat.testBit_or, testBit_maskB f n k]
    by_cases hk : k = n
    · subst hk
      cases h : f k <;> simp [h, Nat.shiftLeft_eq, Nat.testBit_two_pow_self]
    · have h1 : (bif f n then 1 <<< n else 0).testBit k = false := by
        cases f n
        · simp
        · simp only [cond_true, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
          simpa using Ne.symm hk
      rw [h1, Bool.or_false]
      by_cases hkn : k < n
      · simp [hkn, show k < n + 1 by omega]
      · simp [hkn, show ¬ k < n + 1 by omega]

set_option exponentiation.threshold 1024 in
theorem testBit_m1024 (k : ℕ) : m1024.testBit k = decide (k < 1024) := by
  rw [m1024, Nat.testBit_two_pow_sub_one]

theorem testBit_beq_land_one (e z : ℕ) : Nat.beq (Nat.land (Nat.shiftRight e z) 1) 1 = e.testBit z := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((e >>> z) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  cases h : Nat.beq (e / 2 ^ z % 2) 1
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

theorem faOK_iff {FA AT RT o : ℕ} (h : faOK FA AT RT o = true) (κ : ℕ) :
    (fld FA (1024 * o) m1024).testBit κ = true ↔ κ < 1024 ∧ aAct AT κ (vO RT o) = vO RT o := by
  rw [faOK, Nat.beq_eq] at h
  rw [h, testBit_maskB, Bool.and_eq_true, decide_eq_true_iff, Nat.beq_eq]

theorem fbOK_iff {FB BT z : ℕ} (h : fbOK FB BT z = true) (κ : ℕ) :
    (fld FB (1024 * z) m1024).testBit κ = true ↔ κ < 1024 ∧ bAct BT κ (emb z) = emb z := by
  rw [fbOK, Nat.beq_eq] at h
  rw [h, testBit_maskB, Bool.and_eq_true, decide_eq_true_iff, Nat.beq_eq]

theorem vO_lt (RT o : ℕ) : vO RT o < 2 ^ 16 :=
  Nat.and_lt_two_pow _ (by norm_num : (65535 : ℕ) < 2 ^ 16)

theorem emb_lt' (z : ℕ) : emb z < 2 ^ 9 := colsAct_lt (cs := embCols) (w := 9) (by decide) z

theorem faOK_iff_actK {FA AT RT o : ℕ} {GC : List (List ℕ)} (h : faOK FA AT RT o = true)
    (h0 : at0OK AT GC = true) (hrows : ∀ t < 10, atOK AT GC t = true)
    (hGC : ∀ cs ∈ GC, ∀ c ∈ cs, c < 2 ^ 16) (κ : ℕ) :
    (fld FA (1024 * o) m1024).testBit κ = true ↔ κ < 1024 ∧ actK GC κ (vO RT o) = vO RT o := by
  rw [faOK_iff h]
  constructor
  · rintro ⟨hκ, hfix⟩
    exact ⟨hκ, by rwa [← aAct_eq_actK h0 hrows hGC κ hκ _ (vO_lt RT o)]⟩
  · rintro ⟨hκ, hfix⟩
    exact ⟨hκ, by rwa [aAct_eq_actK h0 hrows hGC κ hκ _ (vO_lt RT o)]⟩

theorem fbOK_iff_actK {FB BT z : ℕ} {BG : List (List ℕ)} (h : fbOK FB BT z = true)
    (h0 : bt0OK BT BG = true) (hrows : ∀ t < 10, btOK BT BG t = true)
    (hBG : ∀ cs ∈ BG, ∀ c ∈ cs, c < 2 ^ 9) (κ : ℕ) :
    (fld FB (1024 * z) m1024).testBit κ = true ↔ κ < 1024 ∧ actK BG κ (emb z) = emb z := by
  rw [fbOK_iff h]
  constructor
  · rintro ⟨hκ, hfix⟩
    exact ⟨hκ, by rwa [← bAct_eq_actK h0 hrows hBG κ hκ _ (emb_lt' z)]⟩
  · rintro ⟨hκ, hfix⟩
    exact ⟨hκ, by rwa [bAct_eq_actK h0 hrows hBG κ hκ _ (emb_lt' z)]⟩

@[expose] noncomputable def cuN (FB e n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) m1024
    (fun z ih => Nat.land ih (bif Nat.beq (Nat.land (Nat.shiftRight e z) 1) 1 then
      fld FB (1024 * z) m1024 else m1024)) n

theorem testBit_cuN (FB e κ : ℕ) : ∀ n, (cuN FB e n).testBit κ = true ↔
    κ < 1024 ∧ ∀ z < n, e.testBit z = true → (fld FB (1024 * z) m1024).testBit κ = true
  | 0 => by
    change m1024.testBit κ = true ↔ _
    rw [testBit_m1024]
    simp
  | n + 1 => by
    change (Nat.land (cuN FB e n) (bif Nat.beq (Nat.land (Nat.shiftRight e n) 1) 1 then
      fld FB (1024 * n) m1024 else m1024)).testBit κ = true ↔ _
    change (cuN FB e n &&& _).testBit κ = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, testBit_cuN FB e κ n, testBit_beq_land_one]
    constructor
    · rintro ⟨⟨hκ, hz⟩, hn⟩
      refine ⟨hκ, fun z hz' he => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hz' with hlt | rfl
      · exact hz z hlt he
      · rwa [he, cond_true] at hn
    · rintro ⟨hκ, hz⟩
      refine ⟨⟨hκ, fun z hz' he => hz z (by omega) he⟩, ?_⟩
      cases he : e.testBit n
      · rw [cond_false, testBit_m1024]
        simpa using hκ
      · rw [cond_true]
        exact hz n (by omega) he

theorem testBit_cuOf (FB e κ : ℕ) : (cuOf FB e).testBit κ = true ↔
    κ < 1024 ∧ ∀ z < 32, e.testBit z = true → (fld FB (1024 * z) m1024).testBit κ = true :=
  testBit_cuN FB e κ 32

theorem testBit_cuOf_fix {FB BT e : ℕ} (hfb : ∀ z < 32, fbOK FB BT z = true) (κ : ℕ) :
    (cuOf FB e).testBit κ = true ↔
      κ < 1024 ∧ ∀ z < 32, e.testBit z = true → bAct BT κ (emb z) = emb z := by
  rw [testBit_cuOf]
  constructor
  · rintro ⟨hκ, h⟩
    exact ⟨hκ, fun z hz he => ((fbOK_iff (hfb z hz) κ).1 (h z hz he)).2⟩
  · rintro ⟨hκ, h⟩
    exact ⟨hκ, fun z hz he => (fbOK_iff (hfb z hz) κ).2 ⟨hκ, h z hz he⟩⟩

@[expose] def YEntOK (YE FB s : ℕ) (e : YEnt) : Prop :=
  pc (fld YE (32 * e.1) m32) = 2 ^ s ∧ e.2.1 = cuOf FB (fld YE (32 * e.1) m32) ∧ e.2.2 = pc e.2.1

theorem ygEnts_spec {YE FB s : ℕ} : ∀ (es : List YEnt) (i j : ℕ), ygEnts YE FB s i es = some j →
    j = i + es.length ∧ ∀ k (hk : k < es.length), es[k].1 = i + k ∧ YEntOK YE FB s es[k]
  | [], i, j, h => by
    simp only [ygEnts, Option.some.injEq] at h
    exact ⟨by simp [h], fun k hk => absurd hk (by simp)⟩
  | e :: es, i, j, h => by
    simp only [ygEnts] at h
    cases hc : (Nat.beq e.1 i && Nat.beq (pc (fld YE (32 * i) m32)) (2 ^ s) &&
        Nat.beq e.2.1 (cuOf FB (fld YE (32 * i) m32)) && Nat.beq e.2.2 (pc e.2.1)) with
    | false => rw [hc, cond_false] at h; exact absurd h (by simp)
    | true =>
      rw [hc, cond_true] at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at hc
      obtain ⟨⟨⟨he1, hpc⟩, hcu⟩, hcnt⟩ := hc
      obtain ⟨hj, hrest⟩ := ygEnts_spec es (i + 1) j h
      refine ⟨by simp [hj]; omega, fun k hk => ?_⟩
      rcases k with _ | k
      · refine ⟨by simpa using he1, ?_⟩
        rw [List.getElem_cons_zero, YEntOK, he1]
        exact ⟨hpc, hcu, hcnt⟩
      · obtain ⟨h1, h2⟩ := hrest k (by simpa using hk)
        exact ⟨by simp only [List.getElem_cons_succ]; omega, by simpa using h2⟩

theorem ygGroups_end {YE FB NY : ℕ} : ∀ (gs : List (List YEnt)) (s i : ℕ),
    ygGroups YE FB NY s i gs = true → i ≤ NY
  | [], s, i, h => by
    simp only [ygGroups, Nat.beq_eq] at h
    omega
  | g :: gs, s, i, h => by
    simp only [ygGroups] at h
    cases hg : ygEnts YE FB s i g with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some j =>
      rw [hg] at h
      have := (ygEnts_spec g i j hg).1
      have := ygGroups_end gs (s + 1) j h
      omega

theorem ygGroups_spec {YE FB NY : ℕ} : ∀ (gs : List (List YEnt)) (s i : ℕ),
    ygGroups YE FB NY s i gs = true →
      (∀ t < gs.length, ∀ e ∈ gs.getD t [], i ≤ e.1 ∧ e.1 < NY ∧ YEntOK YE FB (s + t) e) ∧
      (∀ i', i ≤ i' → i' < NY → ∃ t < gs.length, ∃ e ∈ gs.getD t [], e.1 = i')
  | [], s, i, h => by
    simp only [ygGroups, Nat.beq_eq] at h
    exact ⟨fun t ht => absurd ht (by simp), fun i' h1 h2 => by omega⟩
  | g :: gs, s, i, h => by
    simp only [ygGroups] at h
    cases hg : ygEnts YE FB s i g with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some j =>
      rw [hg] at h
      obtain ⟨hj, hents⟩ := ygEnts_spec g i j hg
      obtain ⟨hrest1, hrest2⟩ := ygGroups_spec gs (s + 1) j h
      have hjN := ygGroups_end gs (s + 1) j h
      have hjle : ∀ k (hk : k < g.length), g[k].1 < NY := fun k hk => by
        have := (hents k hk).1
        omega
      refine ⟨fun t ht e he => ?_, fun i' h1 h2 => ?_⟩
      · rcases t with _ | t
        · simp only [List.getD_cons_zero] at he
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
          obtain ⟨hk1, hk2⟩ := hents k hk
          exact ⟨by omega, hjle k hk, by simpa using hk2⟩
        · simp only [List.getD_cons_succ] at he
          obtain ⟨ha, hb, hc⟩ := hrest1 t (by simpa using ht) e he
          exact ⟨by omega, hb, by simpa [Nat.add_assoc, Nat.add_comm 1 t] using hc⟩
      · by_cases hi' : i' < j
        · refine ⟨0, by simp, g[i' - i]'(by omega), by simp, ?_⟩
          have := (hents (i' - i) (by omega)).1
          omega
        · obtain ⟨t, ht, e, he, hei⟩ := hrest2 i' (by omega) h2
          exact ⟨t + 1, by simpa using ht, e, by simpa using he, hei⟩

theorem ygOK_spec {YE FB NY : ℕ} {YG : List (List YEnt)} (h : ygOK YE FB NY YG = true) :
    YG.length = 6 ∧ (∀ s < 6, ∀ e ∈ YG.getD s [], e.1 < NY ∧ YEntOK YE FB s e) ∧
      (∀ i < NY, ∃ s < 6, ∃ e ∈ YG.getD s [], e.1 = i) := by
  rw [ygOK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hlen, hg⟩ := h
  obtain ⟨h1, h2⟩ := ygGroups_spec YG 0 0 hg
  refine ⟨hlen, fun s hs e he => ?_, fun i hi => ?_⟩
  · obtain ⟨-, hb, hc⟩ := h1 s (by omega) e he
    exact ⟨hb, by simpa using hc⟩
  · obtain ⟨t, ht, e, he, hei⟩ := h2 i (Nat.zero_le _) hi
    exact ⟨t, by omega, e, he, hei⟩

end CFSG.KC.P0Vis

end
