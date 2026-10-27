module

public import Certificates.Data.Kernel.LocalQT.Tab2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Tab
public import CFSG.Certificates.Kernel.Common.StrSplit
public import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.LQT.T2

open CFSG.KC.Str CFSG.KC.Ord CFSG.KC.LQT.P CFSG.QuasithinUnique.Unc25G2.M2x

theorem brec {α : Type} (f t : α) (b : Bool) :
    Bool.rec (motive := fun _ => α) f t b = if b = true then t else f := by
  cases b <;> rfl

theorem mkS_eq (o s d f u : Nat) :
    mkS o s d f u = o + (2 * s + 4 * d) + (8 * f + 8388608 * u) := rfl

theorem bit0_eq (s : Nat) : bitS s 0 = s % 2 := by
  change s / 2 ^ 0 % 2 = _
  simp

theorem bit1_eq (s : Nat) : bitS s 1 = s / 2 % 2 := by
  change s / 2 ^ 1 % 2 = _
  simp

theorem bit2_eq (s : Nat) : bitS s 2 = s / 4 % 2 := by
  change s / 2 ^ 2 % 2 = _
  norm_num

theorem fstS_eq (s : Nat) : fstS s = s / 8 % 1048576 := rfl

theorem curS_eq (s : Nat) : curS s = s / 8388608 := rfl

theorem bit_le (s i : Nat) : bitS s i ≤ 1 := by
  change s / 2 ^ i % 2 ≤ 1
  have := Nat.mod_lt (s / 2 ^ i) (by norm_num : 0 < 2)
  omega

theorem fst_lt (s : Nat) : fstS s < 1048576 := by
  rw [fstS_eq]
  omega

theorem bit0_zero : bitS 0 0 = 0 := by
  rw [bit0_eq]

theorem mk_dec {o s d f u : Nat} (ho : o ≤ 1) (hs : s ≤ 1) (hd : d ≤ 1) (hf : f < 1048576) :
    bitS (mkS o s d f u) 0 = o ∧ bitS (mkS o s d f u) 1 = s ∧ bitS (mkS o s d f u) 2 = d ∧
      fstS (mkS o s d f u) = f ∧ curS (mkS o s d f u) = u := by
  rw [bit0_eq, bit1_eq, bit2_eq, fstS_eq, curS_eq, mkS_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem dec0 {d u : Nat} (hd : d ≤ 1) :
    bitS (mkS 1 0 d 0 u) 0 = 1 ∧ bitS (mkS 1 0 d 0 u) 1 = 0 ∧ bitS (mkS 1 0 d 0 u) 2 = d ∧
      fstS (mkS 1 0 d 0 u) = 0 ∧ curS (mkS 1 0 d 0 u) = u :=
  mk_dec (le_refl _) (by omega) hd (by omega)

theorem dec1 {d f u : Nat} (hd : d ≤ 1) (hf : f < 1048576) :
    bitS (mkS 1 1 d f u) 0 = 1 ∧ bitS (mkS 1 1 d f u) 1 = 1 ∧ bitS (mkS 1 1 d f u) 2 = d ∧
      fstS (mkS 1 1 d f u) = f ∧ curS (mkS 1 1 d f u) = u :=
  mk_dec (le_refl _) (le_refl _) hd hf

theorem step_eq (c s : Nat) : stepS c s =
    if 48 ≤ c ∧ c ≤ 57 then mkS (bitS s 0) (bitS s 1) 1 (fstS s) (10 * curS s + (c - 48))
    else if c = 44 then
      (if bitS s 1 = 0 ∧ bitS s 2 = 1 ∧ curS s < 1048576 then mkS (bitS s 0) 1 0 (curS s) 0
        else 0)
    else if c = 32 then (if bitS s 1 = 1 ∧ bitS s 2 = 1 then mkS (bitS s 0) 0 0 0 0 else 0)
    else 0 := by
  simp only [stepS, brec, andB_iff, Nat.ble_eq, beq_iff, blt_iff, Nat.add_eq, Nat.mul_eq,
    Nat.sub_eq]

theorem step_digit {c s : Nat} (h : 48 ≤ c ∧ c ≤ 57) :
    stepS c s = mkS (bitS s 0) (bitS s 1) 1 (fstS s) (10 * curS s + (c - 48)) := by
  rw [step_eq, ite_eq_left h]

theorem step_comma {s : Nat} (h : bitS s 1 = 0 ∧ bitS s 2 = 1 ∧ curS s < 1048576) :
    stepS 44 s = mkS (bitS s 0) 1 0 (curS s) 0 := by
  rw [step_eq, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left h]

theorem step_comma_bad {s : Nat} (h : ¬ (bitS s 1 = 0 ∧ bitS s 2 = 1 ∧ curS s < 1048576)) :
    stepS 44 s = 0 := by
  rw [step_eq, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right h]

theorem step_space {s : Nat} (h : bitS s 1 = 1 ∧ bitS s 2 = 1) :
    stepS 32 s = mkS (bitS s 0) 0 0 0 0 := by
  rw [step_eq, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left h]

theorem step_space_bad {s : Nat} (h : ¬ (bitS s 1 = 1 ∧ bitS s 2 = 1)) : stepS 32 s = 0 := by
  rw [step_eq, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right h]

theorem step_other {c s : Nat} (h1 : ¬ (48 ≤ c ∧ c ≤ 57)) (h2 : c ≠ 44) (h3 : c ≠ 32) :
    stepS c s = 0 := by
  rw [step_eq, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

theorem step_ok {c s : Nat} (h : bitS (stepS c s) 0 = 1) : bitS s 0 = 1 := by
  have h0 := bit_le s 0
  have h1 := bit_le s 1
  have hf := fst_lt s
  rw [step_eq] at h
  split_ifs at h with ha hb hc hd he
  · rwa [(mk_dec (by omega) (by omega) (by omega) hf).1] at h
  · rwa [(mk_dec (by omega) (by omega) (by omega) hc.2.2).1] at h
  · rw [bit0_zero] at h
    omega
  · rwa [(mk_dec (by omega) (by omega) (by omega) (by omega)).1] at h
  · rw [bit0_zero] at h
    omega
  · rw [bit0_zero] at h
    omega

theorem letPN_eq (y : Nat) (k : Nat → Nat × List (Nat × Nat)) : letPN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def runF (cs : List Char) : Nat → List (Nat × Nat) → Nat × List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat) → Nat × List (Nat × Nat))
    (fun s acc => Prod.mk s acc)
    (fun c _ ih s acc => letPN (stepS (Char.toNat c) s) fun s' =>
      ih s' (Bool.rec (motive := fun _ => List (Nat × Nat)) acc
        (List.cons (Prod.mk (fstS s) (curS s)) acc)
        (andB (Nat.beq (Char.toNat c) 32) (Nat.beq (bitS s' 0) 1)))) cs

theorem runP_eq (cs : List Char) : runP cs = runF cs (mkS 1 0 0 0 0) [] := rfl

theorem runF_cons (c : Char) (cs : List Char) (s : Nat) (acc : List (Nat × Nat)) :
    runF (c :: cs) s acc = runF cs (stepS c.toNat s)
      (if c.toNat = 32 ∧ bitS (stepS c.toNat s) 0 = 1 then (fstS s, curS s) :: acc else acc) := by
  have : runF (c :: cs) s acc = letPN (stepS c.toNat s) fun s' => runF cs s'
      (Bool.rec (motive := fun _ => List (Nat × Nat)) acc ((fstS s, curS s) :: acc)
        (andB (Nat.beq c.toNat 32) (Nat.beq (bitS s' 0) 1))) := rfl
  rw [this, letPN_eq, brec]
  simp only [andB_iff, beq_iff]

@[expose] def tok (pk : List Char × List Char) : List Char := pk.1 ++ ',' :: pk.2

@[expose] def val (pk : List Char × List Char) : Nat × Nat := (decVal pk.1, decVal pk.2)

@[expose] def Dig (q : List Char) : Prop := ∀ c ∈ q, c.isDigit = true

@[expose] def Good (pk : List Char × List Char) : Prop :=
  pk.1 ≠ [] ∧ Dig pk.1 ∧ pk.2 ≠ [] ∧ Dig pk.2

@[expose] def Cur (q : List Char) (s : Nat) : Prop :=
  (∃ d, d ≤ 1 ∧ Dig q ∧ (d = 1 ↔ q ≠ []) ∧ s = mkS 1 0 d 0 (decVal q)) ∨
  (∃ p k d, q = p ++ ',' :: k ∧ p ≠ [] ∧ Dig p ∧ decVal p < 1048576 ∧ Dig k ∧ d ≤ 1 ∧
    (d = 1 ↔ k ≠ []) ∧ s = mkS 1 1 d (decVal p) (decVal k))

@[expose] def Inv (pre : List Char) (s : Nat) (acc : List (Nat × Nat)) : Prop :=
  bitS s 0 = 1 → ∃ (T : List (List Char × List Char)) (q : List Char), pre = [' '].intercalate (T.map tok ++ [q]) ∧ acc = (T.map val).reverse ∧
    (∀ pk ∈ T, Good pk) ∧ Cur q s

theorem ic_snoc (L : List (List Char)) (q : List Char) (c : Char) :
    [' '].intercalate (L ++ [q ++ [c]]) = [' '].intercalate (L ++ [q]) ++ [c] := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.cons_append, List.cons_append, List.intercalate_cons_of_ne_nil (by simp),
      List.intercalate_cons_of_ne_nil (by simp), ih]
    simp

theorem ic_two (L : List (List Char)) (x y : List Char) :
    [' '].intercalate (L ++ [x, y]) = [' '].intercalate (L ++ [x]) ++ [' '] ++ y := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rw [List.cons_append, List.cons_append, List.intercalate_cons_of_ne_nil (by simp),
      List.intercalate_cons_of_ne_nil (by simp), ih]
    simp

theorem decVal_snoc (q : List Char) (c : Char) :
    decVal (q ++ [c]) = 10 * decVal q + (c.toNat - 48) := by
  simp only [decVal, List.foldl_append, List.foldl_cons, List.foldl_nil]
  ring

theorem isDigit_iff {c : Char} : c.isDigit = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 :=
  Char.isDigit_iff_toNat

theorem dig_snoc {q : List Char} {c : Char} (hq : Dig q) (hc : c.isDigit = true) :
    Dig (q ++ [c]) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hq x hx
  · rw [List.mem_singleton.mp hx]
    exact hc

theorem inv_step {pre : List Char} {s : Nat} {acc : List (Nat × Nat)} (c : Char)
    (h : Inv pre s acc) : Inv (pre ++ [c]) (stepS c.toNat s)
      (if c.toNat = 32 ∧ bitS (stepS c.toNat s) 0 = 1 then (fstS s, curS s) :: acc else acc) := by
  unfold Inv at h ⊢
  intro h'
  obtain ⟨T, q, hpre, hacc, hT, hq⟩ := h (step_ok h')
  by_cases hdig : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · have hcd : c.isDigit = true := isDigit_iff.mpr hdig
    rw [ite_eq_right (fun h => absurd h.1 (by omega))]
    refine ⟨T, q ++ [c], by rw [hpre, ic_snoc], hacc, hT, ?_⟩
    rw [step_digit hdig]
    rcases hq with ⟨d, hd, hdq, -, rfl⟩ | ⟨p, k, d, rfl, hp, hdp, hpv, hdk, hd, -, rfl⟩
    · obtain ⟨e0, e1, -, e3, e4⟩ := dec0 hd
      rw [e0, e1, e3, e4]
      exact Or.inl ⟨1, le_refl _, dig_snoc hdq hcd, by simp, by rw [decVal_snoc]⟩
    · obtain ⟨e0, e1, -, e3, e4⟩ := dec1 hd hpv
      rw [e0, e1, e3, e4]
      exact Or.inr ⟨p, k ++ [c], 1, by simp, hp, hdp, hpv, dig_snoc hdk hcd, le_refl _, by simp,
        by rw [decVal_snoc]⟩
  by_cases h44 : c.toNat = 44
  · have hc : c = ',' := Char.toNat_inj.mp h44
    subst hc
    rw [ite_eq_right (fun h => absurd h.1 (by decide))]
    rw [h44] at h' ⊢
    rcases hq with ⟨d, hd, hdq, hdiff, rfl⟩ | ⟨p, k, d, rfl, -, -, hpv, -, hd, -, rfl⟩
    · obtain ⟨e0, e1, e2, -, e4⟩ := dec0 hd
      by_cases hcond : d = 1 ∧ decVal q < 1048576
      · rw [step_comma (by rw [e1, e2, e4]; exact ⟨rfl, hcond⟩), e0, e4]
        exact ⟨T, q ++ [','], by rw [hpre, ic_snoc], hacc, hT, Or.inr ⟨q, [], 0, by simp,
          hdiff.mp hcond.1, hdq, hcond.2, by simp [Dig], by omega, by simp, rfl⟩⟩
      · rw [step_comma_bad (by rw [e1, e2, e4]; exact fun h => hcond ⟨h.2.1, h.2.2⟩),
          bit0_zero] at h'
        omega
    · obtain ⟨-, e1, -, -, -⟩ := dec1 hd hpv
      rw [step_comma_bad (by rw [e1]; omega), bit0_zero] at h'
      omega
  by_cases h32 : c.toNat = 32
  · have hc : c = ' ' := Char.toNat_inj.mp h32
    subst hc
    rw [h32] at h' ⊢
    rcases hq with ⟨d, hd, -, -, rfl⟩ | ⟨p, k, d, rfl, hp, hdp, hpv, hdk, hd, hdiff, rfl⟩
    · obtain ⟨-, e1, -, -, -⟩ := dec0 hd
      rw [step_space_bad (by rw [e1]; omega), bit0_zero] at h'
      omega
    · obtain ⟨e0, e1, e2, e3, e4⟩ := dec1 hd hpv
      by_cases hd1 : d = 1
      · rw [step_space (by rw [e1, e2]; exact ⟨rfl, hd1⟩), e0]
        have hz := (mk_dec (o := 1) (s := 0) (d := 0) (f := 0) (u := 0) (by omega) (by omega)
          (by omega) (by omega)).1
        rw [ite_eq_left ⟨rfl, hz⟩, e3, e4]
        refine ⟨T ++ [(p, k)], [], ?_, ?_, ?_, Or.inl ⟨0, by omega, by simp [Dig], by simp, rfl⟩⟩
        · have := ic_two (T.map tok) (tok (p, k)) []
          rw [List.append_nil] at this
          rw [hpre, List.map_append, List.map_singleton, List.append_assoc, List.singleton_append,
            this]
          rfl
        · rw [hacc]
          simp [val]
        · intro pk hpk
          rcases List.mem_append.mp hpk with hpk | hpk
          · exact hT pk hpk
          · rw [List.mem_singleton.mp hpk]
            exact ⟨hp, hdp, hdiff.mp hd1, hdk⟩
      · rw [step_space_bad (by rw [e1, e2]; omega), bit0_zero] at h'
        omega
  rw [step_other hdig h44 h32, bit0_zero] at h'
  omega

theorem inv_init : Inv [] (mkS 1 0 0 0 0) [] := by
  unfold Inv
  exact fun _ => ⟨[], [], by simp, rfl, by simp, Or.inl ⟨0, by omega, by simp [Dig], by simp, rfl⟩⟩

theorem inv_run : ∀ (rest pre : List Char) (s : Nat) (acc : List (Nat × Nat)), Inv pre s acc →
    Inv (pre ++ rest) (runF rest s acc).1 (runF rest s acc).2
  | [], pre, s, acc, h => by
    rw [List.append_nil]
    exact h
  | c :: rest, pre, s, acc, h => by
    have e : pre ++ c :: rest = (pre ++ [c]) ++ rest := by simp
    rw [runF_cons, e]
    exact inv_run rest _ _ _ (inv_step c h)

theorem parseK_shape {cs : List Char} {l : List (Nat × Nat)} (h : parseK cs = some l) :
    ∃ T : List (List Char × List Char), T ≠ [] ∧ (∀ pk ∈ T, Good pk) ∧
      cs = [' '].intercalate (T.map tok) ∧ l = T.map val := by
  have hinv := inv_run cs [] _ _ inv_init
  rw [List.nil_append, ← runP_eq] at hinv
  unfold Inv at hinv
  unfold parseK at h
  rw [brec] at h
  split_ifs at h with hc
  simp only [andB_iff, beq_iff] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  obtain ⟨T, q, hcs, hacc, hT, hq⟩ := hinv h0
  rcases hq with ⟨d, hd, -, -, he⟩ | ⟨p, k, d, rfl, hp, hdp, hpv, hdk, hd, hdiff, he⟩
  · rw [he, (dec0 hd).2.1] at h1
    omega
  · obtain ⟨-, -, e2, e3, e4⟩ := dec1 hd hpv
    rw [he] at h2 h
    rw [e2] at h2
    rw [e3, e4, hacc] at h
    refine ⟨T ++ [(p, k)], by simp, ?_, ?_, ?_⟩
    · intro pk hpk
      rcases List.mem_append.mp hpk with hpk | hpk
      · exact hT pk hpk
      · rw [List.mem_singleton.mp hpk]
        exact ⟨hp, hdp, hdiff.mp h2, hdk⟩
    · rw [hcs, List.map_append, List.map_singleton]
      rfl
    · rw [← Option.some.inj h]
      simp [val]

theorem filterMap_of_some {α β : Type} (g : α → Option β) (v : α → β) :
    ∀ T : List α, (∀ x ∈ T, g x = some (v x)) → T.filterMap g = T.map v
  | [], _ => rfl
  | x :: T, h => by
    rw [List.filterMap_cons_some (h x (by simp)), List.map_cons,
      filterMap_of_some g v T fun y hy => h y (by simp [hy])]

theorem digit_ne {c d : Char} (hc : c.isDigit = true) (hd : d.isDigit = false) : c ≠ d := by
  rintro rfl
  rw [hc] at hd
  exact absurd hd (by decide)

theorem tok_split {p k : List Char} (hp : Dig p) (hk : Dig k) : (p ++ ',' :: k).splitOn ',' = [p, k] := by
  have e : p ++ ',' :: k = [','].intercalate [p, k] := by simp
  rw [e, List.splitOn_intercalate ',' _ (by simp)]
  intro l hl hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact digit_ne (hp _ hmem) (by decide) rfl
  · exact digit_ne (hk _ hmem) (by decide) rfl

theorem parsePairs_render {T : List (List Char × List Char)} (hne : T ≠ [])
    (hT : ∀ pk ∈ T, Good pk) :
    parsePairs (String.ofList ([' '].intercalate (T.map tok))) = T.map val := by
  unfold parsePairs
  have hsp : (" " : String) = String.singleton ' ' := by decide
  have hco : ("," : String) = String.singleton ',' := by decide
  rw [hsp, splitOn_ofList, List.splitOn_intercalate ' ' ?_ (by simpa using hne), List.map_map,
    List.filterMap_map]
  · apply filterMap_of_some
    intro pk hpk
    obtain ⟨hp, hdp, hk, hdk⟩ := hT pk hpk
    simp only [Function.comp, tok]
    rw [hco, splitOn_ofList, tok_split hdp hdk]
    simp only [List.map_cons, List.map_nil, toNat!_ofList hp hdp, toNat!_ofList hk hdk, val]
  · intro l hl hmem
    obtain ⟨pk, hpk, rfl⟩ := List.mem_map.mp hl
    obtain ⟨-, hdp, -, hdk⟩ := hT pk hpk
    rcases List.mem_append.mp hmem with h | h
    · exact digit_ne (hdp _ h) (by decide) rfl
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h (by decide)
      · exact digit_ne (hdk _ h) (by decide) rfl

theorem parseK_sound {cs : List Char} {l : List (Nat × Nat)} (h : parseK cs = some l) :
    l = parsePairs (String.ofList cs) := by
  obtain ⟨T, hne, hT, rfl, rfl⟩ := parseK_shape h
  exact (parsePairs_render hne hT).symm

end CFSG.KC.LQT.T2

end
