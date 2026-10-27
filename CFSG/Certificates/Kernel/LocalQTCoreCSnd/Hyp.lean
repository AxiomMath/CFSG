module

public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.EBfs
public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.EK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert

public section

namespace CFSG.KC.LQT.Syl.CoreSnd

open Equiv CFSG.KC.LQT CFSG.QuasithinUnique.A5.Kc3Cert
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {n : ℕ}

private def kpw_Wf (v : ℕ → ℕ) (u : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if u.testBit k = true then kpw_Wf v u k ^^^ v k else kpw_Wf v u k

private theorem kpw_Wf_succ (v : ℕ → ℕ) (u k : ℕ) :
    kpw_Wf v u (k + 1) = if u.testBit k = true then kpw_Wf v u k ^^^ v k else kpw_Wf v u k :=
  rfl

private theorem kpw_Wf_zero (v : ℕ → ℕ) (u : ℕ) : kpw_Wf v u 0 = 0 := rfl

private theorem kpw_letN (y : ℕ) (k : ℕ → ℕ) : Syl.letN y k = k y := by
  cases y <;> rfl

private theorem kpw_shl (a k : ℕ) : Nat.shiftLeft a k = a * 2 ^ k := Nat.shiftLeft_eq a k

private theorem kpw_or_low {X k S : ℕ} (hX : X < 2 ^ k) : X ||| S * 2 ^ k = X + S * 2 ^ k := by
  rw [Nat.mul_comm, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hX S, Nat.add_comm]

private theorem kpw_xor_lc (a b c : ℕ) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

private theorem kpw_V_eq {a0 a1 a2 a3 : ℕ} (h0 : a0 < 16) (h1 : a1 < 16) (h2 : a2 < 16)
    (h3 : a3 < 16) :
    Nat.lor (Nat.shiftLeft a0 (Nat.mul 4 0)) (Nat.lor (Nat.shiftLeft a1 (Nat.mul 4 1))
      (Nat.lor (Nat.shiftLeft a2 (Nat.mul 4 2)) (Nat.lor (Nat.shiftLeft a3 (Nat.mul 4 3)) 0))) =
      a0 + 16 * (a1 + 16 * (a2 + 16 * a3)) := by
  have T3 : a2 * 2 ^ 8 ||| a3 * 2 ^ 12 = (a2 + 16 * a3) * 2 ^ 8 := by
    have hX : a2 * 2 ^ 8 < 2 ^ 12 := by norm_num; omega
    rw [kpw_or_low hX]; ring
  have T1 : a1 * 2 ^ 4 ||| (a2 + 16 * a3) * 2 ^ 8 = (a1 + 16 * (a2 + 16 * a3)) * 2 ^ 4 := by
    have hX : a1 * 2 ^ 4 < 2 ^ 8 := by norm_num; omega
    rw [kpw_or_low hX]; ring
  have T0 : a0 * 2 ^ 0 ||| (a1 + 16 * (a2 + 16 * a3)) * 2 ^ 4 =
      a0 + 16 * (a1 + 16 * (a2 + 16 * a3)) := by
    have hX : a0 * 2 ^ 0 < 2 ^ 4 := by norm_num; omega
    rw [kpw_or_low hX]; ring
  rw [show Nat.mul 4 0 = 0 from rfl, show Nat.mul 4 1 = 4 from rfl,
    show Nat.mul 4 2 = 8 from rfl, show Nat.mul 4 3 = 12 from rfl,
    Nat.lor_eq, Nat.lor_eq, Nat.lor_eq, Nat.lor_eq, kpw_shl, kpw_shl, kpw_shl, kpw_shl,
    Nat.or_zero, T3, T1, T0]

private theorem kpw_fold_four (c : Perm (Fin n) → ℕ) (g : ℕ → ℕ) (x0 x1 x2 x3 : Perm (Fin n)) :
    List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
      (fun b _ ih j => Nat.lor (Nat.shiftLeft (g b) (Nat.mul 4 j)) (ih (Nat.succ j)))
      (List.map c [x0, x1, x2, x3]) 0 =
    Nat.lor (Nat.shiftLeft (g (c x0)) (Nat.mul 4 0)) (Nat.lor (Nat.shiftLeft (g (c x1)) (Nat.mul 4 1))
      (Nat.lor (Nat.shiftLeft (g (c x2)) (Nat.mul 4 2))
        (Nat.lor (Nat.shiftLeft (g (c x3)) (Nat.mul 4 3)) 0))) :=
  rfl

private theorem kpw_four {B : List (Perm (Fin n))} (hB : B.length = 4) :
    ∃ b0 b1 b2 b3, B = [b0, b1, b2, b3] := by
  rcases B with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, B⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hB <;>
    first
    | exact ⟨_, _, _, _, rfl⟩
    | omega

private theorem kpw_idxK_cons (x y : ℕ) (l : List ℕ) :
    Syl.idxK x (y :: l) = Bool.rec (motive := fun _ => ℕ) (Nat.succ (Syl.idxK x l)) 0
      (Nat.beq x y) :=
  rfl

private theorem kpw_idxK_get : ∀ (l : List ℕ), l.Nodup → ∀ (i x : ℕ), l[i]? = some x →
    Syl.idxK x l = i
  | [], _, i, x, h => by simp at h
  | y :: l, hnd, 0, x, h => by
    have hxy : y = x := by simpa using h
    subst hxy
    rw [kpw_idxK_cons, Nat.beq_refl]
  | y :: l, hnd, i + 1, x, h => by
    have h' : l[i]? = some x := h
    have hx : x ∈ l := List.mem_of_getElem? h'
    have hne : x ≠ y := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hx)
    have hb : Nat.beq x y = false := by
      cases hc : Nat.beq x y
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hc) hne
    rw [kpw_idxK_cons, hb]
    have := kpw_idxK_get l (List.nodup_cons.1 hnd).2 i x h'
    show Nat.succ (Syl.idxK x l) = i + 1
    omega

private theorem kpw_idxK_elt {B : List (Perm (Fin n))} (hn : n ≤ 32) (h : EFacts B) {m : ℕ}
    (hm : m < 16) : Syl.idxK (P.code (elt 4 B m)) ((lst B).map P.code) = m := by
  refine kpw_idxK_get _ (List.Nodup.map (fun a b hab => P.code_inj hn hab) h.nodup) m _ ?_
  simp [lst, List.getElem?_range hm]

private theorem kpw_idx (hn : n ≤ 32) {B : List (Perm (Fin n))} (h : EFacts B) (σ b : Perm (Fin n))
    {m : ℕ} (hm : m < 16) (e : σ * b * σ⁻¹ = elt 4 B m) :
    Syl.idxK (P.mul n (P.mul n (P.code σ) (P.code b)) (P.code σ⁻¹)) ((lst B).map P.code) = m := by
  rw [P.code_mul hn, P.code_mul hn, e]
  exact kpw_idxK_elt hn h hm

private theorem kpw_beq_one (x : ℕ) : Nat.beq x 1 = decide (x = 1) := by
  by_cases h : x = 1
  · subst h; rfl
  · have hf : Nat.beq x 1 = false := by
      cases hc : Nat.beq x 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hc) h
    rw [hf, decide_eq_false h]

private theorem kpw_bitK (u j : ℕ) : Syl.bitK u j = u.testBit j := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  show Nat.beq ((u >>> j) % 2) 1 = decide (u / 2 ^ j % 2 = 1)
  rw [kpw_beq_one, Nat.shiftRight_eq_div_pow]

private noncomputable def kpw_G (V u j x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) x (x ^^^ ((V >>> (4 * j)) % 16)) (Syl.bitK u j)

private theorem kpw_G_eq (V u : ℕ) (v : ℕ → ℕ) (j x : ℕ) (hV : (V >>> (4 * j)) % 16 = v j) :
    kpw_G V u j x = if u.testBit j = true then x ^^^ v j else x := by
  unfold kpw_G
  rw [hV, kpw_bitK]
  cases h : u.testBit j <;> simp [h]

private theorem kpw_linK (V u : ℕ) (v : ℕ → ℕ) (hV : ∀ j < 4, (V >>> (4 * j)) % 16 = v j) :
    Syl.linK V u = kpw_Wf v u 4 := by
  have e : Syl.linK V u = kpw_G V u 0 (kpw_G V u 1 (kpw_G V u 2 (kpw_G V u 3 0))) := rfl
  have w4 : kpw_Wf v u 4 =
      if u.testBit 3 = true then kpw_Wf v u 3 ^^^ v 3 else kpw_Wf v u 3 := rfl
  have w3 : kpw_Wf v u 3 =
      if u.testBit 2 = true then kpw_Wf v u 2 ^^^ v 2 else kpw_Wf v u 2 := rfl
  have w2 : kpw_Wf v u 2 =
      if u.testBit 1 = true then kpw_Wf v u 1 ^^^ v 1 else kpw_Wf v u 1 := rfl
  have w1 : kpw_Wf v u 1 =
      if u.testBit 0 = true then kpw_Wf v u 0 ^^^ v 0 else kpw_Wf v u 0 := rfl
  rw [e, kpw_G_eq V u v 0 _ (hV 0 (by norm_num)), kpw_G_eq V u v 1 _ (hV 1 (by norm_num)),
    kpw_G_eq V u v 2 _ (hV 2 (by norm_num)), kpw_G_eq V u v 3 _ (hV 3 (by norm_num)),
    w4, w3, w2, w1, kpw_Wf_zero]
  cases h0 : u.testBit 0 <;> cases h1 : u.testBit 1 <;> cases h2 : u.testBit 2 <;>
    cases h3 : u.testBit 3 <;>
    simp [h0, h1, h2, h3, Nat.xor_assoc, Nat.xor_comm, kpw_xor_lc]

private theorem kpw_conj {B : List (Perm (Fin n))} (h : EFacts B) (σ : Perm (Fin n)) (v : ℕ → ℕ)
    (hv : ∀ j < 4, σ * B.getD j 1 * σ⁻¹ = elt 4 B (v j)) :
    ∀ k, k ≤ 4 → ∀ u, σ * elt k B u * σ⁻¹ = elt 4 B (kpw_Wf v u k) := by
  have hs : ∀ i, B.getD i 1 * B.getD i 1 = 1 := fun i => h.sq' i
  have hc : ∀ i j, B.getD i 1 * B.getD j 1 = B.getD j 1 * B.getD i 1 := fun i j => h.comm' i j
  have cm : ∀ a b : Perm (Fin n), σ * (a * b) * σ⁻¹ = σ * a * σ⁻¹ * (σ * b * σ⁻¹) := by
    intro a b
    simp only [mul_assoc, inv_mul_cancel_left]
  intro k
  induction k with
  | zero =>
    intro _ u
    have h0 : elt 0 B u = 1 := rfl
    rw [h0, mul_one, mul_inv_cancel, kpw_Wf_zero, elt_zero]
  | succ k ih =>
    intro hk u
    have ihk := ih (by omega) u
    have hk' : k < 4 := by omega
    rw [elt_succ, kpw_Wf_succ]
    by_cases hb : u.testBit k = true
    · rw [if_pos hb, if_pos hb, cm, ihk, hv k hk', elt_mul hs hc]
    · rw [if_neg hb, if_neg hb, mul_one, ihk]

private theorem kpw_Wf_lt (v : ℕ → ℕ) (hv : ∀ j < 4, v j < 16) (u : ℕ) :
    ∀ k, k ≤ 4 → kpw_Wf v u k < 16 := by
  intro k
  induction k with
  | zero => intro _; rw [kpw_Wf_zero]; norm_num
  | succ k ih =>
    intro hk
    have h1 : kpw_Wf v u k < 16 := ih (by omega)
    rw [kpw_Wf_succ]
    split
    · have h2 : v k < 16 := hv k (by omega)
      have h3 := Nat.xor_lt_two_pow (n := 4) (x := kpw_Wf v u k) (y := v k)
        (by norm_num; omega) (by norm_num; omega)
      exact lt_of_lt_of_eq h3 (by norm_num)
    · exact h1

private theorem kpw_elt_inj {B : List (Perm (Fin n))} (h : EFacts B) {m m' : ℕ} (hm : m < 16)
    (hm' : m' < 16) (e : elt 4 B m = elt 4 B m') : m = m' := by
  have hnd : ((List.range 16).map (elt 4 B)).Nodup := h.nodup
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hm) (List.mem_range.2 hm') e

private theorem kpw_cm {B : List (Perm (Fin n))} (h : EFacts B) (σ : Perm (Fin n)) (v : ℕ → ℕ)
    (hv1 : ∀ j < 4, v j < 16) (hv2 : ∀ j < 4, σ * B.getD j 1 * σ⁻¹ = elt 4 B (v j)) (u : ℕ)
    (hu : u < 16) : Cm B σ u ↔ kpw_Wf v u 4 = u := by
  have hc4 := kpw_conj h σ v hv2 4 le_rfl u
  unfold Cm
  rw [← mul_inv_eq_iff_eq_mul, hc4]
  exact ⟨fun e => kpw_elt_inj h (kpw_Wf_lt v hv1 u 4 le_rfl) hu e, fun e => by rw [e]⟩

private theorem kpw_listrec (g : ℕ → ℕ) : ∀ (l : List ℕ),
    List.rec (motive := fun _ => ℕ) 0 (fun u _ ih => Nat.add ih (g u)) l = (l.map g).sum
  | [] => rfl
  | u :: l => by
    have ih := kpw_listrec g l
    show Nat.add (List.rec (motive := fun _ => ℕ) 0 (fun u _ ih => Nat.add ih (g u)) l) (g u) =
      ((u :: l).map g).sum
    rw [ih, List.map_cons, List.sum_cons, Nat.add_eq, Nat.add_comm]

private theorem kpw_range_sum (g : ℕ → ℕ) (N : ℕ) :
    ((List.range N).map g).sum = ∑ u ∈ Finset.range N, g u := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem kpw_main {B : List (Perm (Fin n))} (h : EFacts B) (σ : Perm (Fin n)) (v : ℕ → ℕ)
    (hv1 : ∀ j < 4, v j < 16) (hv2 : ∀ j < 4, σ * B.getD j 1 * σ⁻¹ = elt 4 B (v j)) (V : ℕ)
    (hV : ∀ j < 4, (V >>> (4 * j)) % 16 = v j) :
    List.rec (motive := fun _ => ℕ) 0 (fun u _ ih => Nat.add ih
      (Bool.rec (motive := fun _ => ℕ) 0 (Nat.pow 2 u) (Nat.beq u (Syl.linK V u))))
      (List.range 16) =
      ∑ u ∈ (Finset.range 16).filter (fun u => Cm B σ u), 2 ^ u := by
  rw [kpw_listrec, kpw_range_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu16 : u < 16 := Finset.mem_range.1 hu
  rw [kpw_linK V u v hV]
  by_cases hc : Cm B σ u
  · have he : kpw_Wf v u 4 = u := (kpw_cm h σ v hv1 hv2 u hu16).1 hc
    have hb : Nat.beq u (kpw_Wf v u 4) = true := by
      rw [he]; exact Nat.beq_refl u
    rw [if_pos hc, hb] <;> rfl
  · have he : ¬ kpw_Wf v u 4 = u := fun e => hc ((kpw_cm h σ v hv1 hv2 u hu16).2 e)
    have hb : Nat.beq u (kpw_Wf v u 4) = false := by
      cases hc' : Nat.beq u (kpw_Wf v u 4)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hc').symm he
    rw [if_neg hc, hb] <;> rfl

theorem cmLK_eq (hn : n ≤ 32) {B : List (Perm (Fin n))} (h : EFacts B) (σ : Perm (Fin n))
    (hσ : ∀ e ∈ B, ∃ e' ∈ lst B, σ * e = e' * σ) :
    Syl.cmLK n (B.map P.code) (Syl.lstK n 4 (B.map P.code)) (P.code σ) =
      ∑ u ∈ (Finset.range 16).filter (fun u => Cm B σ u), 2 ^ u := by
  have key : ∀ j < 4, ∃ m < 16, σ * B.getD j 1 * σ⁻¹ = elt 4 B m := by
    intro j hj
    have hlt : j < B.length := by rw [h.len]; exact hj
    have hmem : B.getD j 1 ∈ B := by
      obtain ⟨x, hx⟩ : ∃ x, B[j]? = some x := ⟨B[j], List.getElem?_eq_getElem hlt⟩
      rw [List.getD_eq_getElem?_getD, hx, Option.getD_some]
      exact List.mem_of_getElem? hx
    obtain ⟨e', he', hσe⟩ := hσ _ hmem
    obtain ⟨m, hm, rfl⟩ := mem_lst_iff.1 he'
    exact ⟨m, hm, by rw [hσe, mul_assoc, mul_inv_cancel, mul_one]⟩
  choose! v hv1 hv2 using key
  rw [lstK_code hn B]
  unfold Syl.cmLK
  simp only [kpw_letN]
  rw [P.code_inv hn σ]
  obtain ⟨b0, b1, b2, b3, rfl⟩ := kpw_four h.len
  have e0 := kpw_idx hn h σ b0 (hv1 0 (by norm_num)) (hv2 0 (by norm_num))
  have e1 := kpw_idx hn h σ b1 (hv1 1 (by norm_num)) (hv2 1 (by norm_num))
  have e2 := kpw_idx hn h σ b2 (hv1 2 (by norm_num)) (hv2 2 (by norm_num))
  have e3 := kpw_idx hn h σ b3 (hv1 3 (by norm_num)) (hv2 3 (by norm_num))
  have w0 := hv1 0 (by norm_num)
  have w1 := hv1 1 (by norm_num)
  have w2 := hv1 2 (by norm_num)
  have w3 := hv1 3 (by norm_num)
  refine kpw_main h σ v hv1 hv2 _ ?_
  intro j hj
  rw [kpw_fold_four, e0, e1, e2, e3, kpw_V_eq w0 w1 w2 w3]
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  all_goals simp only [Nat.shiftRight_eq_div_pow]
  all_goals (try norm_num)
  all_goals omega

private theorem kpw_bitK_iff (m i : ℕ) : Syl.bitK m i = true ↔ m.testBit i = true := by
  unfold Syl.bitK
  have e : Nat.shiftRight m i = m / 2 ^ i := Nat.shiftRight_eq_div_pow m i
  rw [P.beq_iff, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  change (Nat.shiftRight m i) % 2 = 1 ↔ _
  rw [e]

theorem tvK_iff (m : ℕ) :
    Syl.tvK m = true ↔ ∃ u < 16, m.testBit u = false ∧
      ∀ y < 16, m.testBit y = true ∨ m.testBit (u ^^^ y) = true := by
  unfold Syl.tvK
  rw [P.anyL_iff]
  refine ⟨fun ⟨u, hu, h⟩ => ?_, fun ⟨u, hu, h1, h2⟩ => ?_⟩
  · rw [P.andB_iff, P.notB_iff, P.allL_iff] at h
    refine ⟨u, List.mem_range.1 hu, ?_, fun y hy => ?_⟩
    · exact Bool.eq_false_iff.2 fun hb => h.1 ((kpw_bitK_iff m u).2 hb)
    · have := h.2 y (List.mem_range.2 hy)
      rw [P.orB_iff, kpw_bitK_iff, kpw_bitK_iff] at this
      exact this
  · refine ⟨u, List.mem_range.2 hu, ?_⟩
    rw [P.andB_iff, P.notB_iff, P.allL_iff]
    refine ⟨fun hb => ?_, fun y hy => ?_⟩
    · have := (kpw_bitK_iff m u).1 hb
      rw [h1] at this
      exact Bool.false_ne_true this
    · rw [P.orB_iff, kpw_bitK_iff, kpw_bitK_iff]
      exact h2 y (List.mem_range.1 hy)

theorem hypAx_sound (hn : n ≤ 32) {B : List (Perm (Fin n))} (h : EFacts B) (σ : Perm (Fin n))
    (hσ : ∀ e ∈ B, ∃ e' ∈ lst B, σ * e = e' * σ)
    (hx : Syl.hypAx n (B.map P.code) (P.code σ) = true) :
    (¬ ∃ u < 16, ¬ Cm B σ u ∧ ∀ y < 16, Cm B σ y ∨ Cm B σ (u ^^^ y)) ∧
      ((∀ u < 16, Cm B σ u) → σ ∈ lst B) := by
  unfold Syl.hypAx at hx
  rw [P.letB_eq, P.andB_iff, P.notB_iff, P.impB_iff, cmLK_eq hn h σ hσ] at hx
  obtain ⟨hnt, himp⟩ := hx
  set Sf := (Finset.range 16).filter (fun u => Cm B σ u) with hSf
  set m := ∑ u ∈ Sf, 2 ^ u with hm
  have hbit : ∀ u < 16, m.testBit u = true ↔ Cm B σ u := fun u hu => by
    rw [hm, testBit_sum_pow, decide_eq_true_iff, hSf, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
  refine ⟨?_, fun hall => ?_⟩
  · rintro ⟨u, hu, hnu, hy⟩
    apply hnt
    rw [tvK_iff]
    refine ⟨u, hu, ?_, fun y hy' => ?_⟩
    · exact Bool.eq_false_iff.2 fun hb => hnu ((hbit u hu).1 hb)
    · rcases hy y hy' with h1 | h1
      · exact Or.inl ((hbit y hy').2 h1)
      · exact Or.inr ((hbit _ (Nat.xor_lt_two_pow (n := 4) hu hy')).2 h1)
  · have hSf16 : Sf = Finset.range 16 := by
      rw [hSf]
      exact Finset.filter_true_of_mem fun u hu => hall u (Finset.mem_range.1 hu)
    have h65 : m = 65535 := by
      rw [hm, hSf16]
      decide
    have := himp (P.beq_iff.2 h65)
    rwa [lstK_code hn, CFSG.KC.LQT.S.memL_iff, P.mem_map_code hn] at this

private theorem kpw_comm_iff (σ a : Perm (Fin n)) :
    RN.enc σ * RN.enc a = RN.enc a * RN.enc σ ↔ σ * a = a * σ := by
  rw [← RN.enc_mul, ← RN.enc_mul]
  exact RN.enc_inj.eq_iff

private theorem kpw_enc_mul_elt {B : List (Perm (Fin n))} (h : EFacts B) (u y : ℕ) :
    RN.enc (elt 4 B u) * RN.enc (elt 4 B y) = RN.enc (elt 4 B (u ^^^ y)) := by
  rw [← RN.enc_mul, elt_mul h.sq' h.comm' 4 u y]

private theorem kpw_mem_El {B : List (Perm (Fin n))} (h : EFacts B) (e : RN n) :
    e ∈ (bfsSet (B.map RN.enc) 16).toList ↔ ∃ m < 16, RN.enc (elt 4 B m) = e := by
  rw [Std.HashSet.mem_toList, es_mem h e]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨m, hm, rfl⟩ := mem_lst_iff.mp ha
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨elt 4 B m, mem_lst_iff.mpr ⟨m, hm, rfl⟩, rfl⟩

theorem isTransvecB_iff {B : List (Perm (Fin n))} (h : EFacts B) (σ : Perm (Fin n)) :
    isTransvecB (bfsSet (B.map RN.enc) 16).toList (RN.enc σ) = true ↔
      ∃ u < 16, ¬ Cm B σ u ∧ ∀ y < 16, Cm B σ y ∨ Cm B σ (u ^^^ y) := by
  unfold isTransvecB
  simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨e, he, hne, hall⟩
    obtain ⟨u, hu, rfl⟩ := (kpw_mem_El h e).mp he
    refine ⟨u, hu, fun hC => hne ((kpw_comm_iff σ (elt 4 B u)).mpr hC), fun y hy => ?_⟩
    rcases hall (RN.enc (elt 4 B y)) ((kpw_mem_El h _).mpr ⟨y, hy, rfl⟩) with hc | hc
    · exact Or.inl ((kpw_comm_iff σ (elt 4 B y)).mp hc)
    · refine Or.inr ((kpw_comm_iff σ (elt 4 B (u ^^^ y))).mp ?_)
      rw [← kpw_enc_mul_elt h u y]
      exact hc
  · rintro ⟨u, hu, hnc, hall⟩
    refine ⟨RN.enc (elt 4 B u), (kpw_mem_El h _).mpr ⟨u, hu, rfl⟩,
      fun heq => hnc ((kpw_comm_iff σ (elt 4 B u)).mp heq), fun e he => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (kpw_mem_El h e).mp he
    rcases hall y hy with hc | hc
    · exact Or.inl ((kpw_comm_iff σ (elt 4 B y)).mpr hc)
    · refine Or.inr ?_
      rw [kpw_enc_mul_elt h u y]
      exact (kpw_comm_iff σ (elt 4 B (u ^^^ y))).mpr hc

theorem selfCent_iff {B : List (Perm (Fin n))} (h : EFacts B) (σ : Perm (Fin n)) :
    ((!((bfsSet (B.map RN.enc) 16).toList.all fun e => RN.enc σ * e == e * RN.enc σ)) ||
        (bfsSet (B.map RN.enc) 16).contains (RN.enc σ)) = true ↔
      ((∀ u < 16, Cm B σ u) → σ ∈ lst B) := by
  have hP : ((bfsSet (B.map RN.enc) 16).toList.all fun e => RN.enc σ * e == e * RN.enc σ) = true ↔
      ∀ u < 16, Cm B σ u := by
    rw [List.all_eq_true]
    constructor
    · intro hall u hu
      have hb : (RN.enc σ * RN.enc (elt 4 B u) == RN.enc (elt 4 B u) * RN.enc σ) = true :=
        hall (RN.enc (elt 4 B u)) ((kpw_mem_El h _).mpr ⟨u, hu, rfl⟩)
      exact (kpw_comm_iff σ (elt 4 B u)).mp (beq_iff_eq.mp hb)
    · intro hall e he
      obtain ⟨u, hu, rfl⟩ := (kpw_mem_El h e).mp he
      exact beq_iff_eq.mpr ((kpw_comm_iff σ (elt 4 B u)).mpr (hall u hu))
  have hQ : (bfsSet (B.map RN.enc) 16).contains (RN.enc σ) = true ↔ σ ∈ lst B := by
    rw [Std.HashSet.contains_iff_mem, es_mem h]
    constructor
    · rintro ⟨a, ha, hae⟩
      obtain rfl := RN.enc_inj hae
      exact ha
    · intro hσ
      exact ⟨σ, hσ, rfl⟩
  have key : ∀ P Q : Bool, ((!P || Q) = true ↔ (P = true → Q = true)) := by
    decide
  exact (key _ _).trans (Iff.imp hP hQ)

end CFSG.KC.LQT.Syl.CoreSnd

end
