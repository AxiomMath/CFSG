module

public import CFSG.Certificates.Kernel.J4TreeTop.WalkSound
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT

inductive XSpan (vs : List ℕ) : ℕ → Prop
  | zero : XSpan vs 0
  | add {t v : ℕ} : XSpan vs t → v ∈ vs → XSpan vs (t ^^^ v)

@[expose] def xm : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: L, m => (if m % 2 = 1 then c else 0) ^^^ xm L (m / 2)

theorem xm_cons (c : ℕ) (L : List ℕ) (m : ℕ) :
    xm (c :: L) m = (if m % 2 = 1 then c else 0) ^^^ xm L (m / 2) := rfl

theorem xm_zero : ∀ L : List ℕ, xm L 0 = 0
  | [] => rfl
  | c :: L => by rw [xm_cons, xm_zero L]; simp

theorem xor4 (a u c v : ℕ) : (a ^^^ u) ^^^ (c ^^^ v) = (a ^^^ c) ^^^ (u ^^^ v) :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor]
    cases a.testBit i <;> cases u.testBit i <;> cases c.testBit i <;> cases v.testBit i <;> rfl

theorem xm_xor : ∀ (L : List ℕ) (I J : ℕ), xm L (I ^^^ J) = xm L I ^^^ xm L J
  | [], _, _ => by simp [xm]
  | c :: L, I, J => by
    have e1 : (I ^^^ J) / 2 = I / 2 ^^^ J / 2 :=
      Nat.eq_of_testBit_eq fun i => by simp only [← Nat.testBit_succ, Nat.testBit_xor]
    have e2 : (I ^^^ J) % 2 = (I % 2 + J % 2) % 2 := by
      have h := Nat.testBit_xor I J 0
      simp only [Nat.testBit_zero] at h
      rcases Nat.mod_two_eq_zero_or_one I with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one J with h2 | h2 <;>
        rcases Nat.mod_two_eq_zero_or_one (I ^^^ J) with h3 | h3 <;> simp_all
    rw [xm_cons, xm_cons, xm_cons, e1, xm_xor L, e2, xor4]
    rcases Nat.mod_two_eq_zero_or_one I with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one J with h2 | h2 <;> simp [h1, h2]

theorem xm_two_pow : ∀ (L : List ℕ) (i : ℕ) (hi : i < L.length), xm L (2 ^ i) = L[i]
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | c :: L, 0, _ => by rw [xm_cons]; simp [xm_zero]
  | c :: L, i + 1, hi => by
    have h1 : 2 ^ (i + 1) % 2 = 0 := by rw [pow_succ]; exact Nat.mul_mod_left _ _
    have h2 : 2 ^ (i + 1) / 2 = 2 ^ i := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [xm_cons, h1, h2, xm_two_pow L i (by simpa using hi)]
    simp

theorem xm_mod : ∀ (L : List ℕ) (I : ℕ), xm L I = xm L (I % 2 ^ L.length)
  | [], _ => rfl
  | c :: L, I => by
    rw [xm_cons, xm_cons, xm_mod L (I / 2), List.length_cons, pow_succ',
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd I (Dvd.intro _ rfl)]

theorem xm_append : ∀ (L L' : List ℕ) (I : ℕ), xm (L ++ L') I = xm L I ^^^ xm L' (I / 2 ^ L.length)
  | [], L', I => by simp [xm]
  | c :: L, L', I => by
    rw [List.cons_append, xm_cons, xm_cons, xm_append L L' (I / 2), Nat.div_div_eq_div_mul,
      List.length_cons, pow_succ', Nat.xor_assoc]

theorem xm_append_ex (L L' : List ℕ) (I : ℕ) : ∃ J, xm (L ++ L') I = xm L I ^^^ xm L' J :=
  ⟨_, xm_append L L' I⟩

theorem xm_lt {k : ℕ} : ∀ {L : List ℕ}, (∀ c ∈ L, c < 2 ^ k) → ∀ I, xm L I < 2 ^ k
  | [], _, _ => by simp [xm]
  | c :: L, h, I => by
    rw [xm_cons]
    refine Nat.xor_lt_two_pow ?_ (xm_lt (fun d hd => h d (List.mem_cons_of_mem _ hd)) _)
    split_ifs
    · exact h c List.mem_cons_self
    · positivity

theorem xm_map_lt {φ : ℕ → ℕ} {k : ℕ}
    (hφ : ∀ a < 2 ^ k, ∀ b < 2 ^ k, φ (a ^^^ b) = φ a ^^^ φ b) :
    ∀ {L : List ℕ}, (∀ c ∈ L, c < 2 ^ k) → ∀ I, xm (L.map φ) I = φ (xm L I)
  | [], _, _ => by
    have h0 := hφ 0 (by positivity) 0 (by positivity)
    rw [Nat.xor_self, Nat.xor_self] at h0
    simp [xm, h0]
  | c :: L, h, I => by
    have h0 := hφ 0 (by positivity) 0 (by positivity)
    rw [Nat.xor_self, Nat.xor_self] at h0
    have hL : ∀ d ∈ L, d < 2 ^ k := fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc : c < 2 ^ k := h c List.mem_cons_self
    rw [List.map_cons, xm_cons, xm_cons, xm_map_lt hφ hL (I / 2)]
    split_ifs
    · rw [hφ _ hc _ (xm_lt hL _)]
    · rw [hφ _ (by positivity) _ (xm_lt hL _), h0]

theorem xm_map {φ : ℕ → ℕ} (hφ : ∀ a b, φ (a ^^^ b) = φ a ^^^ φ b) :
    ∀ (L : List ℕ) (I : ℕ), xm (L.map φ) I = φ (xm L I)
  | [], _ => by
    have h0 := hφ 0 0
    rw [Nat.xor_self, Nat.xor_self] at h0
    simp [xm, h0]
  | c :: L, I => by
    have h0 := hφ 0 0
    rw [Nat.xor_self, Nat.xor_self] at h0
    rw [List.map_cons, xm_cons, xm_cons, xm_map hφ L (I / 2), hφ]
    split_ifs
    · rfl
    · rw [h0]

theorem xspan_xm {L : List ℕ} {t : ℕ} (h : XSpan L t) : ∃ I < 2 ^ L.length, xm L I = t := by
  induction h with
  | zero => exact ⟨0, by positivity, xm_zero L⟩
  | @add t v _ hv ih =>
    obtain ⟨I, hI, rfl⟩ := ih
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hv
    exact ⟨I ^^^ 2 ^ p, Nat.xor_lt_two_pow hI (Nat.pow_lt_pow_right (by norm_num) hp),
      by rw [xm_xor, xm_two_pow L p hp]⟩

theorem xspan_xor {vs : List ℕ} {a b : ℕ} (ha : XSpan vs a) (hb : XSpan vs b) :
    XSpan vs (a ^^^ b) := by
  induction hb with
  | zero => rwa [Nat.xor_zero]
  | add _ hv ih =>
    rw [← Nat.xor_assoc]
    exact XSpan.add ih hv

theorem xspan_mono {vs ws : List ℕ} (h : ∀ v ∈ vs, v ∈ ws) {a : ℕ} (ha : XSpan vs a) :
    XSpan ws a := by
  induction ha with
  | zero => exact XSpan.zero
  | add _ hv ih => exact XSpan.add ih (h _ hv)

theorem xspan_of_mem {vs : List ℕ} {v : ℕ} (hv : v ∈ vs) : XSpan vs v := by
  have h := XSpan.add XSpan.zero hv
  rwa [Nat.zero_xor] at h

theorem xspan_lt {vs : List ℕ} {k : ℕ} (h : ∀ v ∈ vs, v < 2 ^ k) {a : ℕ} (ha : XSpan vs a) :
    a < 2 ^ k := by
  induction ha with
  | zero => positivity
  | add _ hv ih => exact Nat.xor_lt_two_pow ih (h _ hv)

theorem xspan_cons {b : ℕ} {B : List ℕ} {x : ℕ} (hx : XSpan (b :: B) x) :
    ∃ s, XSpan B s ∧ (x = s ∨ x = s ^^^ b) := by
  induction hx with
  | zero => exact ⟨0, XSpan.zero, Or.inl rfl⟩
  | @add t v _ hv ih =>
    obtain ⟨s, hs, hx⟩ := ih
    rcases List.mem_cons.mp hv with hvb | hv
    · rw [hvb]
      rcases hx with h | h
      · exact ⟨s, hs, Or.inr (by rw [h])⟩
      · exact ⟨s, hs, Or.inl (by rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero])⟩
    · rcases hx with h | h
      · exact ⟨s ^^^ v, XSpan.add hs hv, Or.inl (by rw [h])⟩
      · refine ⟨s ^^^ v, XSpan.add hs hv, Or.inr ?_⟩
        rw [h, Nat.xor_assoc, Nat.xor_comm b v, ← Nat.xor_assoc]

theorem testBit_gt_log2 {b j : ℕ} (hj : b.log2 < j) : b.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) hj))

theorem xor_lt_iff_log2 {v b : ℕ} (hb : b ≠ 0) : v ^^^ b < v ↔ v.testBit b.log2 = true := by
  have hbk := Nat.testBit_log2 hb
  have hhi : ∀ j, b.log2 < j → (v ^^^ b).testBit j = v.testBit j := fun j hj => by
    rw [Nat.testBit_xor, testBit_gt_log2 hj, Bool.xor_false]
  constructor
  · intro h
    by_contra hv
    rw [Bool.not_eq_true] at hv
    have h2 : v < v ^^^ b := Nat.lt_of_testBit b.log2 hv
      (by rw [Nat.testBit_xor, hv, hbk]; rfl) (fun j hj => (hhi j hj).symm)
    omega
  · intro hv
    exact Nat.lt_of_testBit b.log2 (by rw [Nat.testBit_xor, hv, hbk]; rfl) hv hhi

theorem log2_le_of_le {a b : ℕ} (ha : a ≠ 0) (h : a ≤ b) : a.log2 ≤ b.log2 :=
  (Nat.le_log2 (by omega)).2 (le_trans (Nat.log2_self_le ha) h)

abbrev EchS (B : List ℕ) : Prop := B.Pairwise (fun a b => b.log2 < a.log2) ∧ ∀ b ∈ B, b ≠ 0

theorem redV_testBit_keep {k : ℕ} : ∀ (B : List ℕ) (v : ℕ), (∀ b ∈ B, b < 2 ^ k) →
    (redV B v).testBit k = v.testBit k
  | [], _, _ => rfl
  | b :: B, v, h => by
    rw [redV, redV_testBit_keep B _ (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    split
    · rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (h b List.mem_cons_self), Bool.xor_false]
    · rfl

theorem redV_clear : ∀ (B : List ℕ) (v : ℕ), EchS B → ∀ b ∈ B, (redV B v).testBit b.log2 = false
  | [], _, _, _, hb => absurd hb List.not_mem_nil
  | b :: B, v, ⟨hp, hz⟩, c, hc => by
    have hB : EchS B :=
      ⟨(List.pairwise_cons.mp hp).2, fun d hd => hz d (List.mem_cons_of_mem _ hd)⟩
    rw [redV]
    rcases List.mem_cons.mp hc with rfl | hc
    · have hb0 := hz c List.mem_cons_self
      have hlow : ∀ d ∈ B, d < 2 ^ c.log2 := fun d hd =>
        (Nat.log2_lt (hz d (List.mem_cons_of_mem _ hd))).1 ((List.pairwise_cons.mp hp).1 d hd)
      rw [redV_testBit_keep B _ hlow]
      by_cases h : v ^^^ c < v
      · rw [if_pos (by simpa using h), Nat.testBit_xor, (xor_lt_iff_log2 hb0).1 h,
          Nat.testBit_log2 hb0]
        rfl
      · rw [if_neg (by simpa using h)]
        exact Bool.eq_false_iff.mpr (fun h' => h ((xor_lt_iff_log2 hb0).2 h'))
    · exact redV_clear B _ hB c hc

theorem redV_mem {P : ℕ → Prop} (hP : ∀ a b, P a → P b → P (a ^^^ b)) :
    ∀ (B : List ℕ) (v : ℕ), (∀ b ∈ B, P b) → P v → P (redV B v)
  | [], _, _, hv => hv
  | b :: B, v, hB, hv => by
    rw [redV]
    refine redV_mem hP B _ (fun c hc => hB c (List.mem_cons_of_mem _ hc)) ?_
    split
    · exact hP _ _ hv (hB b List.mem_cons_self)
    · exact hv

theorem redV_xspan : ∀ (B : List ℕ) (v : ℕ), XSpan B (redV B v ^^^ v)
  | [], v => by
    rw [redV, Nat.xor_self]
    exact XSpan.zero
  | b :: B, v => by
    rw [redV]
    have hw : ∀ w, (w = v ∨ w = v ^^^ b) → XSpan (b :: B) (redV B w ^^^ v) := by
      intro w hw
      have ih := xspan_mono (fun c hc => List.mem_cons_of_mem b hc) (redV_xspan B w)
      rcases hw with rfl | rfl
      · exact ih
      · have h := xspan_xor ih (xspan_of_mem (List.mem_cons_self (a := b) (l := B)))
        rwa [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h
    exact hw _ (by split <;> simp)

theorem mem_insDesc {r c : ℕ} : ∀ {B : List ℕ}, c ∈ insDesc r B ↔ c = r ∨ c ∈ B
  | [] => by simp [insDesc]
  | b :: B => by
    rw [insDesc]
    split
    · exact List.mem_cons
    · rw [List.mem_cons, mem_insDesc, List.mem_cons]
      exact or_left_comm

theorem length_insDesc (r : ℕ) : ∀ B : List ℕ, (insDesc r B).length = B.length + 1
  | [] => rfl
  | b :: B => by
    rw [insDesc]
    split
    · rfl
    · rw [List.length_cons, length_insDesc r B, List.length_cons]

theorem echS_insDesc {r : ℕ} (hr : r ≠ 0) : ∀ {B : List ℕ}, EchS B →
    (∀ b ∈ B, b.log2 ≠ r.log2) → EchS (insDesc r B)
  | [], _, _ => ⟨List.pairwise_singleton _ _, fun c hc => by
      rw [List.mem_singleton.mp hc]
      exact hr⟩
  | b :: B, ⟨hp, hz⟩, hne => by
    have hb0 := hz b List.mem_cons_self
    obtain ⟨hpb, hpB⟩ := List.pairwise_cons.mp hp
    rw [insDesc]
    split
    · rename_i h
      have hlt : b < r := by simpa using h
      have hl : b.log2 < r.log2 :=
        lt_of_le_of_ne (log2_le_of_le hb0 hlt.le) (hne b List.mem_cons_self)
      refine ⟨List.pairwise_cons.mpr ⟨fun c hc => ?_, hp⟩, fun c hc => ?_⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact hl
        · exact lt_trans (hpb c hc) hl
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact hr
        · exact hz c hc
    · rename_i h
      have hle : r ≤ b := by simpa using h
      have hl : r.log2 < b.log2 :=
        lt_of_le_of_ne (log2_le_of_le hr hle) (hne b List.mem_cons_self).symm
      have ih := echS_insDesc hr ⟨hpB, fun c hc => hz c (List.mem_cons_of_mem _ hc)⟩
        (fun c hc => hne c (List.mem_cons_of_mem _ hc))
      refine ⟨List.pairwise_cons.mpr ⟨fun c hc => ?_, ih.1⟩, fun c hc => ?_⟩
      · rcases mem_insDesc.mp hc with rfl | hc
        · exact hl
        · exact hpb c hc
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact hb0
        · exact ih.2 c hc

theorem redV_log2_ne {B : List ℕ} {v : ℕ} (hE : EchS B) (hr : redV B v ≠ 0) :
    ∀ b ∈ B, b.log2 ≠ (redV B v).log2 := fun b hb he => by
  have h := redV_clear B v hE b hb
  rw [he, Nat.testBit_log2 hr] at h
  exact absurd h (by decide)

theorem echB_cons (B : List ℕ) (v : ℕ) (vs : List ℕ) :
    echB B (v :: vs) = echB (if redV B v = 0 then B else insDesc (redV B v) B) vs := rfl

theorem echB_echS : ∀ (vs B : List ℕ), EchS B → EchS (echB B vs)
  | [], _, h => h
  | v :: vs, B, h => by
    rw [echB_cons]
    split
    · exact echB_echS vs B h
    · rename_i hr
      exact echB_echS vs _ (echS_insDesc hr h (redV_log2_ne h hr))

theorem echB_mem {P : ℕ → Prop} (hP : ∀ a b, P a → P b → P (a ^^^ b)) :
    ∀ (vs B : List ℕ), (∀ b ∈ B, P b) → (∀ v ∈ vs, P v) → ∀ c ∈ echB B vs, P c
  | [], _, hB, _ => hB
  | v :: vs, B, hB, hvs => by
    rw [echB_cons]
    refine echB_mem hP vs _ ?_ (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
    split
    · exact hB
    · intro c hc
      rcases mem_insDesc.mp hc with rfl | hc
      · exact redV_mem hP B v hB (hvs v List.mem_cons_self)
      · exact hB c hc

theorem echB_length_le : ∀ (vs B : List ℕ), (echB B vs).length ≤ B.length + vs.length
  | [], B => by
    rw [List.length_nil, Nat.add_zero]
    exact le_refl _
  | v :: vs, B => by
    rw [echB_cons, List.length_cons]
    split
    · have := echB_length_le vs B
      omega
    · have := echB_length_le vs (insDesc (redV B v) B)
      rw [length_insDesc] at this
      omega

theorem echS_span_zero : ∀ {B : List ℕ}, EchS B → ∀ {x : ℕ}, XSpan B x →
    (∀ b ∈ B, x.testBit b.log2 = false) → x = 0
  | [], _, x, hx, _ => by
    induction hx with
    | zero => rfl
    | add _ hv _ => exact absurd hv List.not_mem_nil
  | b :: B, ⟨hp, hz⟩, x, hx, hbit => by
    obtain ⟨hpb, hpB⟩ := List.pairwise_cons.mp hp
    have hB : EchS B := ⟨hpB, fun c hc => hz c (List.mem_cons_of_mem _ hc)⟩
    obtain ⟨s, hs, hxs⟩ := xspan_cons hx
    have hslt : s < 2 ^ b.log2 :=
      xspan_lt (fun c hc => (Nat.log2_lt (hz c (List.mem_cons_of_mem _ hc))).1 (hpb c hc)) hs
    rcases hxs with rfl | rfl
    · exact echS_span_zero hB hs (fun c hc => hbit c (List.mem_cons_of_mem _ hc))
    · exfalso
      have h := hbit b List.mem_cons_self
      rw [Nat.testBit_xor, Nat.testBit_lt_two_pow hslt, Nat.testBit_log2 (hz b List.mem_cons_self)]
        at h
      exact absurd h (by decide)

theorem spanAll_spec {vs : List ℕ} (h : spanAll vs = true) : ∀ t < 2048, XSpan vs t := by
  unfold spanAll at h
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hlt, hlen⟩ := h
  have hE : EchS (echB [] vs) :=
    echB_echS vs [] ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  have hS : ∀ c ∈ echB [] vs, XSpan vs c ∧ c < 2 ^ 11 :=
    echB_mem (P := fun c => XSpan vs c ∧ c < 2 ^ 11)
      (fun a b ha hb => ⟨xspan_xor ha.1 hb.1, Nat.xor_lt_two_pow ha.2 hb.2⟩) vs []
      (fun _ h => absurd h List.not_mem_nil)
      (fun v hv => ⟨xspan_of_mem hv, Nat.le_of_ble_eq_true (hlt v hv)⟩)
  have hnd : ((echB [] vs).map Nat.log2).Nodup :=
    List.pairwise_map.mpr (hE.1.imp fun h => (ne_of_lt h).symm)
  have hsub : ((echB [] vs).map Nat.log2).toFinset ⊆ Finset.range 11 := by
    intro k hk
    rw [List.mem_toFinset, List.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    exact Finset.mem_range.mpr ((Nat.log2_lt (hE.2 c hc)).2 (hS c hc).2)
  have hall : ∀ k < 11, k ∈ (echB [] vs).map Nat.log2 := by
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen, Finset.card_range])
    intro k hk
    rw [← List.mem_toFinset, heq]
    exact Finset.mem_range.mpr hk
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    by_cases ht0 : t = 0
    · rw [ht0]
      exact XSpan.zero
    · have hk : t.log2 < 11 := (Nat.log2_lt ht0).2 ht
      obtain ⟨b, hb, hbk⟩ := List.mem_map.mp (hall _ hk)
      have hb0 := hE.2 b hb
      have hlt' : t ^^^ b < t :=
        (xor_lt_iff_log2 hb0).2 (by rw [hbk]; exact Nat.testBit_log2 ht0)
      have h2 := xspan_xor (ih _ hlt' (lt_trans hlt' ht)) (hS b hb).1
      rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h2

theorem echB_indep_aux : ∀ (vs B : List ℕ), EchS B →
    (echB B vs).length = B.length + vs.length →
    ∀ I < 2 ^ vs.length, XSpan B (xm vs I) → I = 0
  | [], _, _, _, I, hI, _ => by
    rw [List.length_nil, pow_zero] at hI
    omega
  | v :: vs, B, hE, hlen, I, hI, hx => by
    rw [echB_cons, List.length_cons] at hlen
    by_cases hr : redV B v = 0
    · rw [if_pos hr] at hlen
      have := echB_length_le vs B
      omega
    · rw [if_neg hr] at hlen
      have hE' := echS_insDesc hr hE (redV_log2_ne hE hr)
      have hlen' : (echB (insDesc (redV B v) B) vs).length =
          (insDesc (redV B v) B).length + vs.length := by
        rw [hlen, length_insDesc]
        omega
      have hsub : ∀ c ∈ B, c ∈ insDesc (redV B v) B := fun c hc => mem_insDesc.mpr (Or.inr hc)
      have hrm : redV B v ∈ insDesc (redV B v) B := mem_insDesc.mpr (Or.inl rfl)
      have hI2 : I / 2 < 2 ^ vs.length := by
        rw [List.length_cons, pow_succ] at hI
        omega
      rw [xm_cons] at hx
      rcases Nat.mod_two_eq_zero_or_one I with h0 | h1
      · rw [if_neg (by omega), Nat.zero_xor] at hx
        have := echB_indep_aux vs _ hE' hlen' (I / 2) hI2 (xspan_mono hsub hx)
        omega
      · rw [if_pos h1] at hx
        have e : xm vs (I / 2) =
            ((v ^^^ xm vs (I / 2)) ^^^ (redV B v ^^^ v)) ^^^ redV B v :=
          Nat.eq_of_testBit_eq fun i => by
            simp only [Nat.testBit_xor]
            cases (xm vs (I / 2)).testBit i <;> cases v.testBit i <;>
              cases (redV B v).testBit i <;> rfl
        have hy : XSpan (insDesc (redV B v) B) (xm vs (I / 2)) := by
          rw [e]
          exact xspan_xor (xspan_xor (xspan_mono hsub hx) (xspan_mono hsub (redV_xspan B v)))
            (xspan_of_mem hrm)
        have hI0 := echB_indep_aux vs _ hE' hlen' (I / 2) hI2 hy
        rw [hI0, xm_zero, Nat.xor_zero] at hx
        have hrs : XSpan B (redV B v) := by
          have h3 := xspan_xor (redV_xspan B v) hx
          rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h3
        exact absurd (echS_span_zero hE hrs (redV_clear B v hE)) hr

theorem echB_indep {vs : List ℕ} (h : (echB [] vs).length = vs.length) :
    ∀ I < 2 ^ vs.length, xm vs I = 0 → I = 0 := by
  intro I hI h0
  refine echB_indep_aux vs [] ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
    (by rw [h, List.length_nil, Nat.zero_add]) I hI ?_
  rw [h0]
  exact XSpan.zero

theorem zmod2_ite_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then (1 : ZMod 2) else 0) = if q then 1 else 0) : p ↔ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem zmod2_decide_ite (b : Bool) : decide ((if b then (1 : ZMod 2) else 0) = 1) = b := by
  cases b <;> decide

theorem zmod2_decide_add (a b : ZMod 2) :
    decide (a + b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  revert a b
  decide

theorem zmod2_eq_zero_of_ne_one (a : ZMod 2) (h : a ≠ 1) : a = 0 := by
  revert a
  decide

section Codes


@[expose] noncomputable def tau (g : J) : ℕ := (burnsideJ4NP_encJ g).transl

theorem rho_apply {g : J} (hg : g ∈ Hj) (i j : Fin 12) :
    burnsideJ4NP_rho g i j =
      if ((burnsideJ4NP_encJ g).rows[i.val]?.getD 0).testBit j.val then 1 else 0 := by
  have e : burnsideJ4NP_rho g = burnsideJ4NP_codeMat (burnsideJ4NP_enc ⟨g, hg⟩) :=
    (burnsideJ4NP_codeMat_enc ⟨g, hg⟩).symm
  rw [e, burnsideJ4NP_encJ_of_mem hg]
  rfl

theorem rho_pk {x : J} {X : ℕ} (hx : PK x X) (i j : Fin 12) :
    burnsideJ4NP_rho x i j = if (X / 2 ^ (12 * i.val) % 2 ^ 12).testBit j.val then 1 else 0 := by
  rw [rho_apply hx.1, rc_row hx.2 i.2]

theorem rho_E {y : J} (hy : y ∈ Eg uJ 11) {k : Fin 12} (hk : k ≠ 0) (l : Fin 12) :
    burnsideJ4NP_rho y k l = (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) k l := by
  have hyH : y ∈ Hj := Eg_le_Hj hy
  have hin := (burnsideJ4NP_mem_Eg_iff hyH).1 hy
  rw [← burnsideJ4NP_encJ_of_mem hyH] at hin
  unfold Code.inE at hin
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hin
  obtain ⟨k, hk'⟩ := k
  have hk0 : k ≠ 0 := fun e => hk (Fin.ext e)
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  rw [rho_apply hyH, hin i (by omega), Nat.testBit_two_pow, Matrix.one_apply]
  by_cases h : i + 1 = l.val
  · rw [if_pos (decide_eq_true h), if_pos (Fin.ext h)]
  · rw [if_neg (by simpa using h), if_neg (fun e => h (congrArg Fin.val e))]

theorem mem_E_of_rho {g : J} (hg : g ∈ Hj)
    (h : ∀ k : Fin 12, k ≠ 0 → ∀ l, burnsideJ4NP_rho g k l = (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) k l) :
    g ∈ Eg uJ 11 := by
  rw [burnsideJ4NP_mem_Eg_iff hg]
  have hwf := burnsideJ4NP_codeWF_enc ⟨g, hg⟩
  rw [← burnsideJ4NP_encJ_of_mem hg] at hwf ⊢
  unfold Code.inE
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi
  have hs : i + 1 < (burnsideJ4NP_encJ g).rows.size := by rw [hwf.1]; omega
  have hlt : (burnsideJ4NP_encJ g).rows[i + 1]?.getD 0 < 2 ^ 12 := by
    rw [Array.getElem?_eq_getElem hs, Option.getD_some]
    exact hwf.2 _ (Array.getElem_mem hs)
  apply Nat.eq_of_testBit_eq
  intro l
  rw [Nat.testBit_two_pow]
  by_cases hl : l < 12
  · have := h ⟨i + 1, by omega⟩ (fun e => by simp [Fin.ext_iff] at e) ⟨l, hl⟩
    rw [rho_apply hg, Matrix.one_apply] at this
    have hb := zmod2_ite_iff this
    simp only [Fin.mk.injEq] at hb
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hb
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    symm
    rw [decide_eq_false_iff_not]
    omega

theorem tau_lt (g : J) : tau g < 2 ^ 11 := by
  by_cases hg : g ∈ Hj
  · have hwf := burnsideJ4NP_codeWF_enc ⟨g, hg⟩
    rw [← burnsideJ4NP_encJ_of_mem hg] at hwf
    have hs : 0 < (burnsideJ4NP_encJ g).rows.size := by rw [hwf.1]; norm_num
    have hlt : (burnsideJ4NP_encJ g).rows[0]?.getD 0 < 2 ^ 12 := by
      rw [Array.getElem?_eq_getElem hs, Option.getD_some]
      exact hwf.2 _ (Array.getElem_mem hs)
    unfold tau Code.transl
    rw [Nat.shiftRight_eq_div_pow]
    omega
  · classical
    unfold tau burnsideJ4NP_encJ
    rw [dif_neg hg]
    decide

theorem tau_one : tau 1 = 0 := by
  unfold tau
  rw [burnsideJ4NP_encJ_one]
  rfl

theorem tau_testBit {g : J} (hg : g ∈ Hj) {j : ℕ} (hj : j < 11) :
    (tau g).testBit j = decide (burnsideJ4NP_rho g 0 ⟨j + 1, by omega⟩ = 1) := by
  rw [rho_apply hg, zmod2_decide_ite]
  unfold tau Code.transl
  rw [Nat.testBit_shiftRight, Nat.add_comm 1 j]
  rfl

theorem tau_mul_E {g y : J} (hg : g ∈ Hj) (hy : y ∈ Eg uJ 11) : tau (g * y) = tau g ^^^ tau y := by
  have hyH := Eg_le_Hj hy
  have hgy := Hj.mul_mem hg hyH
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 11
  · rw [Nat.testBit_xor, tau_testBit hgy hj, tau_testBit hg hj, tau_testBit hyH hj,
      burnsideJ4NP_rho_mul hyH, Matrix.mul_apply]
    have hl : (0 : Fin 12) ≠ ⟨j + 1, by omega⟩ := fun e => by simp [Fin.ext_iff] at e
    have key : ∀ k, burnsideJ4NP_rho g 0 k * burnsideJ4NP_rho y k ⟨j + 1, by omega⟩ =
        (if k = 0 then burnsideJ4NP_rho y 0 ⟨j + 1, by omega⟩ else 0) +
          burnsideJ4NP_rho g 0 k * (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) k ⟨j + 1, by omega⟩ := by
      intro k
      by_cases hk : k = 0
      · subst hk
        rw [burnsideJ4NP_rho_col0 hg 0, if_pos rfl, if_pos rfl, Matrix.one_apply_ne hl]
        ring
      · rw [rho_E hy hk, if_neg hk, zero_add]
    rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib, ← Matrix.mul_apply,
      Matrix.mul_one]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [zmod2_decide_add, Bool.xor_comm]
  · have h1 : ∀ x < 2 ^ 11, x.testBit j = false := fun x hx =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [Nat.testBit_xor, h1 _ (tau_lt _), h1 _ (tau_lt _), h1 _ (tau_lt _)]
    rfl

theorem eq_one_of_tau {y : J} (hy : y ∈ Eg uJ 11) (h : tau y = 0) : y = 1 := by
  have hyH := Eg_le_Hj hy
  refine burnsideJ4NP_eq_one_of_rho_eq_one hyH (Matrix.ext fun k l => ?_)
  by_cases hk : k = 0
  · subst hk
    by_cases hl : l = 0
    · subst hl
      rw [burnsideJ4NP_rho_col0 hyH, if_pos rfl, Matrix.one_apply_eq]
    · obtain ⟨l, hl'⟩ := l
      have hl0 : l ≠ 0 := fun e => hl (Fin.ext e)
      obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
      have hb := tau_testBit hyH (j := j) (by omega)
      rw [h, Nat.zero_testBit] at hb
      rw [Matrix.one_apply_ne (Ne.symm hl)]
      refine zmod2_eq_zero_of_ne_one _ fun e => ?_
      rw [e] at hb
      exact absurd hb (by decide)
  · exact rho_E hy hk l

theorem tau_inj {y y' : J} (hy : y ∈ Eg uJ 11) (hy' : y' ∈ Eg uJ 11) (h : tau y = tau y') :
    y = y' := by
  have h1 : y * y' = 1 := eq_one_of_tau ((Eg uJ 11).mul_mem hy hy')
    (by rw [tau_mul_E (Eg_le_Hj hy) hy', h, Nat.xor_self])
  have h2 := Eg_sq (elem_uJ j4Facts.mat) hy'
  calc y = y * y' * y' := by rw [mul_assoc, h2, mul_one]
    _ = y' := by rw [h1, one_mul]

theorem conj_mem_E {g y : J} (hg : g ∈ Hj) (hy : y ∈ Eg uJ 11) : g * y * g⁻¹ ∈ Eg uJ 11 := by
  have hN : g ∈ Subgroup.normalizer (Eg uJ 11 : Set J) := by
    rw [normalizer_Eg_eq_Hj j4Facts]
    exact hg
  exact (Subgroup.mem_normalizer_iff.mp hN y).mp hy

theorem conj_mem_E' {g y : J} (hg : g ∈ Hj) (hy : y ∈ Eg uJ 11) : g⁻¹ * y * g ∈ Eg uJ 11 := by
  simpa using conj_mem_E (Hj.inv_mem hg) hy

theorem tau_pk {x : J} {X : ℕ} (hx : PK x X) : tau x = translK X := by
  unfold tau Code.transl translK
  rw [rc_row hx.2 (by norm_num : 0 < 12), Nat.shiftRight_eq_div_pow]
  simp

theorem pk_eta {T : Tabs} (hT : tabsOK T = true) {c : ℕ} (hc : c < 2048) :
    PK (eta uJ 11 c) (T.eta c) := by
  unfold tabsOK at hT
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hT
  have he : T.eta c = etaCK UK c := Nat.eq_of_beq_eq_true (hT.1.1 _ hc)
  have hm : eta uJ 11 c ∈ Hj := Eg_le_Hj (eta_mem_Eg 11 le_rfl c)
  refine ⟨hm, ?_⟩
  rw [burnsideJ4NP_encJ_of_mem hm, burnsideJ4NP_enc_eta c, he]
  exact rc_etaCode u_wf c

theorem pk_kel {T : Tabs} (hT : tabsOK T = true) {e : ℕ} (he : e < 1024) : PK (Kel e) (T.kel e) := by
  unfold tabsOK at hT
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hT
  have hk : T.kel e = kelCK e := Nat.eq_of_beq_eq_true (hT.1.2 _ he)
  refine ⟨Kel_mem_Hj he, ?_⟩
  rw [burnsideJ4NP_encJ_of_mem (Kel_mem_Hj he),
    (burnsideJ4NP_enc_eq_iff (g := ⟨Kel e, Kel_mem_Hj he⟩) (burnsideJ4NP_codeWF_kelCode e)).2
      (burnsideJ4NP_rho_Kel he), hk]
  exact rc_kel e

theorem rows_E_left {y g : J} (hy : y ∈ Eg uJ 11) (hg : g ∈ Hj) {k : Fin 12} (hk : k ≠ 0)
    (l : Fin 12) : burnsideJ4NP_rho (y * g) k l = burnsideJ4NP_rho g k l := by
  rw [burnsideJ4NP_rho_mul hg, Matrix.mul_apply]
  simp_rw [rho_E hy hk]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem rows_E_right {g y : J} (hg : g ∈ Hj) (hy : y ∈ Eg uJ 11) {k : Fin 12} (hk : k ≠ 0)
    (l : Fin 12) : burnsideJ4NP_rho (g * y) k l = burnsideJ4NP_rho g k l := by
  rw [burnsideJ4NP_rho_mul (Eg_le_Hj hy), Matrix.mul_apply]
  have key : ∀ m, burnsideJ4NP_rho g k m * burnsideJ4NP_rho y m l =
      burnsideJ4NP_rho g k m * (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) m l := by
    intro m
    by_cases hm : m = 0
    · subst hm
      rw [burnsideJ4NP_rho_col0 hg k, if_neg hk, zero_mul, zero_mul]
    · rw [rho_E hy hm]
  rw [Finset.sum_congr rfl (fun m _ => key m), ← Matrix.mul_apply, Matrix.mul_one]

theorem rows_mul_right {x y g : J} (hg : g ∈ Hj) {k : Fin 12}
    (h : ∀ l, burnsideJ4NP_rho x k l = burnsideJ4NP_rho y k l) (l : Fin 12) :
    burnsideJ4NP_rho (x * g) k l = burnsideJ4NP_rho (y * g) k l := by
  rw [burnsideJ4NP_rho_mul hg, burnsideJ4NP_rho_mul hg, Matrix.mul_apply, Matrix.mul_apply]
  simp_rw [h]

theorem rows_of_div {x y : J} {X Y : ℕ} (hx : PK x X) (hy : PK y Y) (h : X / 4096 = Y / 4096)
    {k : Fin 12} (hk : k ≠ 0) (l : Fin 12) : burnsideJ4NP_rho x k l = burnsideJ4NP_rho y k l := by
  rw [rho_pk hx, rho_pk hy]
  obtain ⟨k, hk'⟩ := k
  have hk0 : k ≠ 0 := fun e => hk (Fin.ext e)
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have e : ∀ Z : ℕ, Z / 2 ^ (12 * (i + 1)) = Z / 4096 / 2 ^ (12 * i) := by
    intro Z
    rw [Nat.div_div_eq_div_mul, Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
  simp only
  rw [e X, e Y, h]

theorem mul_inv_mem_E_of_div {x y : J} {X Y : ℕ} (hx : PK x X) (hy : PK y Y)
    (h : X / 4096 = Y / 4096) : x * y⁻¹ ∈ Eg uJ 11 := by
  have hyi := Hj.inv_mem hy.1
  refine mem_E_of_rho (Hj.mul_mem hx.1 hyi) fun k hk l => ?_
  rw [rows_mul_right hyi (rows_of_div hx hy h hk) l, mul_inv_cancel, burnsideJ4NP_rho_one]

theorem div_eq_of_rows {x y : J} {X Y : ℕ} (hx : PK x X) (hy : PK y Y) (hX : X < 2 ^ 144)
    (hY : Y < 2 ^ 144)
    (h : ∀ k : Fin 12, k ≠ 0 → ∀ l, burnsideJ4NP_rho x k l = burnsideJ4NP_rho y k l) :
    X / 4096 = Y / 4096 := by
  apply Nat.eq_of_testBit_eq
  intro n
  have e4 : (4096 : ℕ) = 2 ^ 12 := by norm_num
  rw [e4, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hn : n + 12 < 144
  · have hk : (n + 12) / 12 < 12 := by omega
    have hk0 : (⟨(n + 12) / 12, hk⟩ : Fin 12) ≠ 0 := fun e => by
      simp only [Fin.ext_iff, Fin.val_zero] at e
      omega
    have := h _ hk0 ⟨(n + 12) % 12, Nat.mod_lt _ (by norm_num)⟩
    rw [rho_pk hx, rho_pk hy] at this
    have hb := zmod2_ite_iff this
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at hb
    have e : (n + 12) % 12 + 12 * ((n + 12) / 12) = n + 12 := Nat.mod_add_div _ _
    have hlt : (n + 12) % 12 < 12 := Nat.mod_lt _ (by norm_num)
    simp only [hlt, decide_true, Bool.true_and, e] at hb
    rw [Bool.eq_iff_iff]
    exact hb
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] noncomputable def blk (x b : J) : ℕ := tau (x * b) ^^^ tau (b * x)

@[expose] noncomputable def lamE (bJ : List J) (x : J) : ℕ :=
  (bJ.zipIdx).foldl (fun acc p => acc ||| (blk x p.1) * 2 ^ (11 * p.2)) 0

theorem fold11_testBit {α : Type*} (f : α → ℕ) (hf : ∀ b, f b < 2 ^ 11) :
    ∀ (L : List α) (k acc n : ℕ),
      ((L.zipIdx k).foldl (fun acc p => acc ||| f p.1 * 2 ^ (11 * p.2)) acc).testBit n =
        (acc.testBit n || (decide (11 * k ≤ n) && ((L.map f).getD (n / 11 - k) 0).testBit (n % 11)))
  | [], k, acc, n => by simp
  | b :: L, k, acc, n => by
    rw [List.zipIdx_cons, List.foldl_cons, fold11_testBit f hf L (k + 1), Nat.testBit_or,
      Nat.testBit_mul_two_pow, Bool.or_assoc]
    congr 1
    by_cases h1 : 11 * k ≤ n
    · by_cases h2 : n < 11 * k + 11
      · have hq : n / 11 = k := by omega
        have hr : n - 11 * k = n % 11 := by omega
        have h3 : ¬ 11 * (k + 1) ≤ n := by omega
        simp [h1, h3, hq, hr]
      · have hq : n / 11 - k = n / 11 - (k + 1) + 1 := by omega
        have h3 : 11 * (k + 1) ≤ n := by omega
        have hb : (f b).testBit (n - 11 * k) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf b) (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h3, hq, hb]
    · have h3 : ¬ 11 * (k + 1) ≤ n := by omega
      simp [h1, h3]

theorem blk_lt (x b : J) : blk x b < 2 ^ 11 := Nat.xor_lt_two_pow (tau_lt _) (tau_lt _)

theorem lamE_testBit (bJ : List J) (x : J) (n : ℕ) :
    (lamE bJ x).testBit n = ((bJ.map (blk x)).getD (n / 11) 0).testBit (n % 11) := by
  unfold lamE
  rw [fold11_testBit (blk x) (blk_lt x) bJ 0 0 n]
  simp

theorem translK_lt' (X : ℕ) : translK X < 2 ^ 11 := by
  unfold translK
  have : X % 2 ^ 12 < 2 ^ 12 := Nat.mod_lt _ (by positivity)
  omega

theorem map_blk {x : J} {X : ℕ} (hx : PK x X) :
    ∀ {bJ : List J} {B : List ℕ}, List.Forall₂ PK bJ B →
      B.map (fun b => translK (M X b) ^^^ translK (M b X)) = bJ.map (blk x)
  | [], [], .nil => rfl
  | b :: bJ, Bc :: B, .cons hb hs => by
    rw [List.map_cons, List.map_cons, map_blk hx hs, blk, tau_pk (pk_mul hx hb),
      tau_pk (pk_mul hb hx)]

theorem lamX_eq_lamE {bJ : List J} {B : List ℕ} (hB2 : List.Forall₂ PK bJ B) {x : J} {X : ℕ}
    (hx : PK x X) : lamX B X = lamE bJ x := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [lamE_testBit, ← map_blk hx hB2]
  unfold lamX
  rw [fold11_testBit (fun b => translK (M X b) ^^^ translK (M b X))
    (fun b => Nat.xor_lt_two_pow (translK_lt' _) (translK_lt' _)) B 0 0 n]
  simp

theorem getD_map_xor {α : Type*} {f g h : α → ℕ} {l : List α} (hl : ∀ b ∈ l, f b = g b ^^^ h b)
    (j : ℕ) : (l.map f).getD j 0 = (l.map g).getD j 0 ^^^ (l.map h).getD j 0 := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_map]
    exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by simpa using hj),
      List.getD_eq_default _ _ (by simpa using hj)]
    rfl

theorem lamE_xor {bJ : List J} {x x' x'' : J} (h : ∀ b ∈ bJ, blk x b = blk x' b ^^^ blk x'' b) :
    lamE bJ x = lamE bJ x' ^^^ lamE bJ x'' := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_xor, lamE_testBit, lamE_testBit, lamE_testBit, getD_map_xor h, Nat.testBit_xor]

theorem lamE_congr {bJ : List J} {x x' : J} (h : ∀ b ∈ bJ, blk x b = blk x' b) :
    lamE bJ x = lamE bJ x' := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [lamE_testBit, lamE_testBit, List.map_congr_left h]

theorem lamE_zero {bJ : List J} {x : J} (h : ∀ b ∈ bJ, blk x b = 0) : lamE bJ x = 0 := by
  have := lamE_xor (x' := x) (x'' := x) (bJ := bJ) (fun b hb => by rw [h b hb, Nat.xor_self])
  rw [Nat.xor_self] at this
  exact this

theorem blk_comm {x b : J} (h : x * b = b * x) : blk x b = 0 := by
  unfold blk
  rw [h, Nat.xor_self]

theorem blk_E {y b : J} (hy : y ∈ Eg uJ 11) (hb : b ∈ Hj) :
    blk y b = tau (b⁻¹ * y * b) ^^^ tau y := by
  have e : y * b = b * (b⁻¹ * y * b) := by group
  unfold blk
  rw [e, tau_mul_E hb (conj_mem_E' hb hy), tau_mul_E hb hy]
  have := xor4 (tau b) (tau (b⁻¹ * y * b)) (tau b) (tau y)
  rw [Nat.xor_self, Nat.zero_xor] at this
  exact this

theorem blk_mul_E {K y b : J} (hK : K ∈ Hj) (hy : y ∈ Eg uJ 11) (hb : b ∈ Hj) :
    blk (K * y) b = blk K b ^^^ blk y b := by
  have e1 : K * y * b = K * b * (b⁻¹ * y * b) := by group
  have e2 : b * (K * y) = b * K * y := by group
  rw [blk_E hy hb]
  unfold blk
  rw [e1, e2, tau_mul_E (Hj.mul_mem hK hb) (conj_mem_E' hb hy), tau_mul_E (Hj.mul_mem hb hK) hy,
    xor4]

theorem blk_eta_xor {b : J} (hb : b ∈ Hj) (a a' : ℕ) :
    blk (eta uJ 11 (a ^^^ a')) b = blk (eta uJ 11 a) b ^^^ blk (eta uJ 11 a') b := by
  have hE : Elem uJ 11 := elem_uJ j4Facts.mat
  have ha : eta uJ 11 a ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl a
  have ha' : eta uJ 11 a' ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl a'
  rw [eta_xor hE le_rfl, blk_E ((Eg uJ 11).mul_mem ha ha') hb, blk_E ha hb, blk_E ha' hb]
  have e : b⁻¹ * (eta uJ 11 a * eta uJ 11 a') * b =
      (b⁻¹ * eta uJ 11 a * b) * (b⁻¹ * eta uJ 11 a' * b) := by group
  rw [e, tau_mul_E (Eg_le_Hj (conj_mem_E' hb ha)) (conj_mem_E' hb ha'),
    tau_mul_E (Eg_le_Hj ha) ha', xor4]

end Codes

section Walk


noncomputable abbrev Acl (bJ : List J) : Subgroup J := Subgroup.closure {g | g ∈ bJ}

noncomputable abbrev Ccl (bJ : List J) : Subgroup J :=
  Subgroup.centralizer ((Acl bJ : Subgroup J) : Set J)

theorem whd_spec {T : Tabs} {B : List ℕ} {H : WHd} (h : whdOK T B H = true) :
    (B.all fun b => sqOneK b && B.all fun b' => commK b b') = true ∧
    (∀ c ∈ H.vs, c < 2048) ∧ (∀ c ∈ H.ws, c < 2048) ∧ (∀ c ∈ H.vas, c < 2048) ∧
    spanAll (H.vs ++ H.ws) = true ∧ (∀ v ∈ H.vs, ∀ b ∈ B, commK (T.eta v) b = true) ∧
    (echB [] (H.ws.map (lamK T B))).length = H.ws.length ∧
    ((H.vas.zip H.ms).all fun p => Nat.beq (T.eta p.1) (prodMask B p.2)) = true ∧
    H.vas.length = H.ms.length ∧ H.gs.all coordOK = true := by
  unfold whdOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, -⟩ := h
  simp only [List.all_eq_true, List.mem_append, Nat.blt_eq] at h4 h6
  refine ⟨h1, fun c hc => h4 c (Or.inl (Or.inl hc)), fun c hc => h4 c (Or.inl (Or.inr hc)),
    fun c hc => h4 c (Or.inr hc), h5, h6, h7, ?_, h3, h9⟩
  rw [List.all_eq_true] at h8 ⊢
  intro p hp
  have := h8 p hp
  rw [Bool.and_eq_true] at this
  exact this.2

theorem walkOK_cases {T : Tabs} {B : List ℕ} {H : WHd} {e : ℕ} {D : List ℕ}
    (h : walkOK T B H e D = true) :
    (∃ j, D = [0, j]) ∨ (∃ v e', D = [1, v, e']) ∨ (∃ Ki ce m l, D = 2 :: Ki :: ce :: m :: l) ∨
      D = [3] := by
  unfold walkOK at h
  split at h
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact absurd h (by simp)

theorem cen_of_pk {bJ : List J} {B : List ℕ} (hB2 : List.Forall₂ PK bJ B) {z : J} {Z : ℕ}
    (hz : PK z Z) (hZ : ∀ b ∈ B, commK Z b = true) : z ∈ Ccl bJ := by
  refine mem_cent_closure fun b hb => ?_
  obtain ⟨Bb, hBb, hbB⟩ := forall₂_exists hB2 b hb
  exact (pk_comm hz hbB).mpr (hZ Bb hBb)

theorem acl_le_ccl {bJ : List J} {B : List ℕ} (hB2 : List.Forall₂ PK bJ B)
    (hbas : (B.all fun b => sqOneK b && B.all fun b' => commK b b') = true) : Acl bJ ≤ Ccl bJ :=
  (Subgroup.closure_le _).2 fun b hb =>
    mem_cent_closure fun b' hb' => (basis_props hB2 hbas).2 b hb b' hb'

theorem acl_sq {bJ : List J} {B : List ℕ} (hB2 : List.Forall₂ PK bJ B)
    (hbas : (B.all fun b => sqOneK b && B.all fun b' => commK b b') = true) {a : J}
    (ha : a ∈ Acl bJ) : a * a = 1 := by
  have hs := (basis_props hB2 hbas).1
  have hAC := acl_le_ccl hB2 hbas
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hxy := Subgroup.mem_centralizer_iff.mp (hAC hy) x hx
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * x * (y * y) := by rw [← hxy]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem mem_cen {bJ : List J} {x a : J} (hx : x ∈ Ccl bJ) (ha : a ∈ Acl bJ) : a * x = x * a :=
  Subgroup.mem_centralizer_iff.mp hx a ha

theorem eta_xm_mem {S : Subgroup J} : ∀ {L : List ℕ}, (∀ c ∈ L, eta uJ 11 c ∈ S) →
    ∀ I, eta uJ 11 (xm L I) ∈ S
  | [], _, _ => by rw [xm, eta_zero]; exact S.one_mem
  | c :: L, h, I => by
    rw [xm_cons, eta_xor (elem_uJ j4Facts.mat) le_rfl]
    refine S.mul_mem ?_ (eta_xm_mem (fun d hd => h d (List.mem_cons_of_mem _ hd)) _)
    split_ifs
    · exact h c List.mem_cons_self
    · rw [eta_zero]; exact S.one_mem

theorem nw_conj_eta (K : J) : ∀ (L : List ℕ) (I : ℕ),
    nwFrom 1 (L.map fun c => K⁻¹ * eta uJ 11 c * K) I = K⁻¹ * eta uJ 11 (xm L I) * K
  | [], _ => by simp [nwFrom, xm, eta_zero]
  | c :: L, I => by
    rw [List.map_cons, nwFrom_cons, nw_conj_eta K L (I / 2), xm_cons,
      eta_xor (elem_uJ j4Facts.mat) le_rfl]
    split_ifs
    · group
    · rw [eta_zero]; group

theorem forall₂_map_pk {f : ℕ → J} {F : ℕ → ℕ} :
    ∀ {L : List ℕ}, (∀ c ∈ L, PK (f c) (F c)) → List.Forall₂ PK (L.map f) (L.map F)
  | [], _ => .nil
  | c :: L, h => .cons (h c List.mem_cons_self)
      (forall₂_map_pk fun d hd => h d (List.mem_cons_of_mem _ hd))

theorem pk_rep {T : Tabs} (hT : tabsOK T = true) {e : ℕ} (he : e < 1024) {Ki : ℕ}
    (hinv : invK (T.kel e) Ki = true) {cs : List ℕ} (hcs : ∀ c ∈ cs, c < 2048) {x₀ : J} {X₀ : ℕ}
    (hx₀ : PK x₀ X₀) (I : ℕ) :
    PK (x₀ * ((Kel e)⁻¹ * eta uJ 11 (xm cs I) * Kel e))
      (prodFrom X₀ (cs.map fun c => M (M Ki (T.eta c)) (T.kel e)) I) := by
  have hK := pk_kel hT he
  have h2 := forall₂_map_pk (f := fun c => (Kel e)⁻¹ * eta uJ 11 c * Kel e)
    (F := fun c => M (M Ki (T.eta c)) (T.kel e)) (L := cs)
    (fun c hc => pk_mul (pk_mul (pk_inv hK hinv) (pk_eta hT (hcs c hc))) hK)
  have := pk_prodFrom h2 hx₀ I
  rwa [nwFrom_mul, nw_conj_eta] at this

theorem prodFrom_zero : ∀ (acc : ℕ) (L : List ℕ), prodFrom acc L 0 = acc
  | _, [] => rfl
  | acc, x :: L => by
    unfold prodFrom
    simp only [Nat.zero_mod, Nat.zero_ne_one, if_false, Nat.zero_div]
    exact prodFrom_zero acc L

theorem walk_zero_excl {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {H : WHd} {e j c : ℕ} (he : e < 1024)
    (h : walkOK T B H e [0, j] = true) : eta uJ 11 c * Kel e ∉ Ccl bJ := by
  intro hx
  simp only [walkOK, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨hj, hlin⟩ := h
  have hjb : j < bJ.length := by rw [hB2.length_eq]; exact hj
  have hb := forall₂_getD (a := (1 : J)) (b := 0) hB2 j hjb
  have hbA : bJ.getD j 1 ∈ Acl bJ := Subgroup.subset_closure (getD_mem hjb)
  have hxb := mem_cen hx hbA
  have hK := pk_kel hT he
  have hE : eta uJ 11 c ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl c
  have hrows : ∀ k : Fin 12, k ≠ 0 → ∀ l, burnsideJ4NP_rho (Kel e * bJ.getD j 1) k l =
      burnsideJ4NP_rho (bJ.getD j 1 * Kel e) k l := by
    intro k hk l
    have h1 := rows_E_left hE (Hj.mul_mem hK.1 hb.1) hk l
    have h2 := rows_mul_right hK.1 (rows_E_right hb.1 hE hk) l
    rw [← h1, ← mul_assoc, ← hxb, ← mul_assoc, h2]
  have := div_eq_of_rows (pk_mul hK hb) (pk_mul hb hK) (M_lt _ _) (M_lt _ _) hrows
  unfold linC at hlin
  rw [this, Nat.beq_refl] at hlin
  exact Bool.noConfusion hlin

theorem walk_one_move {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {H : WHd} {e v e' c : ℕ} (he : e < 1024) (hc : c < 2 ^ 11)
    (h : walkOK T B H e [1, v, e'] = true) :
    e' < e ∧ ∃ c' < 2 ^ 11, eta uJ 11 c * Kel e * nwFrom 1 bJ v = eta uJ 11 c' * Kel e' := by
  simp only [walkOK, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨he', -⟩, hdiv⟩ := h
  have hdiv' : M (T.kel e) (prodMask B v) / 4096 = T.kel e' / 4096 := Nat.eq_of_beq_eq_true hdiv
  have hK := pk_kel hT he
  have hK' := pk_kel hT (by omega : e' < 1024)
  have hmem := mul_inv_mem_E_of_div (pk_mul hK (pk_prodMask hB2 v)) hK' hdiv'
  obtain ⟨c'', hc'', he''⟩ := (mem_Eg_iff (elem_uJ j4Facts.mat)).1 hmem
  refine ⟨he', c ^^^ c'', Nat.xor_lt_two_pow hc hc'', ?_⟩
  rw [eta_xor (elem_uJ j4Facts.mat) le_rfl, ← he'']
  group

theorem lamK_eq {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {w : ℕ} (hw : w < 2 ^ 11) :
    lamK T B w = lamE bJ (eta uJ 11 w) :=
  lamX_eq_lamE hB2 (pk_eta hT (by omega))

theorem lamK_xor {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) : ∀ a < 2 ^ 11, ∀ b < 2 ^ 11,
      lamK T B (a ^^^ b) = lamK T B a ^^^ lamK T B b := by
  intro a ha b hb
  rw [lamK_eq hT hB2 (Nat.xor_lt_two_pow ha hb), lamK_eq hT hB2 ha, lamK_eq hT hB2 hb]
  exact lamE_xor fun b' hb' => blk_eta_xor (mem_Hj_of hB2 b' hb') a b

theorem lamK_cen {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {w : ℕ} (hw : w < 2 ^ 11) (h : eta uJ 11 w ∈ Ccl bJ) :
    lamK T B w = 0 := by
  rw [lamK_eq hT hB2 hw]
  exact lamE_zero fun b hb => blk_comm (mem_cen h (Subgroup.subset_closure hb)).symm

theorem ws_kill {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {ws : List ℕ} (hwsb : ∀ c ∈ ws, c < 2048)
    (hind : (echB [] (ws.map (lamK T B))).length = ws.length) (I : ℕ)
    (h : eta uJ 11 (xm ws I) ∈ Ccl bJ) : xm ws I = 0 := by
  have hwsb' : ∀ c ∈ ws, c < 2 ^ 11 := fun c hc => by have := hwsb c hc; omega
  rw [xm_mod] at h ⊢
  have h0 := lamK_cen hT hB2 (xm_lt hwsb' _) h
  rw [← xm_map_lt (lamK_xor hT hB2) hwsb'] at h0
  have hI := echB_indep (by rw [hind, List.length_map]) (I % 2 ^ ws.length)
    (by rw [List.length_map]; exact Nat.mod_lt _ (by positivity)) h0
  rw [hI, xm_zero]

theorem walk_three_excl {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {H : WHd} (hH : whdOK T B H = true) {e c : ℕ} (he : e < 1024)
    (h : walkOK T B H e [3] = true) : eta uJ 11 c * Kel e ∉ Ccl bJ := by
  intro hx
  simp only [walkOK, beq_iff_eq] at h
  obtain ⟨-, hvsb, hwsb, -, hspan, hvcen, -, -, -, -⟩ := whd_spec hH
  have hEl : Elem uJ 11 := elem_uJ j4Facts.mat
  have hK := pk_kel hT he
  have hy : (Kel e)⁻¹ * eta uJ 11 c * Kel e ∈ Eg uJ 11 := conj_mem_E' hK.1 (eta_mem_Eg 11 le_rfl c)
  have hxy : eta uJ 11 c * Kel e = Kel e * ((Kel e)⁻¹ * eta uJ 11 c * Kel e) := by group
  obtain ⟨c', hc', hyc⟩ := (mem_Eg_iff hEl).1 hy
  have hblk : ∀ b ∈ bJ, blk (Kel e) b = blk (eta uJ 11 c') b := by
    intro b hb
    have h0 := blk_comm (mem_cen hx (Subgroup.subset_closure hb)).symm
    rw [hxy, blk_mul_E hK.1 hy (mem_Hj_of hB2 b hb), hyc] at h0
    exact Nat.eq_of_testBit_eq fun i => by
      have := congrArg (fun z => z.testBit i) h0
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this
      cases (blk (Kel e) b).testBit i <;> cases (blk (eta uJ 11 c') b).testBit i <;> decide
  have hz : lamX B (T.kel e) = lamK T B c' := by
    rw [lamX_eq_lamE hB2 hK, lamK_eq hT hB2 hc']
    exact lamE_congr hblk
  have hvsb' : ∀ c ∈ H.vs, c < 2 ^ 11 := fun c hc => by have := hvsb c hc; omega
  have hwsb' : ∀ c ∈ H.ws, c < 2 ^ 11 := fun c hc => by have := hwsb c hc; omega
  obtain ⟨I, -, hI⟩ := xspan_xm (spanAll_spec hspan c' (by omega))
  rw [xm_append] at hI
  have hv0 : lamK T B (xm H.vs I) = 0 :=
    lamK_cen hT hB2 (xm_lt hvsb' _) (eta_xm_mem (fun v hv =>
      cen_of_pk hB2 (pk_eta hT (hvsb v hv)) (hvcen v hv)) I)
  rw [← hI, lamK_xor hT hB2 _ (xm_lt hvsb' _) _ (xm_lt hwsb' _), hv0, Nat.zero_xor,
    ← xm_map_lt (lamK_xor hT hB2) hwsb'] at hz
  set L := H.ws.map (lamK T B)
  set J' := I / 2 ^ H.vs.length
  have hLz := echB_indep (vs := L ++ [lamX B (T.kel e)])
    (by rw [h, List.length_append, List.length_map]; rfl)
    (J' % 2 ^ L.length + 2 ^ L.length)
    (by
      rw [List.length_append, List.length_singleton, pow_succ]
      have := Nat.mod_lt J' (Nat.two_pow_pos L.length)
      omega)
  have hmod : (J' % 2 ^ L.length + 2 ^ L.length) % 2 ^ L.length = J' % 2 ^ L.length := by
    rw [Nat.add_mod_right, Nat.mod_mod]
  have hdiv : (J' % 2 ^ L.length + 2 ^ L.length) / 2 ^ L.length = 1 := by
    have := Nat.mod_lt J' (Nat.two_pow_pos L.length)
    rw [Nat.add_div_right _ (Nat.two_pow_pos _), Nat.div_eq_of_lt this]
  rw [xm_append, xm_mod L, hmod, ← xm_mod L, hdiv, ← hz] at hLz
  have : 2 ^ L.length ≤ J' % 2 ^ L.length + 2 ^ L.length := Nat.le_add_left _ _
  have h0 := hLz (by simp [xm, Nat.xor_self])
  have := Nat.two_pow_pos L.length
  omega

theorem eta_conj (K : J) (hK : K ∈ Hj) (c d : ℕ) :
    eta uJ 11 d * (eta uJ 11 c * K) * (eta uJ 11 d)⁻¹ =
      (eta uJ 11 d * K * eta uJ 11 d * K⁻¹) * (eta uJ 11 c * K) := by
  have hEl : Elem uJ 11 := elem_uJ j4Facts.mat
  have hdi : (eta uJ 11 d)⁻¹ = eta uJ 11 d := inv_eq_of_mul_eq_one_right (eta_sq hEl d)
  have hg : eta uJ 11 d * (K * eta uJ 11 d * K⁻¹) ∈ Eg uJ 11 :=
    (Eg uJ 11).mul_mem (eta_mem_Eg 11 le_rfl d) (conj_mem_E hK (eta_mem_Eg 11 le_rfl d))
  have hcm := Eg_comm hEl (eta_mem_Eg 11 le_rfl c) hg
  have hcd := eta_comm hEl d c
  rw [hdi]
  calc eta uJ 11 d * (eta uJ 11 c * K) * eta uJ 11 d
      = eta uJ 11 d * eta uJ 11 c * K * eta uJ 11 d := by group
    _ = eta uJ 11 c * (eta uJ 11 d * (K * eta uJ 11 d * K⁻¹)) * K := by rw [hcd]; group
    _ = eta uJ 11 d * (K * eta uJ 11 d * K⁻¹) * eta uJ 11 c * K := by rw [hcm]
    _ = _ := by group

theorem comm_mem_E {K : J} (hK : K ∈ Hj) (v : ℕ) :
    eta uJ 11 v * K * eta uJ 11 v * K⁻¹ ∈ Eg uJ 11 := by
  have := (Eg uJ 11).mul_mem (eta_mem_Eg 11 le_rfl v) (conj_mem_E hK (eta_mem_Eg 11 le_rfl v))
  rwa [← mul_assoc, ← mul_assoc] at this

theorem comm_xor {K : J} (hK : K ∈ Hj) (a b : ℕ) :
    eta uJ 11 (a ^^^ b) * K * eta uJ 11 (a ^^^ b) * K⁻¹ =
      (eta uJ 11 a * K * eta uJ 11 a * K⁻¹) * (eta uJ 11 b * K * eta uJ 11 b * K⁻¹) := by
  have hEl : Elem uJ 11 := elem_uJ j4Facts.mat
  have hcm := Eg_comm hEl (eta_mem_Eg 11 le_rfl b) (conj_mem_E hK (eta_mem_Eg 11 le_rfl a))
  rw [eta_xor hEl le_rfl]
  calc eta uJ 11 a * eta uJ 11 b * K * (eta uJ 11 a * eta uJ 11 b) * K⁻¹
      = eta uJ 11 a * (eta uJ 11 b * (K * eta uJ 11 a * K⁻¹)) * (K * eta uJ 11 b * K⁻¹) := by
        group
    _ = eta uJ 11 a * ((K * eta uJ 11 a * K⁻¹) * eta uJ 11 b) * (K * eta uJ 11 b * K⁻¹) := by
        rw [hcm]
    _ = _ := by group

theorem conj_marked {T : Tabs} (hT : tabsOK T = true) {e Ki : ℕ} (he : e < 1024)
    (hinv : invK (T.kel e) Ki = true) {zs vs cs : List ℕ} (hzs : ∀ c ∈ zs, c < 2048)
    (hvs : ∀ c ∈ vs, c < 2048) (hcs : ∀ c ∈ cs, c < 2048) {t : ℕ}
    (hspan : XSpan (zs.map (fun c => translK (T.eta c)) ++ commV T (T.kel e) Ki vs ++
      cs.map (fun c => translK (T.eta c))) (tau (eta uJ 11 t))) :
    ∃ I₁ I₂, ∃ I₃ < 2 ^ cs.length, eta uJ 11 (xm vs I₂) * (eta uJ 11 t * Kel e) *
      (eta uJ 11 (xm vs I₂))⁻¹ = eta uJ 11 (xm zs I₁) * (eta uJ 11 (xm cs I₃) * Kel e) := by
  have hEl : Elem uJ 11 := elem_uJ j4Facts.mat
  have hK := pk_kel hT he
  have hKi : PK (Kel e)⁻¹ Ki := pk_inv hK hinv
  have hEm : ∀ v, eta uJ 11 v ∈ Eg uJ 11 := fun v => eta_mem_Eg 11 le_rfl v
  have hφ1 : ∀ a b, tau (eta uJ 11 (a ^^^ b)) = tau (eta uJ 11 a) ^^^ tau (eta uJ 11 b) :=
    fun a b => by rw [eta_xor hEl le_rfl]; exact tau_mul_E (Eg_le_Hj (hEm a)) (hEm b)
  have hφ2 : ∀ a b, tau (eta uJ 11 (a ^^^ b) * Kel e * eta uJ 11 (a ^^^ b) * (Kel e)⁻¹) =
      tau (eta uJ 11 a * Kel e * eta uJ 11 a * (Kel e)⁻¹) ^^^
        tau (eta uJ 11 b * Kel e * eta uJ 11 b * (Kel e)⁻¹) :=
    fun a b => by
      rw [comm_xor hK.1]
      exact tau_mul_E (Eg_le_Hj (comm_mem_E hK.1 a)) (comm_mem_E hK.1 b)
  have hS1 : ∀ L : List ℕ, (∀ c ∈ L, c < 2048) →
      L.map (fun c => translK (T.eta c)) = L.map (fun c => tau (eta uJ 11 c)) :=
    fun L hL => List.map_congr_left fun c hc => (tau_pk (pk_eta hT (hL c hc))).symm
  have hS2 : commV T (T.kel e) Ki vs =
      vs.map (fun v => tau (eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹)) := by
    unfold commV
    refine List.map_congr_left fun v hv => ?_
    have hv' := pk_eta hT (hvs v hv)
    have hconj : PK (Kel e * eta uJ 11 v * (Kel e)⁻¹) (M (M (T.kel e) (T.eta v)) Ki) :=
      pk_mul (pk_mul hK hv') hKi
    rw [← tau_pk hv', ← tau_pk hconj, ← tau_mul_E hv'.1 (conj_mem_E hK.1 (hEm v))]
    simp only [mul_assoc]
  rw [hS1 _ hzs, hS2, hS1 _ hcs] at hspan
  obtain ⟨I, -, hI⟩ := xspan_xm hspan
  obtain ⟨J3, e3⟩ := xm_append_ex _ (cs.map fun c => tau (eta uJ 11 c)) I
  obtain ⟨J2, e2⟩ := xm_append_ex (zs.map fun c => tau (eta uJ 11 c))
    (vs.map fun v => tau (eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹)) I
  rw [e3, e2, xm_map (φ := fun c => tau (eta uJ 11 c)) hφ1,
    xm_map (φ := fun v => tau (eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹)) hφ2,
    xm_map (φ := fun c => tau (eta uJ 11 c)) hφ1] at hI
  set d1 := xm zs I
  set d2 := xm vs J2
  set g2 := eta uJ 11 d2 * Kel e * eta uJ 11 d2 * (Kel e)⁻¹
  have hgE : g2 ∈ Eg uJ 11 := comm_mem_E hK.1 d2
  have hP : eta uJ 11 d1 * g2 ∈ Eg uJ 11 := (Eg uJ 11).mul_mem (hEm d1) hgE
  have hprod : eta uJ 11 t = eta uJ 11 d1 * g2 * eta uJ 11 (xm cs J3) := by
    refine tau_inj (hEm _) ((Eg uJ 11).mul_mem hP (hEm _)) ?_
    rw [tau_mul_E (Eg_le_Hj hP) (hEm _), tau_mul_E (Eg_le_Hj (hEm d1)) hgE]
    exact hI.symm
  refine ⟨I, J2, J3 % 2 ^ cs.length, Nat.mod_lt _ (by positivity), ?_⟩
  rw [← xm_mod, eta_conj (Kel e) hK.1, hprod]
  have hg2 : g2 * g2 = 1 := Eg_sq hEl hgE
  have hc1 : g2 * eta uJ 11 d1 = eta uJ 11 d1 * g2 := Eg_comm hEl hgE (hEm d1)
  calc g2 * (eta uJ 11 d1 * g2 * eta uJ 11 (xm cs J3) * Kel e)
      = (g2 * eta uJ 11 d1) * g2 * eta uJ 11 (xm cs J3) * Kel e := by group
    _ = eta uJ 11 d1 * (g2 * g2) * eta uJ 11 (xm cs J3) * Kel e := by rw [hc1]; group
    _ = _ := by rw [hg2]; group; rfl

theorem walk_two_cover {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {H : WHd} (hH : whdOK T B H = true) {e Ki ce m : ℕ}
    {l : List ℕ} (he : e < 1024) (hD : walkOK T B H e (2 :: Ki :: ce :: m :: l) = true) {c : ℕ}
    (hc : c < 2 ^ 11) (hx : eta uJ 11 c * Kel e ∈ Ccl bJ) :
    ∃ d < 2 ^ 11, eta uJ 11 d ∈ Ccl bJ ∧ ∃ I < 2 ^ m, ∃ y a : J,
      PK y (prodFrom (M (T.eta ce) (T.kel e))
        (((l.take m).map fun i => H.vs.getD i 0).map fun c => M (M Ki (T.eta c)) (T.kel e)) I) ∧
      a ∈ Acl bJ ∧ eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ = y * a := by
  obtain ⟨hinv, hce, -, hlen, his, hcomm, hspan, -⟩ := walkOK_two_spec hD
  obtain ⟨hbas, hvsb, hwsb, hvab, -, hvcen, hind, hva, hvm, -⟩ := whd_spec hH
  have hEl : Elem uJ 11 := elem_uJ j4Facts.mat
  have hK := pk_kel hT he
  have hKi : PK (Kel e)⁻¹ Ki := pk_inv hK hinv
  have hX : PK (eta uJ 11 ce * Kel e) (M (T.eta ce) (T.kel e)) := pk_mul (pk_eta hT hce) hK
  have hXc : eta uJ 11 ce * Kel e ∈ Ccl bJ := cen_of_pk hB2 hX hcomm
  have hvC : ∀ v ∈ H.vs, eta uJ 11 v ∈ Ccl bJ := fun v hv =>
    cen_of_pk hB2 (pk_eta hT (hvsb v hv)) (hvcen v hv)
  have hAC := acl_le_ccl hB2 hbas
  have hvaA : ∀ va ∈ H.vas, eta uJ 11 va ∈ Acl bJ := by
    intro va hva'
    obtain ⟨mm, -, hp⟩ := zip_all_mem hva hvm hva'
    rw [pk_beq (pk_eta hT (hvab va hva')) (pk_prodMask hB2 mm) hp]
    exact nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) mm
  have hEm : ∀ v, eta uJ 11 v ∈ Eg uJ 11 := fun v => eta_mem_Eg 11 le_rfl v
  have hgE : ∀ v, eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹ ∈ Eg uJ 11 :=
    comm_mem_E hK.1
  have hgx := comm_xor hK.1
  have hgC : ∀ v, eta uJ 11 v ∈ Ccl bJ →
      eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹ ∈ Ccl bJ := by
    intro v hv
    have hcm := Eg_comm hEl (hEm ce) (conj_mem_E hK.1 (hEm v))
    have e : eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹ = eta uJ 11 v *
        (eta uJ 11 ce * Kel e) * eta uJ 11 v * (eta uJ 11 ce * Kel e)⁻¹ := by
      calc eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹
          = eta uJ 11 v * (Kel e * eta uJ 11 v * (Kel e)⁻¹) * eta uJ 11 ce *
              (eta uJ 11 ce)⁻¹ := by group
        _ = eta uJ 11 v * (eta uJ 11 ce * (Kel e * eta uJ 11 v * (Kel e)⁻¹)) *
              (eta uJ 11 ce)⁻¹ := by rw [hcm]; group
        _ = _ := by group
    rw [e]
    exact (Ccl bJ).mul_mem ((Ccl bJ).mul_mem ((Ccl bJ).mul_mem hv hXc) hv) ((Ccl bJ).inv_mem hXc)
  have hδ : eta uJ 11 c * Kel e = eta uJ 11 (c ^^^ ce) * (eta uJ 11 ce * Kel e) := by
    rw [eta_xor hEl le_rfl]
    calc eta uJ 11 c * Kel e = eta uJ 11 c * (eta uJ 11 ce * eta uJ 11 ce) * Kel e := by
          rw [eta_sq hEl, mul_one]
      _ = _ := by group
  have hδC : eta uJ 11 (c ^^^ ce) ∈ Ccl bJ := by
    have e : eta uJ 11 (c ^^^ ce) = eta uJ 11 c * Kel e * (eta uJ 11 ce * Kel e)⁻¹ := by
      rw [hδ]; group
    rw [e]
    exact (Ccl bJ).mul_mem hx ((Ccl bJ).inv_mem hXc)
  have hcsv : ∀ c ∈ (l.take m).map (fun i => H.vs.getD i 0), c ∈ H.vs := fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact getD_mem (his i hi)
  have hφ1 : ∀ a b, tau (eta uJ 11 (a ^^^ b)) = tau (eta uJ 11 a) ^^^ tau (eta uJ 11 b) :=
    fun a b => by rw [eta_xor hEl le_rfl]; exact tau_mul_E (Eg_le_Hj (hEm a)) (hEm b)
  have hφ2 : ∀ a b, tau (eta uJ 11 (a ^^^ b) * Kel e * eta uJ 11 (a ^^^ b) * (Kel e)⁻¹) =
      tau (eta uJ 11 a * Kel e * eta uJ 11 a * (Kel e)⁻¹) ^^^
        tau (eta uJ 11 b * Kel e * eta uJ 11 b * (Kel e)⁻¹) :=
    fun a b => by rw [hgx]; exact tau_mul_E (Eg_le_Hj (hgE a)) (hgE b)
  have hS1 : ∀ L : List ℕ, (∀ c ∈ L, c < 2048) →
      L.map (fun c => translK (T.eta c)) = L.map (fun c => tau (eta uJ 11 c)) :=
    fun L hL => List.map_congr_left fun c hc => (tau_pk (pk_eta hT (hL c hc))).symm
  have hS2 : commV T (T.kel e) Ki H.vs =
      H.vs.map (fun v => tau (eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹)) := by
    unfold commV
    refine List.map_congr_left fun v hv => ?_
    have hv' := pk_eta hT (hvsb v hv)
    have hconj : PK (Kel e * eta uJ 11 v * (Kel e)⁻¹) (M (M (T.kel e) (T.eta v)) Ki) :=
      pk_mul (pk_mul hK hv') hKi
    rw [← tau_pk hv', ← tau_pk hconj, ← tau_mul_E hv'.1 (conj_mem_E hK.1 (hEm v))]
    simp only [mul_assoc]
  rw [hS1 _ hvab, hS2, hS1 _ (fun c hc => hvsb c (hcsv c hc)), hS1 _ hwsb] at hspan
  obtain ⟨I, -, hI⟩ := xspan_xm (spanAll_spec hspan (tau (eta uJ 11 (c ^^^ ce)))
    (lt_of_lt_of_le (tau_lt _) (by norm_num)))
  obtain ⟨J4, e4⟩ := xm_append_ex _ (H.ws.map fun c => tau (eta uJ 11 c)) I
  obtain ⟨J3, e3⟩ := xm_append_ex _
    (((l.take m).map fun i => H.vs.getD i 0).map fun c => tau (eta uJ 11 c)) I
  obtain ⟨J2, e2⟩ := xm_append_ex (H.vas.map fun c => tau (eta uJ 11 c))
    (H.vs.map fun v => tau (eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹)) I
  rw [e4, e3, e2, xm_map (φ := fun c => tau (eta uJ 11 c)) hφ1,
    xm_map (φ := fun v => tau (eta uJ 11 v * Kel e * eta uJ 11 v * (Kel e)⁻¹)) hφ2,
    xm_map (φ := fun c => tau (eta uJ 11 c)) hφ1, xm_map (φ := fun c => tau (eta uJ 11 c)) hφ1] at hI
  set cs := (l.take m).map fun i => H.vs.getD i 0 with hcs
  set d1 := xm H.vas I
  set d2 := xm H.vs J2
  set d3 := xm cs J3
  set d4 := xm H.ws J4
  set g2 := eta uJ 11 d2 * Kel e * eta uJ 11 d2 * (Kel e)⁻¹
  have hP : eta uJ 11 d1 * g2 * eta uJ 11 d3 ∈ Eg uJ 11 :=
    (Eg uJ 11).mul_mem ((Eg uJ 11).mul_mem (hEm d1) (hgE d2)) (hEm d3)
  have hprod : eta uJ 11 (c ^^^ ce) = eta uJ 11 d1 * g2 * eta uJ 11 d3 * eta uJ 11 d4 := by
    refine tau_inj (hEm _) ((Eg uJ 11).mul_mem hP (hEm d4)) ?_
    rw [tau_mul_E (Eg_le_Hj hP) (hEm d4), tau_mul_E (Eg_le_Hj ((Eg uJ 11).mul_mem (hEm d1) (hgE d2)))
      (hEm d3), tau_mul_E (Eg_le_Hj (hEm d1)) (hgE d2)]
    exact hI.symm
  have hd1 : eta uJ 11 d1 ∈ Acl bJ := eta_xm_mem hvaA I
  have hd2 : eta uJ 11 d2 ∈ Ccl bJ := eta_xm_mem hvC J2
  have hd3 : eta uJ 11 d3 ∈ Ccl bJ := eta_xm_mem (fun c hc => hvC c (hcsv c hc)) J3
  have hd4C : eta uJ 11 d4 ∈ Ccl bJ := by
    have e : eta uJ 11 d4 = (eta uJ 11 d1 * g2 * eta uJ 11 d3)⁻¹ * eta uJ 11 (c ^^^ ce) := by
      rw [hprod]; group
    rw [e]
    exact (Ccl bJ).mul_mem ((Ccl bJ).inv_mem ((Ccl bJ).mul_mem ((Ccl bJ).mul_mem (hAC hd1)
      (hgC _ hd2)) hd3)) hδC
  have hd4 : eta uJ 11 d4 = 1 := by
    have h0 : d4 = 0 := ws_kill hT hB2 hwsb hind J4 hd4C
    rw [h0, eta_zero]
  have hcl : cs.length = m := by rw [hcs, List.length_map, hlen]
  have hvsb' : ∀ c ∈ H.vs, c < 2 ^ 11 := fun c hc => by have := hvsb c hc; omega
  refine ⟨d2, xm_lt hvsb' _, hd2, J3 % 2 ^ m, Nat.mod_lt _ (by positivity),
    eta uJ 11 d3 * (eta uJ 11 ce * Kel e), eta uJ 11 d1, ?_, hd1, ?_⟩
  · have := pk_rep hT he hinv (fun c hc => hvsb c (hcsv c hc)) hX (J3 % 2 ^ m)
    rw [← hcl, ← xm_mod] at this
    have e : eta uJ 11 ce * Kel e * ((Kel e)⁻¹ * eta uJ 11 d3 * Kel e) =
        eta uJ 11 d3 * (eta uJ 11 ce * Kel e) := by
      rw [← mul_assoc (eta uJ 11 d3), ← eta_comm hEl ce d3]; group
    rw [e] at this
    rw [hcl] at this
    exact this
  · rw [eta_conj (Kel e) hK.1, hδ, hprod, hd4, mul_one]
    have hg2 : g2 * g2 = 1 := Eg_sq hEl (hgE d2)
    have hc1 : g2 * eta uJ 11 d1 = eta uJ 11 d1 * g2 := Eg_comm hEl (hgE d2) (hEm d1)
    have hc2 : eta uJ 11 d1 * (eta uJ 11 d3 * (eta uJ 11 ce * Kel e)) =
        eta uJ 11 d3 * (eta uJ 11 ce * Kel e) * eta uJ 11 d1 :=
      mem_cen ((Ccl bJ).mul_mem hd3 hXc) hd1
    calc g2 * (eta uJ 11 d1 * g2 * eta uJ 11 d3 * (eta uJ 11 ce * Kel e))
        = (g2 * eta uJ 11 d1) * g2 * eta uJ 11 d3 * (eta uJ 11 ce * Kel e) := by group
      _ = eta uJ 11 d1 * (g2 * g2) * eta uJ 11 d3 * (eta uJ 11 ce * Kel e) := by rw [hc1]; group
      _ = eta uJ 11 d1 * (eta uJ 11 d3 * (eta uJ 11 ce * Kel e)) := by rw [hg2]; group
      _ = _ := hc2

theorem walk_cover {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {H : WHd} (hH : whdOK T B H = true) {D : ℕ → List ℕ}
    (hD : ∀ e < 1024, walkOK T B H e (D e) = true) :
    ∀ e < 1024, ∀ c < 2 ^ 11, eta uJ 11 c * Kel e ∈ Ccl bJ → eta uJ 11 c * Kel e ∉ Acl bJ →
      ∃ e' < 1024, ∃ Ki ce m : ℕ, ∃ l : List ℕ, D e' = 2 :: Ki :: ce :: m :: l ∧
        ∃ d < 2 ^ 11, eta uJ 11 d ∈ Ccl bJ ∧ ∃ I < 2 ^ m, ∃ y a : J,
          PK y (prodFrom (M (T.eta ce) (T.kel e'))
            (((l.take m).map fun i => H.vs.getD i 0).map fun c => M (M Ki (T.eta c)) (T.kel e'))
            I) ∧
          a ∈ Acl bJ ∧ eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ = y * a := by
  obtain ⟨hbas, -⟩ := whd_spec hH
  have hAC := acl_le_ccl hB2 hbas
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro he c hc hx hxA
  rcases walkOK_cases (hD e he) with ⟨j, hDe⟩ | ⟨v, e', hDe⟩ | ⟨Ki, ce, m, l, hDe⟩ | hDe
  · exact absurd hx (walk_zero_excl hT hB2 he (by rw [← hDe]; exact hD e he))
  · obtain ⟨he', c', hc', heq⟩ := walk_one_move hT hB2 he hc (by rw [← hDe]; exact hD e he)
    have ha : nwFrom 1 bJ v ∈ Acl bJ :=
      nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) v
    have hx' : eta uJ 11 c' * Kel e' ∈ Ccl bJ := by
      rw [← heq]; exact (Ccl bJ).mul_mem hx (hAC ha)
    have hxA' : eta uJ 11 c' * Kel e' ∉ Acl bJ := by
      rw [← heq]
      intro hm
      have := (Acl bJ).mul_mem hm ((Acl bJ).inv_mem ha)
      rw [mul_inv_cancel_right] at this
      exact hxA this
    obtain ⟨e'', he'', Ki, ce, m, l, hD', d, hd, hdC, I, hI, y, a', hy, ha', hconj⟩ :=
      ih e' he' (by omega) c' hc' hx' hxA'
    refine ⟨e'', he'', Ki, ce, m, l, hD', d, hd, hdC, I, hI, y, a' * (nwFrom 1 bJ v)⁻¹, hy,
      (Acl bJ).mul_mem ha' ((Acl bJ).inv_mem ha), ?_⟩
    have hda := mem_cen hdC ha
    rw [← heq] at hconj
    calc eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹
        = eta uJ 11 d * (eta uJ 11 c * Kel e * nwFrom 1 bJ v) * (eta uJ 11 d)⁻¹ *
            (eta uJ 11 d * (nwFrom 1 bJ v)⁻¹ * (eta uJ 11 d)⁻¹) := by group
      _ = y * a' * (nwFrom 1 bJ v)⁻¹ := by
          rw [hconj]
          have : eta uJ 11 d * (nwFrom 1 bJ v)⁻¹ = (nwFrom 1 bJ v)⁻¹ * eta uJ 11 d := by
            calc eta uJ 11 d * (nwFrom 1 bJ v)⁻¹
                = (nwFrom 1 bJ v)⁻¹ * (nwFrom 1 bJ v * eta uJ 11 d) * (nwFrom 1 bJ v)⁻¹ := by
                  group
              _ = (nwFrom 1 bJ v)⁻¹ * (eta uJ 11 d * nwFrom 1 bJ v) * (nwFrom 1 bJ v)⁻¹ := by
                  rw [hda]
              _ = (nwFrom 1 bJ v)⁻¹ * eta uJ 11 d := by group
          rw [this]; group
      _ = _ := by group
  · exact ⟨e, he, Ki, ce, m, l, hDe, walk_two_cover hT hB2 hH he (by rw [← hDe]; exact hD e he) hc hx⟩
  · exact absurd hx (walk_three_excl hT hB2 hH he (by rw [← hDe]; exact hD e he))

theorem walk_cover_P0 {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {H : WHd} (hH : whdOK T B H = true) {D : ℕ → List ℕ}
    (hD : ∀ e < 1024, walkOK T B H e (D e) = true) {x : J} (hxP : x ∈ P0) (hx : x ∈ Ccl bJ)
    (hxA : x ∉ Acl bJ) (hsq : x * x = 1) :
    ∃ e' < 1024, ∃ Ki ce m : ℕ, ∃ l : List ℕ, D e' = 2 :: Ki :: ce :: m :: l ∧
      ∃ d < 2 ^ 11, eta uJ 11 d ∈ Ccl bJ ∧ ∃ I < 2 ^ m, ((l.drop m).headD 0).testBit I = true ∧
        ∃ y a : J,
          PK y (prodFrom (M (T.eta ce) (T.kel e'))
            (((l.take m).map fun i => H.vs.getD i 0).map fun c => M (M Ki (T.eta c)) (T.kel e'))
            I) ∧
          a ∈ Acl bJ ∧ eta uJ 11 d * x * (eta uJ 11 d)⁻¹ = y * a ∧ y * y = 1 ∧ y ∉ Acl bJ ∧
          ∃ s ∈ H.gs.map burnsideJ4NP_treeElt, s * y ≠ y * s := by
  obtain ⟨hbas, -, -, -, -, -, -, -, -, hgs⟩ := whd_spec hH
  have hAC := acl_le_ccl hB2 hbas
  obtain ⟨c, hc, e, he, rfl⟩ := exists_eta_mul_Kel j4Facts.mat j4Facts hxP
  obtain ⟨e', he', Ki, ce, m, l, hDe, d, hd, hdC, I, hI, y, a, hy, ha, hconj⟩ :=
    walk_cover hT hB2 hH hD e he c hc hx hxA
  have hz : eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ ∈ Ccl bJ :=
    (Ccl bJ).mul_mem ((Ccl bJ).mul_mem hdC hx) ((Ccl bJ).inv_mem hdC)
  have hye : y = eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ * a⁻¹ := by
    rw [hconj]; group
  have hysq : y * y = 1 := by
    have hza := mem_cen hz ((Acl bJ).inv_mem ha)
    have haa : a⁻¹ * a⁻¹ = 1 := acl_sq hB2 hbas ((Acl bJ).inv_mem ha)
    rw [hye]
    calc eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ * a⁻¹ *
          (eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ * a⁻¹)
        = eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ *
            (a⁻¹ * (eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹)) * a⁻¹ := by group
      _ = eta uJ 11 d * ((eta uJ 11 c * Kel e) * (eta uJ 11 c * Kel e)) * (eta uJ 11 d)⁻¹ *
            (a⁻¹ * a⁻¹) := by rw [hza]; group
      _ = 1 := by rw [hsq, haa]; group
  have hyA : y ∉ Acl bJ := by
    intro hm
    have h1 : eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ ∈ Acl bJ := by
      rw [hconj]; exact (Acl bJ).mul_mem hm ha
    have h2 := mem_cen hdC h1
    have : eta uJ 11 c * Kel e = eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ := by
      calc eta uJ 11 c * Kel e = (eta uJ 11 d)⁻¹ *
            (eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹ * eta uJ 11 d) := by group
        _ = (eta uJ 11 d)⁻¹ * (eta uJ 11 d *
            (eta uJ 11 d * (eta uJ 11 c * Kel e) * (eta uJ 11 d)⁻¹)) := by rw [h2]
        _ = _ := by group
    exact hxA (by rw [this]; exact h1)
  obtain ⟨-, -, he0, -, -, -, -, henum⟩ := walkOK_two_spec (by rw [← hDe]; exact hD e' he')
  have h1 : e' ≠ 0 ∨ I ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    have hce : ce = 0 := by rcases he0 with h | h; exact absurd rfl h; exact h
    subst hce
    rw [prodFrom_zero] at hy
    have h1 : PK 1 (M (T.eta 0) (T.kel 0)) := by
      have := pk_mul (pk_eta hT (by norm_num : 0 < 2048)) (pk_kel hT (by norm_num : 0 < 1024))
      rwa [eta_zero, Kel_zero, one_mul] at this
    exact hyA (pk_eq hy h1 ▸ (Acl bJ).one_mem)
  obtain ⟨hL, s, hs, hsy⟩ := walk_leaf_sound hT hgs (henum I hI) hy hysq h1
  exact ⟨e', he', Ki, ce, m, l, hDe, d, hd, hdC, I, hI, hL, y, a, hy, ha, hconj, hysq, hyA, s, hs,
    hsy⟩

end Walk

end CFSG.KC.J4TreeT
