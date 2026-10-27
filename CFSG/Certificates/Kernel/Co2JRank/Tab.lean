module

public import CFSG.Certificates.Kernel.Co2JRank.Sound

set_option exponentiation.threshold 1100

public section

namespace CFSG.KC.Co2JRank

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.TabMatGrp
  CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native

theorem tbK_eq (m i : Nat) : tbK m i = m.testBit i := by
  unfold tbK
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have e : Nat.land (Nat.shiftRight m i) 1 = m / 2 ^ i % 2 := by
    change (m >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem oneIf_eq (b : Bool) : oneIf b = if b then 1 else 0 := by cases b <;> rfl

theorem orK_eq (a b : Bool) : orK a b = (a || b) := by cases a <;> rfl

theorem eqB_iff (a b : Bool) : eqB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

theorem fldJ_lt (W i : Nat) : fldJ W i < 1024 :=
  Nat.and_lt_two_pow _ (by decide : 1023 < 2 ^ 10)

theorem popJ_eq (S : Nat) :
    popJ S = ((Finset.range 1024).filter fun v => S.testBit v = true).card := by
  unfold popJ
  rw [sumBelow_eq' _ _ _ (by decide), Finset.card_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [oneIf_eq, tbK_eq]

theorem omC_iff (c : Nat) : omC c = true ↔ c = 0 ∨ c = 2 ∨ c = 7 := by
  unfold omC
  simp only [orK_eq, Bool.or_eq_true, Nat.beq_eq]

theorem vC_iff (c : Nat) : vC c = true ↔ c = 0 ∨ c = 7 := by
  unfold vC
  simp only [orK_eq, Bool.or_eq_true, Nat.beq_eq]

theorem tabJ_parts {K1 K3 vr CNT OM OL m NT W5 W3 C : Nat}
    (h : tabJ K1 K3 vr CNT OM OL m NT W5 W3 C = true) :
    nzK K1 1024 16 = true ∧ cntK K1 K3 vr CNT = true ∧ omK K1 K3 vr OM = true ∧
      olK OM OL m = true ∧ nK K1 K3 vr OM OL m NT = true ∧ w5K OM W5 = true ∧
      w3K K1 K3 vr W3 = true ∧ spK K1 K3 vr C = true := by
  unfold tabJ at h
  simp only [andK_eq, Bool.and_eq_true] at h
  exact h

theorem cntJ_eq (K1 K3 vr c : Nat) :
    cntJ K1 K3 vr c = ((Finset.range 1024).filter fun v => clsJ K1 K3 vr v = c).card := by
  unfold cntJ
  rw [sumBelow_eq' _ _ _ (by decide), Finset.card_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [oneIf_eq]
  by_cases h : clsJ K1 K3 vr v = c
  · rw [if_pos h, h, Nat.beq_refl, if_pos rfl]
  · rw [if_neg h, beq_false h, if_neg Bool.false_ne_true]

theorem cntK_sound {K1 K3 vr CNT : Nat} (h : cntK K1 K3 vr CNT = true) :
    ∀ c < 10, ((Finset.range 1024).filter fun v => clsJ K1 K3 vr v = c).card =
      fld(CNT, Nat.mul 12 c, 4095) := by
  intro c hc
  rw [← cntJ_eq]
  exact Nat.eq_of_beq_eq_true (recAll (p := fun c => Nat.beq (cntJ K1 K3 vr c)
    (fld(CNT, Nat.mul (nat_lit 12) c, nat_lit 4095))) 10 h c hc)

theorem omK_sound {K1 K3 vr OM : Nat} (h : omK K1 K3 vr OM = true) :
    OM < 2 ^ 1024 ∧ ∀ v < 1024, (OM.testBit v = true ↔ omC (clsJ K1 K3 vr v) = true) := by
  unfold omK at h
  rw [andK_eq, Bool.and_eq_true] at h
  refine ⟨?_, fun v hv => ?_⟩
  · have e : Nat.shiftLeft (nat_lit 1) (nat_lit 1024) = 2 ^ 1024 := by
      change 1 <<< 1024 = 2 ^ 1024
      rw [Nat.one_shiftLeft]
    exact lt_of_lt_of_eq (blt_iff.1 h.1) e
  · have := allBelow_spec h.2 v hv (lt_of_lt_of_le hv (by decide))
    rw [eqB_iff, tbK_eq] at this
    exact this

theorem inc_of_succ {f : Nat → Nat} {m : Nat} (h : ∀ i, i + 1 < m → f i < f (i + 1)) :
    ∀ i j, i < j → j < m → f i < f j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · exact (ih hij (by omega)).trans (h j hj)
    · exact h i hj

theorem olK_sound {OM OL m : Nat} (h : olK OM OL m = true) :
    (Finset.range m).image (fldJ OL) = (Finset.range 1024).filter (fun v => OM.testBit v = true) ∧
      Set.InjOn (fldJ OL) (Finset.range m) := by
  unfold olK at h
  rw [andK_eq, Bool.and_eq_true] at h
  obtain ⟨hp, hl⟩ := h
  have hl' := recAll (p := fun i => andK (tbK OM (fldJ OL i))
    (implK (Nat.blt (Nat.succ i) m) (Nat.blt (fldJ OL i) (fldJ OL (Nat.succ i))))) m hl
  have hmem : ∀ i < m, OM.testBit (fldJ OL i) = true := fun i hi => by
    have := hl' i hi
    rw [andK_eq, Bool.and_eq_true, tbK_eq] at this
    exact this.1
  have hinc : ∀ i, i + 1 < m → fldJ OL i < fldJ OL (i + 1) := fun i hi => by
    have := hl' i (by omega)
    rw [andK_eq, Bool.and_eq_true, implK_eq,
      if_pos (blt_iff.2 (show Nat.succ i < m from hi))] at this
    exact blt_iff.1 this.2
  have hinj : Set.InjOn (fldJ OL) (Finset.range m) := by
    intro a ha b hb e
    have ha' : a < m := Finset.mem_range.1 (Finset.mem_coe.1 ha)
    have hb' : b < m := Finset.mem_range.1 (Finset.mem_coe.1 hb)
    rcases lt_trichotomy a b with hab | hab | hab
    · exact absurd e (inc_of_succ hinc a b hab hb').ne
    · exact hab
    · exact absurd e (inc_of_succ hinc b a hab ha').ne'
  refine ⟨Finset.eq_of_subset_of_card_le ?_ ?_, hinj⟩
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (fldJ_lt _ _), hmem i (Finset.mem_range.1 hi)⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← popJ_eq]
    exact (Nat.eq_of_beq_eq_true hp).le

theorem nJ_eq (OM OL m y : Nat) :
    nJ OM OL m y = ∑ i ∈ Finset.range m, if OM.testBit (fldJ OL i ^^^ y) then 1 else 0 := by
  refine (recSum _ m).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [oneIf_eq, tbK_eq]
  rfl

theorem nK_sound {K1 K3 vr OM OL m NT : Nat} (hom : omK K1 K3 vr OM = true)
    (hol : olK OM OL m = true) (h : nK K1 K3 vr OM OL m NT = true) :
    ∀ y < 1024, clsJ K1 K3 vr y < 9 →
      ((Finset.range 1024).filter fun t => omC (clsJ K1 K3 vr t) = true ∧
        omC (clsJ K1 K3 vr (t ^^^ y)) = true).card = fld(NT, Nat.mul 4 (clsJ K1 K3 vr y), 15) := by
  intro y hy hc
  obtain ⟨-, hOM⟩ := omK_sound hom
  obtain ⟨himg, hinj⟩ := olK_sound hol
  have e := allBelow_spec h y hy (lt_of_lt_of_le hy (by decide))
  simp only [letB_eq, implK_eq] at e
  rw [if_pos (blt_iff.2 hc)] at e
  have hs : (∑ i ∈ Finset.range m, if OM.testBit (fldJ OL i ^^^ y) then 1 else 0) =
      ∑ t ∈ (Finset.range m).image (fldJ OL), if OM.testBit (t ^^^ y) then 1 else 0 :=
    (Finset.sum_image (f := fun t => if OM.testBit (t ^^^ y) then 1 else 0) hinj).symm
  rw [← Nat.eq_of_beq_eq_true e, nJ_eq, hs, himg, Finset.card_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have hty : t ^^^ y < 1024 := Nat.xor_lt_two_pow (n := 10) ht' hy
  simp only [hOM t ht', hOM _ hty]
  by_cases a : omC (clsJ K1 K3 vr t) = true <;> by_cases b : omC (clsJ K1 K3 vr (t ^^^ y)) = true <;>
    simp [a, b]

theorem xorF_five (W : Nat) :
    xorF W 5 = 0 ^^^ fldJ W 0 ^^^ fldJ W 1 ^^^ fldJ W 2 ^^^ fldJ W 3 ^^^ fldJ W 4 := rfl

theorem xorF_three (W : Nat) : xorF W 3 = 0 ^^^ fldJ W 0 ^^^ fldJ W 1 ^^^ fldJ W 2 := rfl

theorem w5K_sound {OM W5 : Nat} (h : w5K OM W5 = true) :
    (∀ i < 5, OM.testBit (fldJ W5 i) = true) ∧
      fldJ W5 0 ^^^ fldJ W5 1 ^^^ fldJ W5 2 ^^^ fldJ W5 3 ^^^ fldJ W5 4 = 0 := by
  unfold w5K at h
  rw [andK_eq, Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, ?_⟩
  · have := recAll (p := fun i => tbK OM (fldJ W5 i)) 5 h.1 i hi
    rwa [tbK_eq] at this
  · have := (xorF_five W5).symm.trans (Nat.eq_of_beq_eq_true h.2)
    rwa [Nat.zero_xor] at this

theorem w3K_sound {K1 K3 vr W3 : Nat} (h : w3K K1 K3 vr W3 = true) :
    (∀ i < 3, clsJ K1 K3 vr (fldJ W3 i) = 4) ∧
      (fldJ W3 0 ^^^ fldJ W3 1 ^^^ fldJ W3 2 = 0 ∨ fldJ W3 0 ^^^ fldJ W3 1 ^^^ fldJ W3 2 = vr) := by
  unfold w3K at h
  simp only [andK_eq, Bool.and_eq_true, letB_eq, orK_eq, Bool.or_eq_true] at h
  refine ⟨fun i hi => Nat.eq_of_beq_eq_true
    (recAll (p := fun i => Nat.beq (clsJ K1 K3 vr (fldJ W3 i)) 4) 3 h.1 i hi), ?_⟩
  have e : fldJ W3 0 ^^^ fldJ W3 1 ^^^ fldJ W3 2 = xorF W3 3 := by
    rw [xorF_three, Nat.zero_xor]
  rw [e]
  rcases h.2 with h2 | h2
  · exact Or.inl (Nat.eq_of_beq_eq_true h2)
  · exact Or.inr (Nat.eq_of_beq_eq_true h2)

theorem xsub_succ (C n u : Nat) :
    xsub C (n + 1) u = xsub C n u ^^^ (if u.testBit n then fldJ C n else 0) := by
  change Nat.xor (xsub C n u) (selN (tbK u n) (fldJ C n) (nat_lit 0)) = _
  rw [selN_eq, tbK_eq]
  rfl

theorem xsub_lt (C u : Nat) : ∀ n, xsub C n u < 1024
  | 0 => by
    change (0 : Nat) < 1024
    decide
  | n + 1 => by
    rw [xsub_succ]
    refine Nat.xor_lt_two_pow (n := 10) (xsub_lt C u n) ?_
    split
    · exact fldJ_lt C n
    · decide

theorem xsub_zero (C : Nat) : ∀ n, xsub C n 0 = 0
  | 0 => rfl
  | n + 1 => by
    rw [xsub_succ, xsub_zero C n, Nat.zero_testBit]
    simp

theorem xsub_xor (C u w : Nat) : ∀ n, xsub C n (u ^^^ w) = xsub C n u ^^^ xsub C n w
  | 0 => by
    change (0 : Nat) = 0 ^^^ 0
    simp
  | n + 1 => by
    rw [xsub_succ, xsub_succ, xsub_succ, xsub_xor C u w n, Nat.testBit_xor]
    apply Nat.eq_of_testBit_eq
    intro i
    cases u.testBit n <;> cases w.testBit n <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, if_true, if_false, Nat.testBit_xor, Nat.zero_testBit] <;>
      cases (xsub C n u).testBit i <;> cases (xsub C n w).testBit i <;>
      cases (fldJ C n).testBit i <;> rfl

theorem spanRec_testBit (C n v : Nat) : ∀ N, (Nat.rec (motive := fun _ => Nat) 0
    (fun u acc => Nat.lor acc (Nat.shiftLeft 1 (xsub C n u))) N : Nat).testBit v = true ↔
      ∃ u < N, xsub C n u = v
  | 0 => by simp
  | N + 1 => by
    change ((Nat.rec (motive := fun _ => Nat) 0
      (fun u acc => Nat.lor acc (Nat.shiftLeft 1 (xsub C n u))) N : Nat) |||
        1 <<< xsub C n N).testBit v = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      spanRec_testBit C n v N, decide_eq_true_iff]
    constructor
    · rintro (⟨u, hu, e⟩ | e)
      · exact ⟨u, by omega, e⟩
      · exact ⟨N, by omega, e⟩
    · rintro ⟨u, hu, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact Or.inl ⟨u, hu, e⟩
      · exact Or.inr e

theorem spanJ_testBit (C n v : Nat) :
    (spanJ C n).testBit v = true ↔ ∃ u < 2 ^ n, xsub C n u = v := by
  have e : (2 : Nat) ^ n = Nat.shiftLeft 1 n := (Nat.one_shiftLeft n).symm
  rw [e]
  exact spanRec_testBit C n v _

theorem spK_sound {K1 K3 vr C : Nat} (h : spK K1 K3 vr C = true) :
    ((Finset.range 64).image (xsub C 6)).card = 64 ∧
      (∀ v < 1024, vC (clsJ K1 K3 vr v) = true → ∃ u < 64, xsub C 6 u = v) ∧
      ∀ i < 6, vC (clsJ K1 K3 vr (fldJ C i)) = true := by
  unfold spK at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨hp, hv, hc⟩ := h
  have himg : (Finset.range 64).image (xsub C 6) =
      (Finset.range 1024).filter fun v => (spanJ C 6).testBit v = true := by
    ext v
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, spanJ_testBit]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨xsub_lt C u 6, u, hu, rfl⟩
    · rintro ⟨-, u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  refine ⟨?_, fun v hv' hvc => ?_, fun i hi => recAll (p := fun i => vC (clsJ K1 K3 vr (fldJ C i)))
    6 hc i hi⟩
  · rw [himg, ← popJ_eq]
    exact Nat.eq_of_beq_eq_true hp
  · have := allBelow_spec hv v hv' (lt_of_lt_of_le hv' (by decide))
    rw [implK_eq, if_pos hvc, tbK_eq, spanJ_testBit] at this
    exact this

theorem evenK_eq (n v : Nat) :
    evenK n v = decide (Even ((Finset.range n).filter fun i => v.testBit i = true).card) := by
  induction n with
  | zero =>
    change true = _
    simp
  | succ n ih =>
    change bIf(tbK v n, notK (evenK n v), evenK n v) = _
    rw [bIf_eq', tbK_eq, notK_eq, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hb : v.testBit n = true
    · rw [if_pos hb, if_pos hb, Finset.card_insert_of_notMem (by simp)]
      simp [Nat.even_add_one, ← Nat.not_even_iff_odd]
    · rw [if_neg hb, if_neg hb]

theorem parK_sound {K1 n : Nat} (h : parK K1 n = true) (hn : 2 ^ n ≤ 64) :
    ∀ v < 2 ^ n, ((v ≠ 0 ∧ Even ((Finset.range n).filter fun i => v.testBit i = true).card) ↔
      (kAt K1 v = 8 ∧ kAt K1 (v ^^^ 1) = 6)) := by
  intro v hv
  have hv' : v < Nat.shiftLeft (nat_lit 1) n := by
    change v < 1 <<< n
    rw [Nat.one_shiftLeft]
    exact hv
  have := allBelow_spec h v hv' (by change v < 64 * 1; omega)
  simp only [eqB_iff, andK_eq, notK_eq, evenK_eq, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, Nat.beq_eq] at this
  have e1 : Nat.beq v 0 = false ↔ v ≠ 0 :=
    ⟨fun h e => by
      subst e
      exact absurd h (by decide), beq_false⟩
  rw [e1] at this
  exact this

section Transfer

variable {M : Type*} [Monoid M] {e : ℕ → M}

theorem card_image_sub (hinj : ∀ s < 1024, ∀ t < 1024, e s = e t → s = t) (P : M → Prop) :
    Nat.card {x // (∃ v < 1024, e v = x) ∧ P x} = Nat.card {v // v < 1024 ∧ P (e v)} := by
  let F : {v // v < 1024 ∧ P (e v)} → {x // (∃ v < 1024, e v = x) ∧ P x} :=
    fun v => ⟨e v.1, ⟨v.1, v.2.1, rfl⟩, v.2.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun a b h => Subtype.ext (hinj a.1 a.2.1 b.1 b.2.1 (congrArg Subtype.val h)),
      fun x => ?_⟩
    obtain ⟨x, ⟨v, hv, rfl⟩, hP⟩ := x
    exact ⟨⟨v, hv, hP⟩, rfl⟩
  exact (Nat.card_eq_of_bijective F hF).symm

theorem closure_xsub (he : ∀ s < 1024, ∀ t < 1024, e (s ^^^ t) = e s * e t) (he0 : e 0 = 1)
    {A : ℕ → Prop} {C n : Nat} (hC : ∀ i < n, A (fldJ C i))
    (hA : ∀ v < 1024, A v → ∃ u < 2 ^ n, xsub C n u = v) {x : M} :
    x ∈ Submonoid.closure {x | ∃ v < 1024, A v ∧ e v = x} ↔ ∃ u < 2 ^ n, e (xsub C n u) = x := by
  constructor
  · intro hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨v, hv, hAv, rfl⟩ := hx
      obtain ⟨u, hu, rfl⟩ := hA v hv hAv
      exact ⟨u, hu, rfl⟩
    | one => exact ⟨0, Nat.two_pow_pos n, by rw [xsub_zero, he0]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨t, ht, rfl⟩ := hy
      exact ⟨s ^^^ t, Nat.xor_lt_two_pow hs ht, by
        rw [xsub_xor, he _ (xsub_lt C s n) _ (xsub_lt C t n)]⟩
  · rintro ⟨u, -, rfl⟩
    have key : ∀ k ≤ n, e (xsub C k u) ∈ Submonoid.closure {x | ∃ v < 1024, A v ∧ e v = x} := by
      intro k
      induction k with
      | zero => intro _; rw [show xsub C 0 u = 0 from rfl, he0]; exact Submonoid.one_mem _
      | succ k ih =>
        intro hk
        have hc : (if u.testBit k then fldJ C k else 0) < 1024 := by
          split
          · exact fldJ_lt C k
          · decide
        rw [xsub_succ, he _ (xsub_lt C u k) _ hc]
        refine Submonoid.mul_mem _ (ih (by omega)) ?_
        split
        · exact Submonoid.subset_closure ⟨fldJ C k, fldJ_lt C k, hC k (by omega), rfl⟩
        · rw [he0]
          exact Submonoid.one_mem _
    exact key n le_rfl

theorem card_closure_xsub (he : ∀ s < 1024, ∀ t < 1024, e (s ^^^ t) = e s * e t) (he0 : e 0 = 1)
    (hinj : ∀ s < 1024, ∀ t < 1024, e s = e t → s = t)
    {A : ℕ → Prop} {C n : Nat} (hC : ∀ i < n, A (fldJ C i))
    (hA : ∀ v < 1024, A v → ∃ u < 2 ^ n, xsub C n u = v) :
    Nat.card (Submonoid.closure {x | ∃ v < 1024, A v ∧ e v = x}) =
      ((Finset.range (2 ^ n)).image (xsub C n)).card := by
  have hset : ((Submonoid.closure {x | ∃ v < 1024, A v ∧ e v = x} : Submonoid M) : Set M) =
      e '' ↑((Finset.range (2 ^ n)).image (xsub C n)) := by
    ext x
    rw [SetLike.mem_coe, closure_xsub he he0 hC hA]
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
  have hinj' : Set.InjOn e ↑((Finset.range (2 ^ n)).image (xsub C n)) := by
    intro a ha b hb h
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image] at ha hb
    obtain ⟨u, -, rfl⟩ := ha
    obtain ⟨w, -, rfl⟩ := hb
    exact hinj _ (xsub_lt C u n) _ (xsub_lt C w n) h
  change Nat.card ↥((Submonoid.closure {x | ∃ v < 1024, A v ∧ e v = x} : Submonoid M) : Set M) = _
  rw [hset, Nat.card_image_of_injOn hinj', Nat.card_coe_set_eq, Set.ncard_coe_finset]

end Transfer

theorem xP_eq_asc {M : Type*} [Monoid M] {f : ℕ → M} {B : ℕ → ℕ → M} (h0 : ∀ u, B 0 u = 1)
    (hs : ∀ k u, B (k + 1) u = B k u * (if u.testBit k then f k else 1)) :
    ∀ k, (∀ i < k, ∀ j < k, Commute (f i) (f j)) → ∀ u, B k u = xP f k u
  | 0, _, u => h0 u
  | k + 1, hc, u => by
    rw [hs, xP_eq_asc h0 hs k (fun i hi j hj => hc i (by omega) j (by omega)) u, xP]
    refine (Commute.eq ?_)
    refine (xP_commute f k u fun i hi => ?_)
    split
    · exact hc i (by omega) k (by omega)
    · exact Commute.one_right _

theorem allPt_ranks {CR JE : Nat → Nat} {K1 K3 R vr N hi : Nat}
    (h : allBelow N hi (fun v => ptJ CR K1 K3 R vr (JE v) v) = true) (hN : N ≤ 64 * hi) :
    ∀ v < N, (MatP 22 (JE v) + 1).rank = kAt K1 v ∧ (kAt K1 v = 10 → kAt K1 (v ^^^ vr) = 10 →
      ((MatP 22 R + 1) * (MatP 22 (JE v) + 1)).rank = kAt K3 v) :=
  fun v hv => ptJ_sound (allBelow_spec h v hv (by omega))

end CFSG.KC.Co2JRank

end
