module

public import Certificates.Data.Kernel.Fi22Twist.Pairs
public import CFSG.Certificates.Kernel.E27Lie.SoundRep
public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KS.Fi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KS.E27Lie Subgroup

theorem qpBit_iff (m i : ℕ) : qpBit m i = true ↔ m.testBit i = true := by
  unfold qpBit
  change Nat.beq ((m >>> i) &&& 1) 1 = true ↔ _
  rw [Nat.beq_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, Nat.and_one_is_mod,
    Nat.shiftRight_eq_div_pow]

theorem testBit_qpE (r t u : ℕ) :
    (qpE r t).testBit u = (r.testBit (16 * t + u) && decide (u < 16)) := by
  have e : qpE r t = (r >>> (16 * t)) &&& (2 ^ 16 - 1) := rfl
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]

theorem testBit_full (n i : ℕ) : ((1 <<< n) - 1).testBit i = decide (i < n) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem testBit_qpFull (i : ℕ) : qpFull.testBit i = decide (i < 729) := testBit_full 729 i

theorem testBit_shl1 (k i : ℕ) : (1 <<< k).testBit i = decide (k = i) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_one_ne {i : ℕ} (h : i ≠ 0) : (1 : ℕ).testBit i = false := by
  have e : (1 : ℕ) = 1 <<< 0 := rfl
  rw [e, testBit_shl1]
  simpa [eq_comm] using h

theorem testBit_foldOr (n : ℕ) (g : ℕ → ℕ) (i : ℕ) :
    (foldN n (fun t s => Nat.lor s (g t)) 0).testBit i = true ↔ ∃ t < n, (g t).testBit i = true := by
  rw [CFSG.KS.PK.foldN_eq]
  have key : ∀ l : List ℕ, (l.foldr (fun t s => Nat.lor s (g t)) 0).testBit i = true ↔
      ∃ t ∈ l, (g t).testBit i = true := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.foldr_cons]
      change (_ ||| g a).testBit i = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih]
      simp only [List.mem_cons, exists_eq_or_imp]
      exact Or.comm
  rw [key]
  simp only [List.mem_range]

theorem qpVM_bit (row i : ℕ) : (qpVM row).testBit i = true ↔ ∃ t < 9, qpE row t = i := by
  refine (testBit_foldOr 9 (fun t => 1 <<< qpE row t) i).trans ?_
  simp only [testBit_shl1, decide_eq_true_eq]

theorem key96_eq {r r' : ℕ} (h : ∀ l < 6, qpE r (2 + l) = qpE r' (2 + l)) :
    fld(r, nat_lit 32, nat_lit 79228162514264337593543950335) =
      fld(r', nat_lit 32, nat_lit 79228162514264337593543950335) := by
  have e1 : ∀ s : ℕ, fld(s, nat_lit 32, nat_lit 79228162514264337593543950335) =
      (s >>> 32) &&& (2 ^ 96 - 1) := fun s => rfl
  rw [e1, e1]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 96
  · have hl : j / 16 < 6 := by omega
    have hm : j % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have e2 : 16 * (2 + j / 16) + j % 16 = 32 + j := by omega
    have := congrArg (fun z => z.testBit (j % 16)) (h (j / 16) hl)
    simp only [testBit_qpE, hm, decide_true, Bool.and_true, e2] at this
    rw [this]
  · simp [hj]

theorem allBlk0_spec {f : ℕ → Bool} {len : ℕ} (h : allBlk 0 f len = true) :
    ∀ l < len, f l = true := by
  intro l hl
  have e := CFSG.KS.allBlk_spec h l hl
  have e0 : Nat.add 0 l = l := Nat.zero_add l
  rwa [e0] at e

theorem allBlk0_intro {f : ℕ → Bool} : ∀ {len : ℕ}, (∀ l < len, f l = true) →
    allBlk 0 f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk 0 f len) (f (Nat.add 0 len)) = true
    have e0 : Nat.add 0 len = len := Nat.zero_add len
    rw [e0, h len (Nat.lt_succ_self len), allBlk0_intro fun l hl => h l (by omega)]

theorem qpMul_spec {p R S : ℕ} (h : qpMul p R S = true) :
    ∀ l < 6, qpE R (2 + l) = ap p (qpE S (2 + l)) := by
  intro l hl
  exact beq_of (allBlk0_spec h l hl)

theorem qp_sortC_spec {key s : ℕ → ℕ} {n m : ℕ} (h : sortC key s n m = true) :
    s m < n ∧ (m + 1 < n → key (s m) < key (s (m + 1))) := by
  unfold sortC at h
  rw [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨blt_of h1, fun hm => ?_⟩
  have hb : Nat.blt (Nat.succ m) n = true := Eq.mpr Nat.blt_eq hm
  rw [bRec_eq, if_pos hb, sB_eq] at h2
  exact blt_of h2

theorem qp_inj_of_sorted {key s : ℕ → ℕ} {n : ℕ} (hs : ∀ m < n, s m < n)
    (hlt : ∀ m, m + 1 < n → key (s m) < key (s (m + 1))) :
    ∀ i < n, ∀ k < n, key i = key k → i = k := by
  have mono : ∀ m₁ m₂, m₁ < m₂ → m₂ < n → key (s m₁) < key (s m₂) := by
    intro m₁ m₂ h12 h2
    induction m₂ with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 h12 with h | rfl
      · exact lt_trans (ih h (by omega)) (hlt m h2)
      · exact hlt _ h2
  have inj : ∀ m₁ < n, ∀ m₂ < n, key (s m₁) = key (s m₂) → m₁ = m₂ := by
    intro m₁ h1 m₂ h2 e
    rcases lt_trichotomy m₁ m₂ with h | h | h
    · exact absurd e (ne_of_lt (mono _ _ h h2))
    · exact h
    · exact absurd e (ne_of_gt (mono _ _ h h1))
  have surj : ∀ i < n, ∃ m < n, s m = i := by
    intro i hi
    obtain ⟨m, hm, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n)
      (t := Finset.range n) (fun m _ => s m)
      (fun m hm => Finset.mem_range.2 (hs m (Finset.mem_range.1 hm)))
      (fun m₁ m₂ h1 h2 e => inj m₁ (Finset.mem_range.1 h1) m₂ (Finset.mem_range.1 h2)
        (by rw [e])) le_rfl i (Finset.mem_range.2 hi)
    exact ⟨m, Finset.mem_range.1 hm, e.symm⟩
  intro i hi k hk e
  obtain ⟨m₁, h1, rfl⟩ := surj i hi
  obtain ⟨m₂, h2, rfl⟩ := surj k hk
  rw [inj m₁ h1 m₂ h2 e]

variable {G : Type*} [Group G]

@[expose] noncomputable def pt (ψ : G →* Equiv.Perm (Fin 3510)) (g : G) (z : ℕ) : ℕ :=
  if h : z < 3510 then (ψ g ⟨z, h⟩ : ℕ) else z

theorem pt_lt (ψ : G →* Equiv.Perm (Fin 3510)) (g : G) {z : ℕ} (hz : z < 3510) :
    pt ψ g z < 3510 := by
  rw [pt, dif_pos hz]
  exact (ψ g ⟨z, hz⟩).isLt

theorem pt_mul (ψ : G →* Equiv.Perm (Fin 3510)) (g h : G) (z : ℕ) :
    pt ψ (g * h) z = pt ψ g (pt ψ h z) := by
  by_cases hz : z < 3510
  · have h1 : pt ψ h z = (ψ h ⟨z, hz⟩ : ℕ) := dif_pos hz
    have h2 : pt ψ g (ψ h ⟨z, hz⟩ : ℕ) = (ψ g (ψ h ⟨z, hz⟩) : ℕ) :=
      dif_pos (ψ h ⟨z, hz⟩).isLt
    rw [h1, h2, pt, dif_pos hz, map_mul, Equiv.Perm.mul_apply]
  · have h1 : ∀ k : G, pt ψ k z = z := fun k => dif_neg hz
    rw [h1, h1, h1]

theorem pt_one (ψ : G →* Equiv.Perm (Fin 3510)) (z : ℕ) : pt ψ 1 z = z := by
  unfold pt
  split_ifs <;> simp

theorem ap_eq {ψ : G →* Equiv.Perm (Fin 3510)} {P : ℕ} {g : G} (h : PRep 3510 12 ψ P g) {z : ℕ}
    (hz : z < 3510) : ap P z = pt ψ g z := by
  rw [pt, dif_pos hz, ← h.2 ⟨z, hz⟩]
  rfl

theorem bp_lt6 : ∀ l < 6, bp l < 3510 := by
  intro l hl
  interval_cases l <;> decide

structure PairTab (ψ : G →* Equiv.Perm (Fin 3510)) (e : ℕ → G) (T : Subgroup G)
    (K M X V : ℕ → ℕ) : Prop where
  key : ∀ i < 729, PRep 3510 12 ψ (K i) (e i)
  one : e 0 = 1
  mem : ∀ g, g ∈ T ↔ ∃ i < 729, e i = g
  xc : ∀ x < 729, qpXC K X x = true
  oc : ∀ b < 729, qpOC K M X b = true
  cc : ∀ x < 729, qpCC K M X V x = true
  vc : ∀ r < 517, qpVC K M X V r = true

theorem xc_spec {K X : ℕ → ℕ} {x : ℕ} (h : qpXC K X x = true) :
    (∀ l < 6, qpE (X x) (2 + l) = ap (K x) (bp l)) ∧ qpE (X x) 0 < 729 ∧
      qpMul (K x) (X (qpE (X x) 0)) (X x) = true ∧
      sortC (fun i => fld(X i, nat_lit 32, nat_lit 79228162514264337593543950335))
        (fun q => qpE (X q) 1) 729 x = true := by
  unfold qpXC at h
  rw [sB_eq, sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  rw [sB_eq] at h2
  obtain ⟨h4, h5⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  exact ⟨fun l hl => beq_of (allBlk0_spec h1 l hl), blt_of h4, h5, h3⟩

namespace PairTab

variable {ψ : G →* Equiv.Perm (Fin 3510)} {e : ℕ → G} {T : Subgroup G} {K M X V : ℕ → ℕ}

theorem img (P : PairTab ψ e T K M X V) {x : ℕ} (hx : x < 729) :
    ∀ l < 6, qpE (X x) (2 + l) = pt ψ (e x) (bp l) := fun l hl => by
  rw [(xc_spec (P.xc x hx)).1 l hl, ap_eq (P.key x hx) (bp_lt6 l hl)]

theorem img_lt (P : PairTab ψ e T K M X V) {x : ℕ} (hx : x < 729) :
    ∀ l < 6, qpE (X x) (2 + l) < 3510 := fun l hl => by
  rw [P.img hx l hl]
  exact pt_lt ψ _ (bp_lt6 l hl)

theorem e_mem (P : PairTab ψ e T K M X V) {i : ℕ} (hi : i < 729) : e i ∈ T :=
  (P.mem _).2 ⟨i, hi, rfl⟩

theorem base_eq (P : PairTab ψ e T K M X V) {g h : G} (hg : g ∈ T) (hh : h ∈ T)
    (hb : ∀ l < 6, pt ψ g (bp l) = pt ψ h (bp l)) : g = h := by
  obtain ⟨i, hi, rfl⟩ := (P.mem g).1 hg
  obtain ⟨k, hk, rfl⟩ := (P.mem h).1 hh
  have hs : ∀ q < 729, sortC (fun i => fld(X i, nat_lit 32, nat_lit 79228162514264337593543950335))
      (fun q => qpE (X q) 1) 729 q = true := fun q hq => (xc_spec (P.xc q hq)).2.2.2
  have := qp_inj_of_sorted
    (key := fun i => fld(X i, nat_lit 32, nat_lit 79228162514264337593543950335))
    (fun m hm => (qp_sortC_spec (hs m hm)).1)
    (fun m hm => (qp_sortC_spec (hs m (by omega))).2 hm) i hi k hk
    (key96_eq (r := X i) (r' := X k) fun l hl => by rw [P.img hi l hl, P.img hk l hl, hb l hl])
  rw [this]

theorem mul_spec (P : PairTab ψ e T K M X V) {i j k : ℕ} (hi : i < 729) (hj : j < 729)
    (hk : k < 729) (h : qpMul (K i) (X j) (X k) = true) : e j = e i * e k := by
  refine P.base_eq (P.e_mem hj) (mul_mem (P.e_mem hi) (P.e_mem hk)) fun l hl => ?_
  have h1 := qpMul_spec h l hl
  rw [P.img hj l hl, P.img hk l hl, ap_eq (P.key i hi) (pt_lt ψ _ (bp_lt6 l hl))] at h1
  rw [h1, pt_mul]

theorem sq (P : PairTab ψ e T K M X V) {x : ℕ} (hx : x < 729) :
    qpE (X x) 0 < 729 ∧ e (qpE (X x) 0) = e x * e x := by
  obtain ⟨-, hs, hm, -⟩ := xc_spec (P.xc x hx)
  exact ⟨hs, P.mul_spec hx hs hx hm⟩

theorem oc_spec (P : PairTab ψ e T K M X V) {b : ℕ} (hb : b < 729) (hb0 : b ≠ 0)
    (h3 : e b ^ 3 = 1) : qpBit (M 0) b = true := by
  have h := P.oc b hb
  unfold qpOC at h
  have hb' : (Nat.beq b 0 = true) = False := by simp only [Nat.beq_eq, hb0]
  rw [bRec_eq, if_neg (by rw [hb']; exact id), bRec_eq] at h
  by_contra hq
  rw [if_neg hq, sB_eq, sB_eq, notB_eq, Bool.not_eq_true'] at h
  have hall : allBlk 0 (fun l => Nat.beq (ap (K b) (ap (K b) (qpE (X b) (2 + l)))) (bp l)) 6 =
      true := by
    refine allBlk0_intro fun l hl => ?_
    have hp := bp_lt6 l hl
    have e3 : e b * e b * e b = e b ^ 3 := by rw [pow_three, mul_assoc]
    rw [P.img hb l hl, ap_eq (P.key b hb) (pt_lt ψ _ hp),
      ap_eq (P.key b hb) (pt_lt ψ _ (pt_lt ψ _ hp)), ← pt_mul, ← pt_mul, e3, h3, pt_one]
    exact Nat.beq_refl _
  have hfalse : allBlk 0 (fun l => Nat.beq (ap (K b) (ap (K b) (qpE (X b) (2 + l)))) (bp l)) 6 =
      false := h
  rw [hall] at hfalse
  exact Bool.noConfusion hfalse

theorem cc_parts (P : PairTab ψ e T K M X V) {x : ℕ} (hx : x < 729)
    (hxO : qpBit (M 0) x = true) :
    (∀ b < 729, qpBit (M 0 &&& (qpFull ^^^ M (x + 1))) b = true →
      allBlk 0 (fun l => Nat.beq (ap (K x) (qpE (X b) (2 + l)))
        (ap (K b) (qpE (X x) (2 + l)))) 6 = false) ∧
    (∀ t < qpE (X x) 8, qpE (X x) (9 + t) < 517 ∧
      qpBit (qpVM (V (qpE (X x) (9 + t)))) x = true) ∧
    M (x + 1) &&& ((qpFull ^^^ foldN (qpE (X x) 8)
        (fun t s => Nat.lor s (qpVM (V (qpE (X x) (9 + t))))) 0) &&&
      (qpFull ^^^ (1 ||| (1 <<< x ||| 1 <<< qpE (X x) 0)))) = 0 := by
  have h := P.cc x hx
  unfold qpCC at h
  rw [bRec_eq, if_pos hxO, sB_eq, sB_eq, sB_eq, sB_eq] at h
  obtain ⟨hA, hB⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  rw [sB_eq] at hB
  obtain ⟨hB1, hB2⟩ := (CFSG.KS.bAnd_iff _ _).1 hB
  refine ⟨fun b hb hm => ?_, fun t ht => ?_, beq_of hB2⟩
  · have h1 := CFSG.KS.allN_spec hA b hb
    rw [bRec_eq] at h1
    split_ifs at h1 with hc
    · rw [sB_eq, sB_eq, notB_eq, Bool.not_eq_true'] at h1
      exact h1
    · exact absurd hm hc
  · have h2 := CFSG.KS.allN_spec hB1 t ht
    rw [sB_eq] at h2
    obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
    exact ⟨blt_of h3, h4⟩

theorem cc_comm (P : PairTab ψ e T K M X V) {x b : ℕ} (hx : x < 729)
    (hxO : qpBit (M 0) x = true) (hb : b < 729) (hbO : qpBit (M 0) b = true)
    (hc : e x * e b = e b * e x) : qpBit (M (x + 1)) b = true := by
  by_contra hn
  have hm : qpBit (M 0 &&& (qpFull ^^^ M (x + 1))) b = true := by
    rw [qpBit_iff] at hn hbO ⊢
    rw [Bool.not_eq_true] at hn
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_qpFull, hbO, hn]
    simp [hb]
  have h1 := (P.cc_parts hx hxO).1 b hb hm
  have h2 : allBlk 0 (fun l => Nat.beq (ap (K x) (qpE (X b) (2 + l)))
      (ap (K b) (qpE (X x) (2 + l)))) 6 = true := by
    refine allBlk0_intro fun l hl => ?_
    have hp := bp_lt6 l hl
    rw [P.img hb l hl, P.img hx l hl, ap_eq (P.key x hx) (pt_lt ψ _ hp),
      ap_eq (P.key b hb) (pt_lt ψ _ hp), ← pt_mul, ← pt_mul, hc]
    exact Nat.beq_refl _
  rw [h2] at h1
  exact Bool.noConfusion h1

theorem cc_cover (P : PairTab ψ e T K M X V) {x i : ℕ} (hx : x < 729)
    (hxO : qpBit (M 0) x = true) (hi : i < 729) (hci : qpBit (M (x + 1)) i = true)
    (h0 : i ≠ 0) (h1 : i ≠ x) (h2 : i ≠ qpE (X x) 0) :
    ∃ r < 517, qpBit (qpVM (V r)) x = true ∧ qpBit (qpVM (V r)) i = true := by
  obtain ⟨-, hv, hz⟩ := P.cc_parts hx hxO
  have hb := congrArg (fun z => z.testBit i) hz
  rw [qpBit_iff] at hci
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, testBit_qpFull, testBit_shl1,
    testBit_one_ne h0, Nat.zero_testBit, hci, hi, decide_true, Bool.true_and, Bool.true_xor,
    Bool.false_or] at hb
  have hU : (foldN (qpE (X x) 8) (fun t s => Nat.lor s (qpVM (V (qpE (X x) (9 + t))))) 0).testBit
      i = true := by
    by_contra hn
    rw [Bool.not_eq_true] at hn
    rw [hn] at hb
    simp [Ne.symm h1, Ne.symm h2] at hb
  obtain ⟨t, ht, hti⟩ := (testBit_foldOr _ _ _).1 hU
  obtain ⟨hr, hrx⟩ := hv t ht
  exact ⟨_, hr, hrx, (qpBit_iff _ _).2 hti⟩

theorem vc_spec (P : PairTab ψ e T K M X V) {r : ℕ} (hr : r < 517) :
    (∀ t < 9, qpE (V r) t < 729) ∧ qpBit (M 0) (qpE (V r) 3) = true ∧
    qpBit (M 0) (qpE (V r) 1) = true ∧
    (∀ t < 9, e (qpE (V r) t) = e (qpE (V r) 3) ^ (t / 3) * e (qpE (V r) 1) ^ (t % 3)) ∧
    e (qpE (V r) 3) ^ 3 = 1 ∧ e (qpE (V r) 1) ^ 3 = 1 ∧
    e (qpE (V r) 3) * e (qpE (V r) 1) = e (qpE (V r) 1) * e (qpE (V r) 3) ∧
    (∀ u < qpE (V r) 9, qpE (V r) (10 + u) < 81 ∧
      ∀ t < 9, qpBit (M (730 + qpE (V r) (10 + u))) (qpE (V r) t) = true) ∧
    (∀ i < 729, qpBit (M (qpE (V r) 3 + 1)) i = true → qpBit (M (qpE (V r) 1 + 1)) i = true →
      (∀ t < 9, qpE (V r) t ≠ i) →
      ∃ u < qpE (V r) 9, qpBit (M (730 + qpE (V r) (10 + u))) i = true) := by
  have h := P.vc r hr
  unfold qpVC at h
  rw [sB_eq, sB_eq, sB_eq] at h
  obtain ⟨h0, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hlt, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨haO, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hbO, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  rw [sB_eq, sB_eq] at h
  obtain ⟨hch, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨ha2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hb2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hab, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  rw [sB_eq, sB_eq] at h
  obtain ⟨hrec, hcov⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  set w := fun t => qpE (V r) t with hw
  have hw' : ∀ t < 9, w t < 729 := fun t ht => blt_of (CFSG.KS.allN_spec hlt t ht)
  have hw0 : w 0 = 0 := beq_of h0
  have hB : ∀ t, 1 ≤ t → t < 3 → e (w t) = e (w 1) * e (w (t - 1)) := by
    intro t ht1 ht3
    have h1 := CFSG.KS.allN_spec hch t (by change t < 9; omega)
    have hn0 : ¬ (Nat.beq t 0 = true) := by
      rw [Nat.beq_eq]
      omega
    rw [bRec_eq, if_pos (Eq.mpr Nat.blt_eq ht3), bRec_eq, if_neg hn0] at h1
    exact P.mul_spec (hw' 1 (by norm_num)) (hw' t (by omega)) (hw' _ (by omega)) h1
  have hA : ∀ t, 3 ≤ t → t < 9 → e (w t) = e (w 3) * e (w (t - 3)) := by
    intro t ht3 ht9
    have h1 := CFSG.KS.allN_spec hch t ht9
    have hn3 : ¬ (Nat.blt t 3 = true) := by
      rw [Nat.blt_eq]
      omega
    rw [bRec_eq, if_neg hn3] at h1
    exact P.mul_spec (hw' 3 (by norm_num)) (hw' t ht9) (hw' _ (by omega)) h1
  have he0 : e (w 0) = 1 := by rw [hw0, P.one]
  have hpow : ∀ t < 9, e (w t) = e (w 3) ^ (t / 3) * e (w 1) ^ (t % 3) := by
    have e2 : e (w 2) = e (w 1) * e (w 1) := hB 2 (by norm_num) (by norm_num)
    have e4 : e (w 4) = e (w 3) * e (w 1) := hA 4 (by norm_num) (by norm_num)
    have e5 : e (w 5) = e (w 3) * e (w 2) := hA 5 (by norm_num) (by norm_num)
    have e6 : e (w 6) = e (w 3) * e (w 3) := hA 6 (by norm_num) (by norm_num)
    have e7 : e (w 7) = e (w 3) * e (w 4) := hA 7 (by norm_num) (by norm_num)
    have e8 : e (w 8) = e (w 3) * e (w 5) := hA 8 (by norm_num) (by norm_num)
    intro t ht
    interval_cases t <;>
      simp only [he0, e2, e4, e5, e6, e7, e8, Nat.reduceDiv, Nat.reduceMod] <;>
      simp [pow_two, mul_assoc]
  have hone : e 0 = 1 := P.one
  have ha3 : e (w 3) ^ 3 = 1 := by
    have h1 := P.mul_spec (hw' 3 (by norm_num)) (by norm_num) (hw' 6 (by norm_num)) ha2
    rw [hone, hpow 6 (by norm_num)] at h1
    norm_num at h1
    rw [pow_three, ← pow_two, h1]
  have hb3 : e (w 1) ^ 3 = 1 := by
    have h1 := P.mul_spec (hw' 1 (by norm_num)) (by norm_num) (hw' 2 (by norm_num)) hb2
    rw [hone, hpow 2 (by norm_num)] at h1
    norm_num at h1
    rw [pow_three, ← pow_two, h1]
  have hcomm : e (w 3) * e (w 1) = e (w 1) * e (w 3) := by
    have h1 := P.mul_spec (hw' 1 (by norm_num)) (hw' 4 (by norm_num)) (hw' 3 (by norm_num)) hab
    rw [hpow 4 (by norm_num)] at h1
    norm_num at h1
    exact h1
  have hvm : ∀ t < 9, (qpVM (V r)).testBit (w t) = true := fun t ht =>
    (qpVM_bit _ _).2 ⟨t, ht, rfl⟩
  refine ⟨hw', haO, hbO, hpow, ha3, hb3, hcomm, fun u hu => ?_, fun i hi hia hib hn => ?_⟩
  · have h1 := CFSG.KS.allN_spec hrec u hu
    rw [sB_eq] at h1
    obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h1
    have h4 : qpVM (V r) &&& (qpFull ^^^ M (730 + w (10 + u))) = 0 := beq_of h3
    refine ⟨blt_of h2, fun t ht => ?_⟩
    have h5 := congrArg (fun z => z.testBit (w t)) h4
    simp only [Nat.testBit_and, Nat.testBit_xor, testBit_qpFull, hvm t ht, hw' t ht,
      decide_true, Bool.true_and, Bool.true_xor, Nat.zero_testBit, Bool.not_eq_false'] at h5
    rw [qpBit_iff]
    simpa using h5
  · have h4 : (M (w 3 + 1) &&& M (w 1 + 1)) &&& ((qpFull ^^^ qpVM (V r)) &&&
        (qpFull ^^^ foldN (w 9) (fun t s => Nat.lor s (M (730 + w (10 + t)))) 0)) = 0 :=
      beq_of hcov
    have h5 := congrArg (fun z => z.testBit i) h4
    have hvi : (qpVM (V r)).testBit i = false := by
      by_contra hc
      rw [Bool.not_eq_false, qpVM_bit] at hc
      obtain ⟨t, ht, e⟩ := hc
      exact hn t ht e
    have hia' : (M (w 3 + 1)).testBit i = true := (qpBit_iff _ _).1 hia
    have hib' : (M (w 1 + 1)).testBit i = true := (qpBit_iff _ _).1 hib
    simp only [Nat.testBit_and, Nat.testBit_xor, testBit_qpFull, hia', hib', hvi, hi,
      decide_true, Bool.true_and, Bool.true_xor, Nat.zero_testBit, Bool.xor_false,
      Bool.not_eq_false'] at h5
    have hU : (foldN (w 9) (fun t s => Nat.lor s (M (730 + w (10 + t)))) 0).testBit i = true := by
      simpa using h5
    obtain ⟨u, hu, hui⟩ := (testBit_foldOr _ _ _).1 hU
    exact ⟨u, hu, (qpBit_iff _ _).2 hui⟩

end PairTab

theorem pow_mod3 {g : G} (h : g ^ 3 = 1) (i : ℕ) : g ^ (i % 3) = g ^ i := by
  conv_rhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, h, one_pow, one_mul]

theorem inv_pow3 {g : G} (h : g ^ 3 = 1) (i : ℕ) : (g ^ i)⁻¹ = g ^ (2 * i) := by
  refine inv_eq_of_mul_eq_one_right ?_
  have e3 : i + 2 * i = 3 * i := by ring
  rw [← pow_add, e3, pow_mul, h, one_pow]

theorem closure_pair [Finite G] {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a) :
    (∀ g ∈ closure ({a, b} : Set G), ∃ i j : ℕ, a ^ i * b ^ j = g) ∧
      Nat.card (closure ({a, b} : Set G)) ≤ 9 := by
  have hc : Commute a b := hab
  have hmul : ∀ i j k l : ℕ, a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
    intro i j k l
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
          simp only [mul_assoc]
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [← (hc.pow_pow k j).eq]
      _ = a ^ (i + k) * b ^ (j + l) := by simp only [pow_add, mul_assoc]
  have hS : ∀ g ∈ closure ({a, b} : Set G), ∃ i j : ℕ, a ^ i * b ^ j = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul g h _ _ ihg ihh =>
      obtain ⟨i, j, rfl⟩ := ihg
      obtain ⟨k, l, rfl⟩ := ihh
      exact ⟨i + k, j + l, (hmul i j k l).symm⟩
    | inv g _ ih =>
      obtain ⟨i, j, rfl⟩ := ih
      refine ⟨2 * i, 2 * j, ?_⟩
      rw [mul_inv_rev, inv_pow3 ha, inv_pow3 hb, ← (hc.pow_pow _ _).eq]
  refine ⟨hS, ?_⟩
  have haV : a ∈ closure ({a, b} : Set G) := subset_closure (by simp)
  have hbV : b ∈ closure ({a, b} : Set G) := subset_closure (by simp)
  let F : Fin 3 × Fin 3 → closure ({a, b} : Set G) := fun p =>
    ⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), mul_mem (pow_mem haV _) (pow_mem hbV _)⟩
  have hF : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨i, j, rfl⟩ := hS g hg
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    change a ^ (i % 3) * b ^ (j % 3) = a ^ i * b ^ j
    rw [pow_mod3 ha, pow_mod3 hb]
  have := Nat.card_le_card_of_surjective F hF
  simpa [Nat.card_prod] using this

theorem card_dvd27 [Finite G] {H A : Subgroup G} (hle : H ≤ A) (hA : Nat.card A = 27) :
    Nat.card H = 1 ∨ Nat.card H = 3 ∨ Nat.card H = 9 ∨ Nat.card H = 27 := by
  have hd : Nat.card H ∣ 3 ^ 3 := by
    have e27 : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [e27, ← hA]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  interval_cases k <;> simp [he]

namespace PairTab

variable {ψ : G →* Equiv.Perm (Fin 3510)} {e : ℕ → G} {T : Subgroup G} {K M X V : ℕ → ℕ}

theorem e27_le_record [Finite G] (P : PairTab ψ e T K M X V) (A : Subgroup G) (hAT : A ≤ T)
    (hcard : Nat.card A = 27) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ 3 = 1) :
    ∃ c < 81, A ≤ closure {g | ∃ i < 729, qpBit (M (730 + c)) i = true ∧ e i = g} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have idx : ∀ g ∈ A, ∃ i < 729, e i = g := fun g hg => (P.mem g).1 (hAT hg)
  have inO : ∀ i < 729, e i ∈ A → e i ≠ 1 → qpBit (M 0) i = true := fun i hi hA h1 =>
    P.oc_spec hi (fun h0 => h1 (by rw [h0, P.one])) (hexp _ hA)
  obtain ⟨x, hxA, hx1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 hno
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hzx : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hexp x hxA) hx1]
  obtain ⟨y, hyA, hyx⟩ : ∃ y ∈ A, y ∉ zpowers x := by
    by_contra hno
    push Not at hno
    have hle : A ≤ zpowers x := hno
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨ix, hix, rfl⟩ := idx x hxA
  obtain ⟨iy, hiy, rfl⟩ := idx y hyA
  have hxO := inO ix hix hxA hx1
  have hy1 : e iy ≠ 1 := fun h => hyx (by rw [h]; exact (zpowers (e ix)).one_mem)
  have hyO := inO iy hiy hyA hy1
  have hyC := P.cc_comm hix hxO hiy hyO (hcomm _ hxA _ hyA)
  obtain ⟨-, hes⟩ := P.sq hix
  obtain ⟨r, hr, hrx, hry⟩ := P.cc_cover hix hxO hiy hyC
    (fun h => hy1 (by rw [h, P.one]))
    (fun h => hyx (by rw [h]; exact mem_zpowers _))
    (fun h => hyx (by rw [h, hes]; exact mul_mem (mem_zpowers _) (mem_zpowers _)))
  obtain ⟨hw, haO, hbO, hpow, ha3, hb3, hab, hrec, hcov⟩ := P.vc_spec hr
  obtain ⟨hS, hV9⟩ := closure_pair ha3 hb3 hab
  set Vs := closure ({e (qpE (V r) 3), e (qpE (V r) 1)} : Set G) with hVs
  have haV : e (qpE (V r) 3) ∈ Vs := subset_closure (by simp)
  have hbV : e (qpE (V r) 1) ∈ Vs := subset_closure (by simp)
  have hwV : ∀ t < 9, e (qpE (V r) t) ∈ Vs := fun t ht => by
    rw [hpow t ht]
    exact mul_mem (pow_mem haV _) (pow_mem hbV _)
  have hinV : ∀ i, qpBit (qpVM (V r)) i = true → e i ∈ Vs := fun i hi => by
    rw [qpBit_iff, qpVM_bit] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    exact hwV t ht
  set Pg := closure ({e ix, e iy} : Set G) with hPg
  have hPA : Pg ≤ A := (closure_le A).2 (by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hxA
    · exact hyA)
  have hPV : Pg ≤ Vs := (closure_le Vs).2 (by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hinV _ hrx
    · exact hinV _ hry)
  have hxP : zpowers (e ix) ≤ Pg := (Subgroup.zpowers_le).2 (subset_closure (by simp))
  have hyP : e iy ∈ Pg := subset_closure (by simp)
  have hP9 : Nat.card Pg = 9 := by
    have hle := Subgroup.card_le_of_le hPV
    rcases card_dvd27 hPA hcard with h | h | h | h
    · have := Subgroup.card_le_of_le hxP
      omega
    · exact absurd (Subgroup.eq_of_le_of_card_ge hxP (by omega) ▸ hyP) hyx
    · exact h
    · omega
  have hPeq : Pg = Vs := Subgroup.eq_of_le_of_card_ge hPV (by omega)
  have hVA : Vs ≤ A := hPeq ▸ hPA
  obtain ⟨z, hzA, hzV⟩ : ∃ z ∈ A, z ∉ Vs := by
    by_contra hno
    push Not at hno
    have hle : A ≤ Vs := hno
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨iz, hiz, rfl⟩ := idx z hzA
  have hz1 : e iz ≠ 1 := fun h => hzV (by rw [h]; exact Vs.one_mem)
  have hzO := inO iz hiz hzA hz1
  have hza := P.cc_comm (hw 3 (by norm_num)) haO hiz hzO (hcomm _ (hVA haV) _ hzA)
  have hzb := P.cc_comm (hw 1 (by norm_num)) hbO hiz hzO (hcomm _ (hVA hbV) _ hzA)
  obtain ⟨u, hu, hzR⟩ := hcov iz hiz hza hzb (fun t ht h => hzV (h ▸ hwV t ht))
  obtain ⟨hc81, hcw⟩ := hrec u hu
  refine ⟨_, hc81, ?_⟩
  set R := closure {g | ∃ i < 729, qpBit (M (730 + qpE (V r) (10 + u))) i = true ∧ e i = g}
    with hR
  have hVR : Vs ≤ R := (closure_le R).2 (by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact subset_closure ⟨_, hw 3 (by norm_num), hcw 3 (by norm_num), rfl⟩
    · exact subset_closure ⟨_, hw 1 (by norm_num), hcw 1 (by norm_num), rfl⟩)
  have hzR' : e iz ∈ R := subset_closure ⟨iz, hiz, hzR, rfl⟩
  have hVQ : Vs ≤ A ⊓ R := le_inf hVA hVR
  have hQ : Nat.card ↥(A ⊓ R) = 27 := by
    have hV9' : Nat.card Vs = 9 := hPeq ▸ hP9
    have hd : Nat.card Vs ∣ Nat.card ↥(A ⊓ R) := Subgroup.card_dvd_of_le hVQ
    rcases card_dvd27 (inf_le_left : A ⊓ R ≤ A) hcard with h | h | h | h
    · rw [h, hV9'] at hd
      omega
    · rw [h, hV9'] at hd
      omega
    · exact absurd ((Subgroup.eq_of_le_of_card_ge hVQ (by omega)).symm ▸
        (Subgroup.mem_inf.2 ⟨hzA, hzR'⟩)) hzV
    · exact h
  have hQA : A ⊓ R = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  intro g hg
  rw [← hQA] at hg
  exact (Subgroup.mem_inf.1 hg).2

end PairTab

end CFSG.KS.Fi22Twist

end
