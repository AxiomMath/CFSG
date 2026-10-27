module

public import CFSG.Certificates.Kernel.J4.Words
public import CFSG.Certificates.Kernel.DceWords
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.J4Words

open CFSG.Certificates.KB.Sound CFSG.Certificates.DceLoop CFSG.Certificates.DceWord

variable {G : Type*} [Group G]

theorem wLet_eq : CFSG.KJ4.wLet = CFSG.KC.Th.wLet := rfl
theorem lInv_eq : CFSG.KJ4.lInv = CFSG.KC.Th.lInv := rfl
theorem strip_eq : CFSG.KJ4.strip = CFSG.KC.Th.strip := rfl
theorem rot_eq : CFSG.KJ4.rot = CFSG.KC.Th.rot := rfl
theorem isRot_eq : CFSG.KJ4.isRot = CFSG.KC.Th.isRot := rfl
theorem isRelRot_eq : CFSG.KJ4.isRelRot = CFSG.KC.Th.isRelRot := rfl
theorem freeRed_eq : CFSG.KJ4.freeRed = CFSG.KC.Th.freeRed := rfl
theorem chkWord_eq : CFSG.KJ4.chkWord = CFSG.KC.Th.chkWord := rfl
theorem wInv_eq : CFSG.KJ4.wInv = CFSG.KC.Th.wInv := rfl
theorem wCat_eq : CFSG.KJ4.wCat = CFSG.KC.Th.wCat := rfl

theorem chkPsiRel_eq (inv T sw ns pw np r m : ℕ) :
    CFSG.KJ4.chkPsiRel inv T sw ns pw np r m = CFSG.KC.Th.chkPsiRel inv T T sw ns pw np r m := rfl

theorem andB_iff {a b : Bool} : CFSG.KJ4.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem wLet_byteG (w i : ℕ) : CFSG.KJ4.wLet w i = byteG w i := rfl

theorem wLet_lt (w i : ℕ) : CFSG.KJ4.wLet w i < 256 := by
  rw [wLet_eq, DceWord.wLet_eq]
  exact byte_lt w i

theorem wv_one (v : ℕ → G) {c : ℕ} (hc : c < 256) : wv v c 1 = v c := by
  have : byteG c 0 = c := by
    rw [byteG_eq, byte_eq']
    simp [Nat.mod_eq_of_lt hc]
  simp [wv, this]

theorem wCat_lt {a na b nb : ℕ} (ha : a < 256 ^ na) (hb : b < 256 ^ nb) :
    CFSG.KJ4.wCat a na b < 256 ^ (na + nb) := by
  rw [wCat_eq, DceWord.wCat_eq a na b ha, pow_add]
  calc a + 256 ^ na * b < 256 ^ na + 256 ^ na * b := by omega
    _ = 256 ^ na * (b + 1) := by ring
    _ ≤ 256 ^ na * 256 ^ nb := Nat.mul_le_mul_left _ hb

theorem bytes_wCat {a na b nb : ℕ} (ha : a < 256 ^ na) (hb : b < 256 ^ nb) :
    bytes (CFSG.KJ4.wCat a na b) (na + nb) = bytes a na ++ bytes b nb := by
  have e : a + 256 ^ na * b = pkb 256 (bytes a na ++ bytes b nb) := by
    rw [pkb_append, bytes_length, pkb_bytes ha, pkb_bytes hb]
  have h256 : ∀ d ∈ bytes a na ++ bytes b nb, d < 256 := fun d hd => by
    rcases List.mem_append.1 hd with h | h
    · exact bytes_lt a na d h
    · exact bytes_lt b nb d h
  rw [wCat_eq, DceWord.wCat_eq a na b ha, e, bytes_of_pkb h256 (by simp [bytes_length])]

theorem wv_wCat (v : ℕ → G) {a na b nb : ℕ} (ha : a < 256 ^ na) (hb : b < 256 ^ nb) :
    wv v (CFSG.KJ4.wCat a na b) (na + nb) = wv v a na * wv v b nb :=
  DceWord.wv_wCat v ha hb

theorem wCat_lt' {a na b nb k : ℕ} (ha : a < 256 ^ na) (hb : b < 256 ^ nb) (hk : na + nb = k) :
    CFSG.KJ4.wCat a na b < 256 ^ k := hk ▸ wCat_lt ha hb

theorem wv_wCat' (v : ℕ → G) {a na b nb k : ℕ} (ha : a < 256 ^ na) (hb : b < 256 ^ nb)
    (hk : na + nb = k) : wv v (CFSG.KJ4.wCat a na b) k = wv v a na * wv v b nb :=
  hk ▸ wv_wCat v ha hb

theorem wInv_lt (inv w n : ℕ) : CFSG.KJ4.wInv inv w n < 256 ^ n := DceWord.wInv_lt inv w n

theorem bytes_wInv (inv w n : ℕ) :
    bytes (CFSG.KJ4.wInv inv w n) n = (bytes w n).reverse.map (CFSG.KJ4.lInv inv) := by
  have h256 : ∀ d ∈ (bytes w n).reverse.map (CFSG.KC.Th.lInv inv), d < 256 := by
    intro d hd
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hd
    exact lInv_lt inv c
  rw [wInv_eq, DceWord.wInv_eq, bytes_of_pkb h256 (by simp [bytes_length])]
  rfl

theorem wv_wInv (v : ℕ → G) (inv w n : ℕ)
    (hinv : ∀ q < n, v (CFSG.KJ4.lInv inv (CFSG.KJ4.wLet w q)) = (v (CFSG.KJ4.wLet w q))⁻¹) :
    wv v (CFSG.KJ4.wInv inv w n) n = (wv v w n)⁻¹ :=
  DceWord.wv_wInv v inv w n (fun q hq => by
    have := hinv q hq
    rwa [lInv_eq, wLet_byteG, DceWord.lInv_eq] at this)

theorem strip_spec (w n : ℕ) : CFSG.KJ4.strip w n =
    (pkb 256 ((bytes w n).filter (· ≠ 255)), ((bytes w n).filter (· ≠ 255)).length) :=
  DceWord.strip_spec w n

theorem isRot_val (v : ℕ → G) {r n w : ℕ} (hr : r < 256 ^ n) (h1 : wv v r n = 1)
    (h : CFSG.KJ4.isRot r n w = true) : wv v w n = 1 := by
  obtain ⟨s, -, rfl⟩ := isRot_spec h
  exact wv_rot v hr h1 s

theorem isRelRot_val (f : ℕ → G) {r m w n : ℕ} (hr : r < 256 ^ m) (hr1 : wv f r m = 1)
    (h : CFSG.KJ4.isRelRot r m w n = true) : wv (lvE f) w n = 1 := by
  rw [isRelRot_eq] at h
  unfold CFSG.KC.Th.isRelRot at h
  rw [DceWord.strip_spec] at h
  change CFSG.KC.Th.andB _ _ = true at h
  obtain ⟨h1, h2⟩ := thAnd_iff.1 h
  obtain ⟨s, -, hs⟩ := isRot_spec h2
  set l := (bytes w n).filter (· ≠ 255)
  have hm : l.length = m := Nat.eq_of_beq_eq_true h1
  have hl256 : ∀ d ∈ l, d < 256 := fun d hd => bytes_lt w n d (List.mem_of_mem_filter hd)
  have e1 : bytes (pkb 256 l) m = l := by
    rw [← hm]
    exact bytes_pkb l hl256
  have hrot := wv_rot f hr hr1 s
  rw [hs, wv_eq, e1] at hrot
  rw [wv_eq, ← lv_filter (lvE f) 255 (by simp [lvE])]
  rw [← hrot]
  unfold lv
  congr 1
  refine List.map_congr_left fun d hd => ?_
  have : d ≠ 255 := by simpa using (List.mem_filter.1 hd).2
  simp [lvE, this]

theorem chkWord_val (f : ℕ → G) {inv w n r m : ℕ} (hr : r < 256 ^ m) (hr1 : wv f r m = 1)
    (hinv : ∀ q < n, CFSG.KJ4.wLet w q ≠ 255 →
      f (CFSG.KJ4.lInv inv (CFSG.KJ4.wLet w q)) = (f (CFSG.KJ4.wLet w q))⁻¹)
    (h : CFSG.KJ4.chkWord inv w n r m = true) : wv (lvE f) w n = 1 :=
  chkWord_sound f hr hr1 (fun q hq hne => by
    have := hinv q hq hne
    rwa [lInv_eq, wLet_byteG, DceWord.lInv_eq] at this) h

theorem pkb_inj : ∀ {l₁ l₂ : List ℕ}, (∀ d ∈ l₁, 0 < d ∧ d < 256) → (∀ d ∈ l₂, 0 < d ∧ d < 256) →
    pkb 256 l₁ = pkb 256 l₂ → l₁ = l₂
  | [], l₂, _, h₂, h => (pkb_eq_zero (fun d hd => (h₂ d hd).1) h.symm).symm
  | a :: l₁, [], h₁, _, h => pkb_eq_zero (fun d hd => (h₁ d hd).1) h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [pkb_cons, pkb_cons] at h
    have ha := (h₁ a (by simp)).2
    have hb := (h₂ b (by simp)).2
    have hab : a = b := by omega
    subst hab
    have : pkb 256 l₁ = pkb 256 l₂ := by omega
    rw [pkb_inj (fun d hd => h₁ d (by simp [hd])) (fun d hd => h₂ d (by simp [hd])) this]

theorem freeRed_stack' (f : ℕ → G) (inv w n : ℕ)
    (hinv : ∀ q < n, CFSG.KJ4.wLet w q ≠ 255 →
      f (CFSG.KJ4.lInv inv (CFSG.KJ4.wLet w q)) = (f (CFSG.KJ4.wLet w q))⁻¹) :
    ∃ st : List ℕ, CFSG.KJ4.freeRed inv w n = pkb 256 (st.map (· + 1)) ∧
      (∀ d ∈ st, d < 255) ∧ wv (lvE f) w n = lv f st.reverse := by
  obtain ⟨st, h1, h2, h3⟩ := freeRed_stack f inv w n (fun q hq hne => by
    have := hinv q hq (by rwa [wLet_eq, DceWord.wLet_eq])
    rwa [lInv_eq, wLet_eq, CFSG.KC.Th.lInv, DceWord.wLet_eq, DceWord.wLet_eq] at this) n le_rfl
  exact ⟨st, h1, h2, by rw [wv_eq, h3]⟩

theorem freeRed_val (f : ℕ → G) {inv u n v m : ℕ}
    (hu : ∀ q < n, CFSG.KJ4.wLet u q ≠ 255 →
      f (CFSG.KJ4.lInv inv (CFSG.KJ4.wLet u q)) = (f (CFSG.KJ4.wLet u q))⁻¹)
    (hv : ∀ q < m, CFSG.KJ4.wLet v q ≠ 255 →
      f (CFSG.KJ4.lInv inv (CFSG.KJ4.wLet v q)) = (f (CFSG.KJ4.wLet v q))⁻¹)
    (h : CFSG.KJ4.freeRed inv u n = CFSG.KJ4.freeRed inv v m) :
    wv (lvE f) u n = wv (lvE f) v m := by
  obtain ⟨s₁, e₁, l₁, v₁⟩ := freeRed_stack' f inv u n hu
  obtain ⟨s₂, e₂, l₂, v₂⟩ := freeRed_stack' f inv v m hv
  have hb : ∀ s : List ℕ, (∀ d ∈ s, d < 255) → ∀ d ∈ s.map (· + 1), 0 < d ∧ d < 256 := by
    intro s hs d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    have := hs c hc
    omega
  have hs : s₁ = s₂ := by
    have := pkb_inj (hb s₁ l₁) (hb s₂ l₂) (by rw [← e₁, ← e₂, h])
    exact List.map_injective_iff.2 (add_left_injective 1) this
  rw [v₁, v₂, hs]

theorem freeRed_val' (f : ℕ → G) {inv u n v m : ℕ}
    (hI : ∀ c < 255, f (CFSG.KJ4.lInv inv c) = (f c)⁻¹)
    (h : CFSG.KJ4.freeRed inv u n = CFSG.KJ4.freeRed inv v m) :
    wv (lvE f) u n = wv (lvE f) v m :=
  freeRed_val f (fun q _ hne => hI _ (by have := wLet_lt u q; omega))
    (fun q _ hne => hI _ (by have := wLet_lt v q; omega)) h

@[expose] noncomputable def zsub (f : ℕ → G) (Z Zi : G) (c : ℕ) : G :=
  if c = 5 then Z else if c = 6 then Zi else f c

theorem substZ_val (f : ℕ → G) (w zw zwi m : ℕ) (hzw : zw < 256 ^ m) (hzwi : zwi < 256 ^ m) :
    ∀ n, (CFSG.KJ4.substZ w n zw zwi m).1 < 256 ^ (CFSG.KJ4.substZ w n zw zwi m).2 ∧
      wv (lvE f) (CFSG.KJ4.substZ w n zw zwi m).1 (CFSG.KJ4.substZ w n zw zwi m).2 =
        wv (lvE (zsub f (wv (lvE f) zw m) (wv (lvE f) zwi m))) w n
  | 0 => ⟨by simp [CFSG.KJ4.substZ], by simp [CFSG.KJ4.substZ, wv]⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := substZ_val f w zw zwi m hzw hzwi n
    have hst : CFSG.KJ4.substZ w (n + 1) zw zwi m =
        Prod.rec (motive := fun _ => ℕ × ℕ) (fun v k =>
          Bool.rec
            (Bool.rec (Prod.mk (CFSG.KJ4.wCat v k (CFSG.KJ4.wLet w n)) (Nat.succ k))
              (Prod.mk (CFSG.KJ4.wCat v k zwi) (Nat.add k m)) (Nat.beq (CFSG.KJ4.wLet w n) 6))
            (Prod.mk (CFSG.KJ4.wCat v k zw) (Nat.add k m)) (Nat.beq (CFSG.KJ4.wLet w n) 5))
          (CFSG.KJ4.substZ w n zw zwi m) := rfl
    rw [hst]
    rcases hp : CFSG.KJ4.substZ w n zw zwi m with ⟨v, k⟩
    rw [hp] at ih1 ih2
    dsimp only at ih1 ih2 ⊢
    have hval : wv (lvE (zsub f (wv (lvE f) zw m) (wv (lvE f) zwi m))) w (n + 1) =
        wv (lvE f) v k * lvE (zsub f (wv (lvE f) zw m) (wv (lvE f) zwi m)) (CFSG.KJ4.wLet w n) := by
      rw [wv_succ, ih2]
      rfl
    rw [hval]
    set c := CFSG.KJ4.wLet w n with hc
    have hc256 : c < 256 := wLet_lt w n
    cases h5 : Nat.beq c 5
    · have hn5 : c ≠ 5 := Nat.ne_of_beq_eq_false h5
      cases h6 : Nat.beq c 6
      · have hn6 : c ≠ 6 := Nat.ne_of_beq_eq_false h6
        refine ⟨wCat_lt (nb := 1) ih1 (by simpa using hc256), ?_⟩
        change wv (lvE f) (CFSG.KJ4.wCat v k c) (k + 1) = _
        rw [wv_wCat _ ih1 (by simpa using hc256), wv_one _ hc256]
        congr 1
        by_cases h255 : c = 255
        · simp [lvE, h255]
        · simp [lvE, zsub, h255, hn5, hn6]
      · have he6 : c = 6 := Nat.eq_of_beq_eq_true h6
        refine ⟨wCat_lt ih1 hzwi, ?_⟩
        change wv (lvE f) (CFSG.KJ4.wCat v k zwi) (k + m) = _
        rw [wv_wCat _ ih1 hzwi]
        simp [lvE, zsub, he6]
    · have he5 : c = 5 := Nat.eq_of_beq_eq_true h5
      refine ⟨wCat_lt ih1 hzw, ?_⟩
      change wv (lvE f) (CFSG.KJ4.wCat v k zw) (k + m) = _
      rw [wv_wCat _ ih1 hzw]
      simp [lvE, zsub, he5]

theorem chkSubst_val (f : ℕ → G) {w n zw zwi m u k : ℕ} (hzw : zw < 256 ^ m)
    (hzwi : zwi < 256 ^ m) (h : CFSG.KJ4.chkSubst w n zw zwi m u k = true) :
    wv (lvE (zsub f (wv (lvE f) zw m) (wv (lvE f) zwi m))) w n = wv (lvE f) u k := by
  obtain ⟨-, h2⟩ := substZ_val f w zw zwi m hzw hzwi n
  unfold CFSG.KJ4.chkSubst at h
  rcases hp : CFSG.KJ4.substZ w n zw zwi m with ⟨v, l⟩
  rw [hp] at h h2
  change CFSG.KJ4.andB _ _ = true at h
  obtain ⟨e1, e2⟩ := andB_iff.1 h
  rw [← h2, Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2]

theorem chkSubstRed_val (f : ℕ → G) {inv w n zw zwi m u k : ℕ}
    (hI : ∀ c < 255, f (CFSG.KJ4.lInv inv c) = (f c)⁻¹) (hzw : zw < 256 ^ m)
    (hzwi : zwi < 256 ^ m) (h : CFSG.KJ4.chkSubstRed inv w n zw zwi m u k = true) :
    wv (lvE (zsub f (wv (lvE f) zw m) (wv (lvE f) zwi m))) w n = wv (lvE f) u k := by
  obtain ⟨-, h2⟩ := substZ_val f w zw zwi m hzw hzwi n
  unfold CFSG.KJ4.chkSubstRed at h
  rcases hp : CFSG.KJ4.substZ w n zw zwi m with ⟨v, l⟩
  rw [hp] at h h2
  rw [← h2]
  exact freeRed_val' f hI (Nat.eq_of_beq_eq_true h)

theorem chkPsiRel_val (v : ℕ → G) {inv T sw ns pw np r m : ℕ} (hr : r < 256 ^ m)
    (hr1 : wv v r m = 1) (hT : T < 256) (hsw : sw < 256 ^ ns)
    (hp : ∀ q < np, v (CFSG.KJ4.lInv inv (CFSG.KJ4.wLet pw q)) = (v (CFSG.KJ4.wLet pw q))⁻¹)
    (h : CFSG.KJ4.chkPsiRel inv T sw ns pw np r m = true) :
    v T * wv v sw ns * v T = wv v pw np := by
  unfold CFSG.KJ4.chkPsiRel at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  have hm : ns + np + 2 = m := Nat.eq_of_beq_eq_true h1
  change CFSG.KJ4.isRot r m (CFSG.KJ4.wCat (CFSG.KJ4.wCat (CFSG.KJ4.wCat T 1 sw) (ns + 1) T)
    (ns + 2) (CFSG.KJ4.wInv inv pw np)) = true at h2
  have hT1 : T < 256 ^ 1 := by simpa using hT
  have a1 := wCat_lt' hT1 hsw (by omega : 1 + ns = ns + 1)
  have a2 := wCat_lt' a1 hT1 (by omega : ns + 1 + 1 = ns + 2)
  have hW := isRot_val v hr hr1 h2
  rw [wv_wCat' v a2 (wInv_lt inv pw np) (by omega : ns + 2 + np = m),
    wv_wCat' v a1 hT1 (by omega : ns + 1 + 1 = ns + 2), wv_wCat' v hT1 hsw (by omega : 1 + ns = ns + 1),
    wv_one v hT, wv_wInv v inv pw np hp] at hW
  exact mul_inv_eq_one.1 hW

@[expose] noncomputable def jv (x y t z : G) (c : ℕ) : G :=
  if c = 0 then x else if c = 1 then x⁻¹ else if c = 2 then y else if c = 3 then y⁻¹ else
  if c = 4 then t else if c = 5 then z else if c = 6 then z⁻¹ else x⁻¹

@[expose] def invJ : ℕ := 0x5060402030001

theorem lInv_invJ_lt (c : ℕ) : CFSG.KJ4.lInv invJ c < 7 := by
  rw [lInv_eq, DceWord.lInv_eq, byteG_eq, byte_eq']
  rcases Nat.lt_or_ge c 7 with hc | hc
  · interval_cases c <;> simp [invJ]
  · have : invJ / 256 ^ c = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le (by simp [invJ])
      (Nat.pow_le_pow_right (by norm_num) hc))
    simp [this]

theorem jv_inv (x y t z : G) (ht : t * t = 1) (c : ℕ) :
    CFSG.KJ4.lInv invJ c < 255 ∧ jv x y t z (CFSG.KJ4.lInv invJ c) = (jv x y t z c)⁻¹ := by
  refine ⟨lt_trans (lInv_invJ_lt c) (by norm_num), ?_⟩
  have hb : CFSG.KJ4.lInv invJ c = invJ / 256 ^ c % 256 := by
    rw [lInv_eq, DceWord.lInv_eq, byteG_eq, byte_eq']
  rw [hb]
  rcases Nat.lt_or_ge c 7 with hc | hc
  · have ht' : t = t⁻¹ := (inv_eq_of_mul_eq_one_right ht).symm
    interval_cases c <;> simp [invJ, jv]
    exact ht'
  · have : invJ / 256 ^ c = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le (by simp [invJ])
      (Nat.pow_le_pow_right (by norm_num) hc))
    rw [this]
    have h0 : c ≠ 0 := by omega
    have h1 : c ≠ 1 := by omega
    have h2 : c ≠ 2 := by omega
    have h3 : c ≠ 3 := by omega
    have h4 : c ≠ 4 := by omega
    have h5 : c ≠ 5 := by omega
    have h6 : c ≠ 6 := by omega
    simp [jv, h0, h1, h2, h3, h4, h5, h6]

end CFSG.Certificates.J4Words

end
