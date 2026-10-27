module

public import CFSG.Certificates.Kernel.GGToral.PkBridge
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertWeyl

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.StepTwoToralCert

@[expose] noncomputable def vecZ (p n v : ℕ) : Fin n → ZMod p := fun j => ((lane v j : ℕ) : ZMod p)

@[simp] theorem andB_eq_true (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

@[simp] theorem orB_eq_true (a b : Bool) : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

@[simp] theorem notB_eq_true (a : Bool) : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem allN_eq_true {m : ℕ} {f : ℕ → Bool} : allN m f = true ↔ ∀ r < m, f r = true := by
  induction m with
  | zero => simp [allN]
  | succ m ih =>
    change andB (f m) (allN m f) = true ↔ _
    rw [andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · exact h2 r hr
      · exact h1
    · intro h
      exact ⟨h m (by omega), fun r hr => h r (by omega)⟩

theorem tagHdOK_basic {τ : Tag} {p mode : ℕ} {H : Hd} (h : tagHdOK τ p mode H = true) :
    tgOK τ = true ∧ H.mode = mode ∧ H.n = τ.rank ∧ H.p = p ∧ 3 ≤ p ∧ p < 16 ∧ H.np = tgNp τ ∧
      H.k0 = tgK0 τ ∧ H.threv = packRevL (pkTheta τ) := by
  simp only [tagHdOK, andB_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h
  exact ⟨h1, Nat.eq_of_beq_eq_true h2, (Nat.eq_of_beq_eq_true h3).trans (tgRank_eq τ),
    Nat.eq_of_beq_eq_true h4, Nat.le_of_ble_eq_true h5, Nat.le_of_ble_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h9, Nat.eq_of_beq_eq_true h8⟩

theorem tagHdOK_atil {τ : Tag} {p mode : ℕ} {H : Hd} (h : tagHdOK τ p mode H = true) :
    ∀ l < H.n, row H.atil l = packN H.n (atilC τ H l) := by
  simp only [tagHdOK, andB_eq_true] at h
  intro l hl
  exact Nat.eq_of_beq_eq_true (allN_eq_true.mp h.2.2.2.2.2.2.2.2.2.1 l hl)

theorem packN_add_mul (n c : ℕ) (f g : ℕ → ℕ) :
    packN n f + c * packN n g = packN n (fun j => f j + c * g j) := by
  rw [packN_eq_sum, packN_eq_sum, packN_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem lane_lt (v j : ℕ) : lane v j < 65536 := Nat.mod_lt _ (by norm_num)

theorem red_spec {H : Hd} {v : ℕ} (hp : 0 < H.p) (h : red H v = true) :
    v < 2 ^ (16 * H.n) ∧ ∀ j < H.n, lane v j < H.p := by
  have h1 : modL H.p H.n v = v := Nat.eq_of_beq_eq_true h
  have hl : ∀ j, lane v j % H.p < 65536 := fun j => lt_of_le_of_lt (Nat.mod_le _ _) (lane_lt v j)
  constructor
  · rw [← h1, modL_eq_packN]
    exact packN_lt fun j _ => hl j
  · intro j hj
    rw [← h1, modL_eq_packN, lane_packN (fun k _ => hl k) hj]
    exact Nat.mod_lt _ hp

theorem red_modL {H : Hd} (hp : 0 < H.p) (hp16 : H.p ≤ 65536) (x : ℕ) :
    red H (modL H.p H.n x) = true := by
  refine Nat.beq_eq_true_eq _ _ ▸ ?_
  rw [modL_eq_packN, modL_eq_packN]
  exact packN_congr fun j hj => by rw [lane_packN (fun k _ => lt_of_lt_of_le (Nat.mod_lt _ hp)
    hp16) hj, Nat.mod_mod]

theorem vecZ_modL_packN {p n : ℕ} {g : ℕ → ℕ} (hg : ∀ j < n, g j < 65536) (j : Fin n) :
    vecZ p n (modL p n (packN n g)) j = ((g j : ℕ) : ZMod p) := by
  have hm : ∀ k, lane (packN n g) k % p < 65536 ∨ n ≤ k := fun k => by
    by_cases hk : k < n
    · rw [lane_packN hg hk]
      exact Or.inl (lt_of_le_of_lt (Nat.mod_le _ _) (hg k hk))
    · exact Or.inr (by omega)
  simp only [vecZ, modL_eq_packN]
  rw [lane_packN (fun k hk => (hm k).resolve_right (by omega)) j.2, lane_packN hg j.2,
    ZMod.natCast_mod]

theorem simple_eq (H : Hd) (l f : ℕ) :
    simple H l f = modL H.p H.n (f + lane f l * row H.atil l) := rfl

theorem vecZ_simple {τ : Tag} {p mode : ℕ} {H : Hd} (h : tagHdOK τ p mode H = true) {l : ℕ}
    (hl : l < τ.rank) {f : ℕ} (hf : red H f = true) :
    vecZ p τ.rank (CFSG.KC.GGToral.simple H l f) =
      cowAct (CFSG.LieType.Chevalley.simple τ ⟨l, hl⟩) (vecZ p τ.rank f) := by
  obtain ⟨hτ, -, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  obtain ⟨hflt, hflane⟩ := red_spec hpos hf
  have hatil := tagHdOK_atil h l (by omega)
  have hle : ∀ k, atilC τ H l k < 16 := fun k => by
    unfold atilC
    cases Nat.beq k l
    · exact lt_of_lt_of_le (Nat.mod_lt _ hpos) (by omega)
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
  have hfl : lane f l < 16 := lt_of_lt_of_le (hflane l (by omega)) (by omega)
  have hsum : f + lane f l * row H.atil l =
      packN H.n (fun k => lane f k + lane f l * atilC τ H l k) := by
    rw [hatil]
    nth_rewrite 1 [eq_packN_lane hflt]
    exact packN_add_mul _ _ _ _
  have hg : ∀ k < H.n, lane f k + lane f l * atilC τ H l k < 65536 := fun k hk => by
    have h1 := hflane k hk
    have h2 := hle k
    nlinarith
  funext j
  rw [simple_eq, hsum]
  revert hg
  rw [hn, hpp]
  intro hg
  rw [vecZ_modL_packN hg j, cowAct_simple]
  have hA : ((atilC τ H l j : ℕ) : ZMod p) = -((τ.cartan ⟨l, hl⟩ j : ℤ) : ZMod p) := by
    unfold atilC
    by_cases hjl : (j : ℕ) = l
    · have hb : Nat.beq (j : ℕ) l = true := Nat.beq_eq_true_eq _ _ ▸ hjl
      have hj : j = ⟨l, hl⟩ := Fin.ext hjl
      rw [hb, hj, cartan_self hτ, hpp]
      change (((p - 2 : ℕ) : ℕ) : ZMod p) = _
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]
      push_cast
      ring
    · have hb : Nat.beq (j : ℕ) l = false :=
        Bool.eq_false_iff.mpr fun h => hjl (Nat.eq_of_beq_eq_true h)
      have hne : (⟨l, hl⟩ : Fin τ.rank) ≠ j := fun h => hjl (by rw [← h])
      rw [hb, tgCneg_lane hτ ⟨l, hl⟩ j hne]
      change (((lane (row (tgCneg τ) l) j % H.p : ℕ)) : ZMod p) = _
      rw [hpp, ZMod.natCast_mod]
      push_cast
      ring
  simp only [vecZ, Nat.cast_add, Nat.cast_mul]
  rw [hA]
  ring

@[expose] noncomputable def thN (τ : Tag) (i : ℕ) : ℕ := (pkTheta τ).getD i 0

theorem packRevL_pkTheta {τ : Tag} (hτ : tgOK τ = true) :
    packRevL (pkTheta τ) = packN τ.rank (fun k => thN τ (τ.rank - 1 - k)) := by
  cases τ <;> simp [tgOK] at hτ <;> decide +kernel

theorem thN_le {τ : Tag} (hτ : tgOK τ = true) : ∀ i < τ.rank, thN τ i ≤ 6 := by
  cases τ <;> simp [tgOK] at hτ <;> decide

theorem shiftLeft_eq_packN {n k : ℕ} (hk : k < n) (x : ℕ) :
    x <<< (16 * k) = packN n (fun j => if j = k then x else 0) := by
  rw [packN_eq_sum, Nat.shiftLeft_eq]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (Finset.range n) k, if_pos (Finset.mem_range.mpr hk), mul_comm]

theorem packN_add (n : ℕ) (f g : ℕ → ℕ) : packN n f + packN n g = packN n (fun j => f j + g j) := by
  have := packN_add_mul n 1 f g
  simp only [one_mul] at this
  exact this

section Theta


theorem thN_spec {τ : Tag} (hτ : tgOK τ = true) (i : Fin τ.rank) :
    ((thN τ i : ℕ) : ℤ) = (kacOf τ).θ i := by
  cases τ <;> simp [tgOK] at hτ <;> fin_cases i <;> rfl

theorem vecZ_thetaL {τ : Tag} {p mode : ℕ} {H : Hd} (h : tagHdOK τ p mode H = true) {f : ℕ}
    (hf : red H f = true) :
    vecZ p τ.rank (thetaL H f) = cowAct (rootReflection (kacOf τ).θ) (vecZ p τ.rank f) := by
  obtain ⟨hτ, -, hn, hpp, hp3, hp16, -, hk0, hth⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  obtain ⟨hflt, hflane⟩ := red_spec hpos hf
  have hk0n : tgK0 τ < τ.rank := tgK0_lt hτ
  have hflt' : f < 2 ^ (16 * τ.rank) := hn ▸ hflt
  set d := dotR H H.threv f with hd_def
  have hd : d = ∑ l ∈ Finset.range τ.rank, thN τ l * lane f l := by
    rw [hd_def, dotR, hth, packRevL_pkTheta hτ, hn]
    nth_rewrite 1 [eq_packN_lane hflt']
    exact lane_mul_rev (F := 6) (G := 15) (by have := hn ▸ tgK0_lt hτ; omega) (thN_le hτ)
      (fun j hj => by have := hflane j (by omega); omega)
      (by have : τ.rank ≤ 8 := by cases τ <;> decide
          omega)
  have hsum : f + (H.p - d % H.p) <<< (16 * H.k0) =
      packN τ.rank (fun j => lane f j + if j = tgK0 τ then H.p - d % H.p else 0) := by
    rw [hk0, shiftLeft_eq_packN hk0n]
    nth_rewrite 1 [eq_packN_lane hflt']
    exact packN_add _ _ _
  have hg : ∀ k < τ.rank, lane f k + (if k = tgK0 τ then H.p - d % H.p else 0) < 65536 :=
    fun k hk => by
      have h1 := hflane k (by omega)
      split_ifs <;> omega
  funext j
  change vecZ p τ.rank (modL H.p H.n (f + (H.p - d % H.p) <<< (16 * H.k0))) j = _
  rw [hsum, hn, hpp]
  rw [hpp] at hg
  rw [vecZ_modL_packN hg j, cowAct_rootReflection_θ, tgK0_spec hτ]
  have hlat : latChar p (vecZ p τ.rank f) (kacOf τ).θ = ((d : ℕ) : ZMod p) := by
    rw [hd, latChar]
    push_cast
    rw [Finset.sum_range (fun l => ((thN τ l : ℕ) : ZMod p) * ((lane f l : ℕ) : ZMod p))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← thN_spec hτ i, Int.cast_natCast]
    rfl
  rw [hlat]
  simp only [vecZ]
  split_ifs with hj
  · push_cast
    rw [Nat.cast_sub (Nat.mod_lt _ (by omega)).le, ZMod.natCast_self, ZMod.natCast_mod]
    ring
  · push_cast
    ring

theorem red_simple {H : Hd} (hp : 0 < H.p) (hp16 : H.p ≤ 65536) (l f : ℕ) :
    red H (CFSG.KC.GGToral.simple H l f) = true := red_modL hp hp16 _

theorem red_thetaL {H : Hd} (hp : 0 < H.p) (hp16 : H.p ≤ 65536) (f : ℕ) :
    red H (thetaL H f) = true := red_modL hp hp16 _

theorem vecZ_letter_split {τ : Tag} {p : ℕ} {H : Hd} (h : tagHdOK τ p 0 H = true) {f : ℕ}
    (hf : red H f = true) (l : ℕ) :
    vecZ p τ.rank (letter H l f) = cowAct (tcLetterElt τ l) (vecZ p τ.rank f) ∧
      red H (letter H l f) = true := by
  obtain ⟨hτ, hm, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have htw : tw H = false := by
    rw [tw, hm]
    rfl
  have hpos : 0 < H.p := by omega
  have hp16' : H.p ≤ 65536 := by omega
  unfold letter
  rw [htw]
  by_cases hl : l < τ.rank
  · have hb : Nat.blt l H.n = true := by
      rw [Nat.blt_eq, hn]
      exact hl
    simp only [hb]
    rw [tcLetterElt, dif_pos hl]
    exact ⟨vecZ_simple h hl hf, red_simple hpos hp16' l f⟩
  · have hb : Nat.blt l H.n = false := by
      rw [Bool.eq_false_iff]
      intro h1
      rw [Nat.blt_eq, hn] at h1
      exact hl h1
    simp only [hb]
    rw [tcLetterElt, dif_neg hl]
    exact ⟨vecZ_thetaL h hf, red_thetaL hpos hp16' f⟩

theorem vecZ_word_split {τ : Tag} {p : ℕ} {H : Hd} (h : tagHdOK τ p 0 H = true) (w : List ℕ) :
    ∀ {f : ℕ}, red H f = true →
      vecZ p τ.rank (word H w f) = cowAct (tcWordElt τ w) (vecZ p τ.rank f) ∧
        red H (word H w f) = true := by
  induction w with
  | nil => exact fun hf => ⟨(cowAct_one _).symm, hf⟩
  | cons l w ih =>
    intro f hf
    obtain ⟨h1, h2⟩ := vecZ_letter_split h hf l
    obtain ⟨h3, h4⟩ := ih h2
    refine ⟨?_, h4⟩
    change vecZ p τ.rank (word H w (letter H l f)) = _
    rw [h3, h1, tcWordElt, cowAct_mul]

@[expose] noncomputable def twElt (g : ℕ) : WeylGroup Tag.E6 :=
  tcWordElt Tag.E6 ((tcTwistGens ()).getD (min g 3) [])

theorem commutesPi_twElt (g : ℕ) : CommutesPi e6Gamma (twElt g) := commutesPi_twistGen _

theorem vecZ_letter_twist {p : ℕ} {H : Hd} (h : tagHdOK .E6 p 1 H = true) {f : ℕ}
    (hf : red H f = true) (g : ℕ) :
    vecZ p Tag.E6.rank (letter H g f) = cowAct (twElt g) (vecZ p Tag.E6.rank f) ∧
      red H (letter H g f) = true := by
  obtain ⟨hτ, hm, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have htw : tw H = true := by
    rw [tw, hm]
    rfl
  have hpos : 0 < H.p := by omega
  have hp16' : H.p ≤ 65536 := by omega
  have hs : ∀ (l : ℕ) (hl : l < Tag.E6.rank) {x : ℕ}, red H x = true →
      vecZ p Tag.E6.rank (CFSG.KC.GGToral.simple H l x) =
        cowAct (tcLetterElt Tag.E6 l) (vecZ p Tag.E6.rank x) := fun l hl x hx => by
    rw [tcLetterElt, dif_pos hl]
    exact vecZ_simple h hl hx
  unfold letter
  rw [htw]
  simp only
  unfold twLetter twElt
  rcases g with _ | _ | _ | g
  · refine ⟨?_, red_simple hpos hp16' _ _⟩
    change _ = cowAct (1 * tcLetterElt Tag.E6 1) _
    rw [one_mul]
    exact hs 1 (by decide) hf
  · refine ⟨?_, red_simple hpos hp16' _ _⟩
    change _ = cowAct (1 * tcLetterElt Tag.E6 3) _
    rw [one_mul]
    exact hs 3 (by decide) hf
  · refine ⟨?_, red_simple hpos hp16' _ _⟩
    change _ = cowAct (1 * tcLetterElt Tag.E6 4 * tcLetterElt Tag.E6 2) _
    rw [one_mul, cowAct_mul, ← hs 2 (by decide) hf]
    exact hs 4 (by decide) (red_simple hpos hp16' _ _)
  · have hb0 : Nat.beq (g + 3) 0 = false := rfl
    have hb1 : Nat.beq (g + 3) 1 = false := rfl
    have hb2 : Nat.beq (g + 3) 2 = false := rfl
    have hmin : min (g + 3) 3 = 3 := by omega
    simp only [hb0, hb1, hb2, hmin]
    refine ⟨?_, red_simple hpos hp16' _ _⟩
    change _ = cowAct (1 * tcLetterElt Tag.E6 5 * tcLetterElt Tag.E6 0) _
    rw [one_mul, cowAct_mul, ← hs 0 (by decide) hf]
    exact hs 5 (by decide) (red_simple hpos hp16' _ _)

@[expose] noncomputable def twWordElt : List ℕ → WeylGroup Tag.E6
  | [] => 1
  | g :: w => twWordElt w * twElt g

theorem commutesPi_twWordElt (w : List ℕ) : CommutesPi e6Gamma (twWordElt w) := by
  induction w with
  | nil => exact commutesPi_one e6Gamma
  | cons g w ih => exact commutesPi_mul ih (commutesPi_twElt g)

theorem vecZ_word_twist {p : ℕ} {H : Hd} (h : tagHdOK .E6 p 1 H = true) (w : List ℕ) :
    ∀ {f : ℕ}, red H f = true →
      vecZ p Tag.E6.rank (word H w f) = cowAct (twWordElt w) (vecZ p Tag.E6.rank f) ∧
        red H (word H w f) = true := by
  induction w with
  | nil => exact fun hf => ⟨(cowAct_one _).symm, hf⟩
  | cons g w ih =>
    intro f hf
    obtain ⟨h1, h2⟩ := vecZ_letter_twist h hf g
    obtain ⟨h3, h4⟩ := ih h2
    refine ⟨?_, h4⟩
    change vecZ p Tag.E6.rank (word H w (letter H g f)) = _
    rw [h3, h1, twWordElt, cowAct_mul]

end Theta

end CFSG.KC.GGToral
