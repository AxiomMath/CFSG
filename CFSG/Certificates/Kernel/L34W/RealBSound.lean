
module

public import Certificates.Data.Kernel.L34W.RealB
public import CFSG.Certificates.Kernel.L34W.OutCovSound
public import CFSG.Certificates.Kernel.L34W.FixSound

public section

namespace CFSG.KC.L34W.RBS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.L34W CFSG.KC.L34W.OCS CFSG.KC.L34KSnd
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
open CFSG.KLie.CT (notB)

theorem fld_pmk' {n w : ℕ} {f : ℕ → ℕ} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w) :
    PF.Fld w (pmk n w f) (fun i => if i < n then f i else 0) := by
  have hc := PF.clog_spec hn
  have h := PF.fld_pmkT n w f hf (clog n) 0
  have e : pmk n w f = pmkT n w f (clog n) 0 := by
    unfold pmk
    rw [PF.strictN_eqP]
  rw [e]
  refine PF.fld_congr h fun i => ?_
  by_cases hi : i < n
  · have h2 : i < 2 ^ clog n := by omega
    simp [hi, h2]
  · simp [hi]

theorem pg_pmk' {n w i : ℕ} {f : ℕ → ℕ} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w)
    (hi : i < n) : pg w (mask w) (pmk n w f) i = f i := by
  rw [PF.pg_of_fld (fld_pmk' hn hf) (by simp only [hi, ↓reduceIte]; exact hf i hi)]
  simp [hi]

theorem allM_all {f : MElt → Bool} : allM.all f = true ↔ ∀ c < 1024, f (dec c) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h c hc
    exact h _ (mem_allM (dec_lt hc))
  · intro h x hx
    obtain ⟨c, hc, rfl⟩ := dec_surj (lt_of_mem_allM hx)
    exact h c hc

theorem bc_eq (j : ℕ) : bc j = 64 * (j / 16) + j % 16 := rfl

theorem bc_lt {j : ℕ} (hj : j < 64) : bc j < 1024 := by
  rw [bc_eq]
  omega

theorem zT0_iff {c : ℕ} (hc : c < 1024) : zT0.contains (c / 16) = true ↔ ∃ j < 64, bc j = c := by
  constructor
  · intro h
    have h' : c / 16 = 0 ∨ c / 16 = 4 ∨ c / 16 = 8 ∨ c / 16 = 12 := by simpa [zT0] using h
    refine ⟨16 * (c / 64) + c % 16, by omega, ?_⟩
    rw [bc_eq]
    omega
  · rintro ⟨j, hj, rfl⟩
    rw [bc_eq]
    have e : (64 * (j / 16) + j % 16) / 16 = 4 * (j / 16) := by omega
    rw [e]
    rcases (by omega : j / 16 = 0 ∨ j / 16 = 1 ∨ j / 16 = 2 ∨ j / 16 = 3) with h | h | h | h <;>
      rw [h] <;> decide

theorem betaK_lt {A : ℕ → ℕ} (b i x : ℕ) : betaK A b i x < 1024 := by
  rw [betaK_eq]
  have : pg 10 (mask 10) b (x / 16) < 1024 := pg_lt' 10 b _
  exact mk_lt (by omega)

theorem bIf_true {c x y : Bool} (hc : c = true) (h : bIf(c, x, y) = true) : x = true := by
  subst hc
  exact h

theorem outI_eq : ∀ i < 36, outI i = !repInS.contains i := by decide +kernel

variable {κ : ZMod 4 × ZMod 4} {m : ℕ} {T A : ℕ → ℕ}

theorem eqKM_eq (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val))
    (x y : MElt) : eqKM κ x y = eqKB (kbOfMask m) x y := by
  unfold eqKM eqKB inKB kIdx
  rw [hm, getD_mask m]
  have := ZMod.val_lt (x.2.1 - y.2.1)
  have := ZMod.val_lt (x.2.2 - y.2.2)
  omega

theorem eqKM_dec (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val))
    (x y : ℕ) : eqKM κ (dec x) (dec y) = eqC m x y := by
  rw [eqKM_eq hm, eqC_eq]

theorem isBhM_dec (hT : T1Of T) (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val))
    {c : ℕ} (hc : c < 1024) : isBhM κ (dec c) = (zT0.contains (c / 16) && eqC m (mulC T c c) 0) := by
  unfold isBhM
  rw [← dec_mulC hT hc hc, ← dec_zero, eqKM_dec hm]
  rfl

theorem bh_iff (hT : T1Of T) (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val))
    {BH : ℕ} (hB : ∀ j < 64, hasBit BH j = eqC m (mulC T (bc j) (bc j)) 0) {c : ℕ} (hc : c < 1024) :
    isBhM κ (dec c) = true ↔ ∃ j < 64, bc j = c ∧ hasBit BH j = true := by
  rw [isBhM_dec hT hm hc, Bool.and_eq_true, zT0_iff hc]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, h2⟩
    exact ⟨j, hj, rfl, by rw [hB j hj]; exact h2⟩
  · rintro ⟨j, hj, rfl, h2⟩
    exact ⟨⟨j, hj, rfl⟩, by rw [← hB j hj]; exact h2⟩

theorem eqKB_comm_ctr (kb : List Bool) (k : ℕ) (a b : ZMod 4) (y : MElt) :
    eqKB kb (mulM (k, a, b) y) (mulM y (k, a, b)) =
      eqKB kb (mulM (k, 0, 0) y) (mulM y (k, 0, 0)) := by
  obtain ⟨l, c, d⟩ := y
  rw [mulM_ctr k l a b c d, mulM_ctr l k c d a b, mulM_ctr k l 0 0 c d, mulM_ctr l k c d 0 0]
  simp only [eqKB]
  have e1 : ∀ p q : ZMod 4, p + (a + c) - (q + (c + a)) = p + (0 + c) - (q + (c + 0)) :=
    fun p q => by ring
  have e2 : ∀ p q : ZMod 4, p + (b + d) - (q + (d + b)) = p + (0 + d) - (q + (d + 0)) :=
    fun p q => by ring
  rw [e1, e2]

theorem dec_eq (v : ℕ) : dec v = (v / 16, ((v / 4 % 4 : ℕ) : ZMod 4), ((v % 4 : ℕ) : ZMod 4)) := rfl

theorem isAhM_dec (hT : T1Of T)
    (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val)) {BH AH : ℕ}
    (hB : ∀ j < 64, hasBit BH j = eqC m (mulC T (bc j) (bc j)) 0)
    (hAh : ∀ k < 64, hasBit AH k =
      allN 64 fun j => bIf(hasBit BH j, commC T m (16 * k) (bc j), true))
    {v : ℕ} (hv : v < 1024) : isAhM κ (dec v) = hasBit AH (v / 16) := by
  have hk : v / 16 < 64 := by omega
  have h16 : 16 * (v / 16) < 1024 := by omega
  rw [hAh _ hk, Bool.eq_iff_iff, isAhM, allM_all, allN_iff']
  constructor
  · intro h j hj
    rw [bIf_eq']
    split
    · next hbj =>
      have h1 := h (bc j) (bc_lt hj)
      rw [(bh_iff hT hm hB (bc_lt hj)).2 ⟨j, hj, rfl, hbj⟩, Bool.not_true, Bool.false_or,
        eqKM_eq hm, dec_eq v, eqKB_comm_ctr] at h1
      unfold commC
      rw [eqC_eq, dec_mulC hT h16 (bc_lt hj), dec_mulC hT (bc_lt hj) h16, dec_sixteen]
      exact h1
    · rfl
  · intro h c hc
    cases hbc : isBhM κ (dec c)
    · rfl
    · obtain ⟨j, hj, rfl, hbj⟩ := (bh_iff hT hm hB hc).1 hbc
      have h1 := bIf_true hbj (h j hj)
      unfold commC at h1
      rw [eqC_eq, dec_mulC hT h16 hc, dec_mulC hT hc h16, dec_sixteen] at h1
      rw [Bool.not_true, Bool.false_or, eqKM_eq hm, dec_eq v, eqKB_comm_ctr]
      exact h1

theorem invK_eq (hA : AlOf A) {i : ℕ} (hi : i < 36) (k₁ k₂ : ℕ) :
    invK A k₁ k₂ m i = m.testBit (4 * ((k₁ : ZMod 4) * ((alphaEntry i 64).2.1 : ZMod 4) +
      (k₂ : ZMod 4) * ((alphaEntry i 65).2.1 : ZMod 4)).val +
      ((k₁ : ZMod 4) * ((alphaEntry i 64).2.2.1 : ZMod 4) +
        (k₂ : ZMod 4) * ((alphaEntry i 65).2.2.1 : ZMod 4)).val) := by
  unfold invK
  rw [strictB_eq', strictB_eq', bitC_eq, hA i 64 hi (by norm_num), hA i 65 hi (by norm_num)]
  simp only [quad]
  rw [cast_val_add, cast_val_add]
  rfl

theorem liftsK_eq (hA : AlOf A)
    (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val)) {k₁ k₂ : ℕ}
    (hκ : κ = ((k₁ : ZMod 4), (k₂ : ZMod 4))) {i : ℕ} (hi : i < 36) :
    liftsK κ i = liftK A k₁ k₂ m i := by
  have key : ∀ n : ℕ, invK A (Nat.mul n k₁) (Nat.mul n k₂) m i =
      decide (inKC κ ((n : ZMod 4) * κ.1 * ((alphaEntry i 64).2.1 : ZMod 4) +
          (n : ZMod 4) * κ.2 * ((alphaEntry i 65).2.1 : ZMod 4))
        ((n : ZMod 4) * κ.1 * ((alphaEntry i 64).2.2.1 : ZMod 4) +
          (n : ZMod 4) * κ.2 * ((alphaEntry i 65).2.2.1 : ZMod 4))) := by
    intro n
    rw [hm]
    change invK A (n * k₁) (n * k₂) m i = _
    rw [invK_eq hA hi, hκ]
    push_cast
    rfl
  rw [Bool.eq_iff_iff, liftK, allN_iff', liftsK, List.all_eq_true]
  constructor
  · intro h n hn
    rw [key]
    have h1 := h (n : ZMod 4) (by interval_cases n <;> decide)
    exact h1
  · intro h x _
    have hx' : x = ((x.val : ℕ) : ZMod 4) := (ZMod.natCast_zmod_val x).symm
    have h1 := h x.val (ZMod.val_lt x)
    rw [key, ← hx'] at h1
    exact h1

theorem fixB_of (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val)) {BH : ℕ}
    (hB : ∀ j < 64, hasBit BH j = eqC m (mulC T (bc j) (bc j)) 0) {t i : ℕ} (ht : t < 64)
    (hi : i < 36) (h : fixBM κ t i = true) : fixB T A m BH (16 * t) (invC T (16 * t)) i = true := by
  unfold fixB
  rw [allN_iff']
  intro j hj
  rw [bIf_eq']
  split
  · next hbj =>
    have h1 := (allM_all.1 h) (bc j) (bc_lt hj)
    rw [(bh_iff hT hm hB (bc_lt hj)).2 ⟨j, hj, rfl, hbj⟩, Bool.not_true, Bool.false_or] at h1
    have e : betaW T A (16 * t) (invC T (16 * t)) i (bc j) = betaC T A t i (bc j) := rfl
    rw [e, ← eqKM_dec hm, dec_betaC hT hA hb ht hi (bc_lt hj)]
    exact h1
  · rfl

variable {G Y : ℕ → ℕ}

theorem pow4M_eq (hG : GensG G) (hy : yOK G Y = true) {t i : ℕ} (ht : t < 64) (hi : i < 36) :
    pow4M t i = pow4K (Y (64 * i + t)) := by
  obtain ⟨hr, hc⟩ := rT_eq hG hy ht hi
  have e : comp 42 (wordTab (tg t)) (repTab i) = unpack 42 6 (Y (64 * i + t)) := hr
  unfold pow4M pow4K
  dsimp only
  rw [e, comp_eq hc hc, comp_eq (cn_pc hc hc) (cn_pc hc hc), idTab42,
    beq_unpack (cn_pc (cn_pc hc hc) (cn_pc hc hc)) cn_pidn, strictB_eq']

theorem brow_pmk (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) {t i : ℕ} (ht : t < 64)
    (hi : i < 36) :
    BRow (pmk 64 10 fun k => betaW T A (16 * t) (invC T (16 * t)) i (Nat.mul 16 k)) t i := by
  intro k hk
  have hf : ∀ x < 64, betaW T A (16 * t) (invC T (16 * t)) i (Nat.mul 16 x) < 2 ^ 10 :=
    fun x hx => lt_of_lt_of_eq (betaC_lt hb ht hi (by change 16 * x < 1024; omega)) (by norm_num)
  rw [pg_pmk' (by norm_num) hf hk]
  change dec (betaC T A t i (16 * k)) = _
  rw [dec_betaC hT hA hb ht hi (by omega), dec_sixteen]

theorem tagOK_spec {AH b i w f : ℕ} (h : tagOK T A m AH b i w f = true) :
    (∃ v < 1024, eqC m (betaK A b i (betaK A b i v)) (mulC T (mulC T w v) (invC T w)) = false) ∨
    (∃ v < 1024, hasBit AH (v / 16) = true ∧ eqC m (uK T A b i w v) 0 = true) ∨
    (∃ v < 1024, hasBit AH (v / 16) = true ∧ mulC T (uK T A b i w v) (uK T A b i w v) / 16 = 0 ∧
      eqC m (mulC T (uK T A b i w v) (uK T A b i w v)) 0 = false) ∨
    (∀ v < 1024, hasBit AH (v / 16) = true → uK T A b i w v / 16 = 0 ∧
      eqC m (mulC T (uK T A b i w v) (uK T A b i w v)) 0 = true ∧ eqC m (uK T A b i w v) 0 = false) := by
  unfold tagOK at h
  simp only [strictB_eq'] at h
  have hv : f % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
  rcases bIf_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [bNot_eq, Bool.not_eq_true'] at h
    exact Or.inl ⟨_, hv, h⟩
  rcases bIf_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [bAnd_iff] at h
    exact Or.inr (Or.inl ⟨_, hv, h.1, h.2⟩)
  rcases bIf_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [bAnd_iff, bAnd_iff, bNot_eq, Bool.not_eq_true'] at h
    exact Or.inr (Or.inr (Or.inl ⟨_, hv, h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2⟩))
  rcases bIf_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
  · refine Or.inr (Or.inr (Or.inr fun v hv' hab => ?_))
    have h1 := bIf_true hab (allN_spec h v hv')
    rw [bAnd_iff, bAnd_iff, bNot_eq, Bool.not_eq_true'] at h1
    exact ⟨Nat.eq_of_beq_eq_true h1.1, h1.2.1, h1.2.2⟩
  · exact absurd h (by decide)

theorem c6_core (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val)) {BH AH : ℕ}
    (hB : ∀ j < 64, hasBit BH j = eqC m (mulC T (bc j) (bc j)) 0)
    (hAh : ∀ k < 64, hasBit AH k =
      allN 64 fun j => bIf(hasBit BH j, commC T m (16 * k) (bc j), true))
    {b t i R : ℕ} (hi : i < 36) (hbr : BRow b t i)
    (h : allN 1024 (fun w => bIf(fixC A b i m w, tagOK T A m AH b i w (pg 16 (mask 16) R w), true))
      = true) :
    (allM.all fun w => !eqKM κ (betaYM t i w) w ||
      !(allM.all fun x => eqKM κ (betaYM t i (betaYM t i x)) (mulM (mulM w x) (invM w))) ||
      trichM κ (allM.filter (isAhM κ)) t i w) = true := by
  rw [allM_all]
  intro w hw
  have hu : ∀ v < 1024, uK T A b i w v < 1024 ∧
      dec (uK T A b i w v) = mulM (mulM (dec v) (betaYM t i (dec v))) (dec w) := by
    intro v hv
    unfold uK
    refine ⟨mulC_lt hb (mulC_lt hb hv (betaK_lt _ _ _)) hw, ?_⟩
    rw [dec_mulC hT (mulC_lt hb hv (betaK_lt _ _ _)) hw, dec_mulC hT hv (betaK_lt _ _ _),
      dec_betaK hA hbr hi hv]
  have hAm : ∀ v < 1024, hasBit AH (v / 16) = true → dec v ∈ allM.filter (isAhM κ) := by
    intro v hv hab
    rw [List.mem_filter, isAhM_dec hT hm hB hAh hv]
    exact ⟨dec_mem_allM hv, hab⟩
  cases hfix : eqKM κ (betaYM t i (dec w)) (dec w)
  · rfl
  have hfc : fixC A b i m w = true := by
    rw [fixC_eq hA hbr hi m hw]
    unfold fixKB
    rw [← eqKM_eq hm]
    exact hfix
  have h1 := bIf_true hfc (allN_spec h w hw)
  rw [Bool.not_true, Bool.false_or]
  rcases tagOK_spec h1 with ⟨v, hv, hne⟩ | ⟨v, hv, hab, h0⟩ | ⟨v, hv, hab, h2, h3⟩ | hall
  · have e : (allM.all fun x => eqKM κ (betaYM t i (betaYM t i x))
        (mulM (mulM (dec w) x) (invM (dec w)))) = false := by
      rw [← Bool.not_eq_true, allM_all]
      intro hh
      have h4 := hh v hv
      rw [← dec_betaK hA hbr hi hv, ← dec_betaK hA hbr hi (betaK_lt _ _ _), ← dec_invC hT hw,
        ← dec_mulC hT hw hv, ← dec_mulC hT (mulC_lt hb hw hv) invC_lt, eqKM_dec hm, hne] at h4
      exact absurd h4 (by decide)
    rw [e]
    rfl
  · have ht : trichM κ (allM.filter (isAhM κ)) t i (dec w) = true := by
      unfold trichM
      simp only [Bool.or_eq_true, List.any_eq_true]
      refine Or.inl (Or.inl ⟨dec v, hAm v hv hab, ?_⟩)
      rw [← (hu v hv).2, ← dec_zero, eqKM_dec hm]
      exact h0
    rw [ht, Bool.or_true]
  · have ht : trichM κ (allM.filter (isAhM κ)) t i (dec w) = true := by
      unfold trichM
      simp only [Bool.or_eq_true, List.any_eq_true]
      refine Or.inl (Or.inr ⟨dec v, hAm v hv hab, ?_⟩)
      have hl := (hu v hv).1
      rw [← (hu v hv).2, ← dec_mulC hT hl hl, ← dec_zero, eqKM_dec hm, h3, Bool.not_false,
        Bool.and_true, beq_iff_eq]
      exact h2
    rw [ht, Bool.or_true]
  · have ht : trichM κ (allM.filter (isAhM κ)) t i (dec w) = true := by
      unfold trichM
      simp only [Bool.or_eq_true, List.all_eq_true]
      refine Or.inr fun x hx => ?_
      obtain ⟨hxm, hxa⟩ := List.mem_filter.1 hx
      obtain ⟨c, hc, rfl⟩ := dec_surj (lt_of_mem_allM hxm)
      rw [isAhM_dec hT hm hB hAh hc] at hxa
      obtain ⟨e1, e2, e3⟩ := hall c hc hxa
      have hl := (hu c hc).1
      rw [← (hu c hc).2, ← dec_mulC hT hl hl, ← dec_zero, eqKM_dec hm, eqKM_dec hm, e2, e3,
        Bool.not_false, Bool.and_true, Bool.and_true, beq_iff_eq]
      exact e1
    rw [ht, Bool.or_true]

theorem cK_sound (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) (hG : GensG G)
    (hy : yOK G Y = true) {H W : ℕ → ℕ} {hc k₁ k₂ : ℕ} (hκ : κ = ((k₁ : ZMod 4), (k₂ : ZMod 4)))
    (hm : ∀ a b : ZMod 4, decide (inKC κ a b) = m.testBit (4 * a.val + b.val))
    (h : cK T A Y H W hc k₁ k₂ m = true) :
    ((List.range 36).all fun i => !liftsK κ i ||
      (List.range 64).all fun t => !fixBM κ t i || pow4M t i) = true ∧
    ((List.range 36).all fun i => repInS.contains i || !liftsK κ i ||
      (List.range 64).all fun t => !fixBM κ t i || allM.all fun w =>
        !eqKM κ (betaYM t i w) w ||
          !(allM.all fun x => eqKM κ (betaYM t i (betaYM t i x)) (mulM (mulM w x) (invM w))) ||
          trichM κ (allM.filter (isAhM κ)) t i w) = true := by
  unfold cK at h
  simp only [strictB_eq'] at h
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  generalize pg 64 (mask 64) (H hc) 0 = BH at h1 h2 h3
  generalize pg 64 (mask 64) (H hc) 1 = AH at h1 h2 h3
  have hB : ∀ j < 64, hasBit BH j = eqC m (mulC T (bc j) (bc j)) 0 :=
    fun j hj => bEq_iff.1 (allN_spec h1 j hj)
  have hAh : ∀ k < 64, hasBit AH k =
      allN 64 fun j => bIf(hasBit BH j, commC T m (16 * k) (bc j), true) :=
    fun k hk => bEq_iff.1 (allN_spec h2 k hk)
  have main : ∀ i < 36, liftsK κ i = true → ∀ t < 64, fixBM κ t i = true →
      pow4M t i = true ∧ (repInS.contains i = false →
        c6T T A m AH (16 * t) (invC T (16 * t)) i (W (64 * (36 * hc + i) + t)) = true) := by
    intro i hi hl t ht hf
    rw [liftsK_eq hA hm hκ hi] at hl
    have h4 := bIf_true hl (allN_spec h3 i hi)
    have h5 := bIf_true (fixB_of hT hA hb hm hB ht hi hf) (allN_spec h4 t ht)
    rw [bAnd_iff] at h5
    obtain ⟨h6, h7⟩ := h5
    refine ⟨by rw [pow4M_eq hG hy ht hi]; exact h6, fun hS => ?_⟩
    have ho : outI i = true := by rw [outI_eq i hi, hS]; rfl
    exact bIf_true ho h7
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro i hi'
    have hi := List.mem_range.1 hi'
    cases hl : liftsK κ i
    · rfl
    rw [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro t ht'
    have ht := List.mem_range.1 ht'
    cases hf : fixBM κ t i
    · rfl
    rw [Bool.not_true, Bool.false_or]
    exact (main i hi hl t ht hf).1
  · rw [List.all_eq_true]
    intro i hi'
    have hi := List.mem_range.1 hi'
    cases hS : repInS.contains i
    · cases hl : liftsK κ i
      · rfl
      rw [Bool.not_true, Bool.false_or, Bool.false_or, List.all_eq_true]
      intro t ht'
      have ht := List.mem_range.1 ht'
      cases hf : fixBM κ t i
      · rfl
      rw [Bool.not_true, Bool.false_or]
      have h6 := (main i hi hl t ht hf).2 hS
      unfold c6T at h6
      rw [strictB_eq'] at h6
      exact c6_core hT hA hb hm hB hAh hi (brow_pmk hT hA hb ht hi) h6
    · rfl

end CFSG.KC.L34W.RBS

end
