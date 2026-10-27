
module

public import Certificates.Data.Kernel.L34W.OutCov
public import Certificates.Data.GrSLitL34Sec4OutCovCheck
public import CFSG.Certificates.Kernel.L34W.ModKSound
public import CFSG.Certificates.Kernel.L34W.OuterSound
public import CFSG.Certificates.Kernel.L34Scan2Sound
public import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34W.OCS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.L34W CFSG.KC.L34KSnd CFSG.KS.PEnum CFSG.KC.L34K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.GrS4.OutCov
open CFSG.ComponentClassification.GrSLit.GrS4 CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
open CFSG.KLie.CT (notB)

theorem orK_eq (a b : Bool) : orK a b = (a || b) := by cases a <;> rfl

theorem bIf_eq' (c t e : Bool) : bIf(c, t, e) = (if c = true then t else e) := by cases c <;> rfl

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem notB_eq' (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

theorem allN_iff' {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  CFSG.KS.Raw.Orb.allN_iff

theorem memL_iff {N x : ℕ} {T : ℕ → ℕ} : CFSG.KC.L34Scan2.memL N T x = true ↔ ∃ q < N, T q = x := by
  refine ⟨CFSG.KC.L34Scan2.memL_spec, fun ⟨q, hq, e⟩ => ?_⟩
  unfold CFSG.KC.L34Scan2.memL
  rw [notB_eq', Bool.not_eq_true']
  cases h : allN N fun q => CFSG.KLie.CT.notB (Nat.beq (T q) x)
  · rfl
  · have := allN_iff'.1 h q hq
    rw [notB_eq', e, Nat.beq_refl] at this
    exact absurd this (by decide)

theorem allBelow_iff' {m : ℕ} {f : ℕ → Bool} : allBelow m f = true ↔ ∀ i < m, f i = true := by
  unfold allBelow
  rw [List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.2 hi), fun h x hx => h x (List.mem_range.1 hx)⟩

theorem pg_lt' (w p j : ℕ) : pg w (mask w) p j < 2 ^ w := by
  rw [CFSG.KS.Raw.Orb.pg_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem invIdx_eq (t : ℕ) :
    CFSG.ComponentClassification.GrSLit.GrS4.OutCov.invIdx t =
      CFSG.ComponentClassification.GrSLit.L34Facts.Real.invIdx t := rfl

theorem invE_eq (t : ℕ) : invE t = invM (t, 0, 0) := by
  unfold invE invM
  rw [invIdx_eq, sub_zero, sub_zero]

theorem betaE_eq (t i : ℕ) (x : El) : betaE t i x = betaYM t i x := by
  unfold betaE betaYM
  rw [invE_eq]
  rfl

theorem mulE_eq (x y : El) : mulE x y = mulM x y := rfl

variable {κ : ZMod 4 × ZMod 4} {m : ℕ}

theorem eqE_eq (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) (x y : El) :
    eqE κ x y = eqKB (kbOfMask m) x y := by
  unfold eqE eqKB inKB kIdx
  rw [hm, getD_mask m]
  have := ZMod.val_lt (x.2.1 - y.2.1)
  have := ZMod.val_lt (x.2.2 - y.2.2)
  omega

theorem eqE_dec (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) (x y : ℕ) :
    eqE κ (dec x) (dec y) = eqC m x y := by
  rw [eqE_eq hm, eqC_eq]

variable {T A : ℕ → ℕ}

theorem mulE_dec (hT : T1Of T) {x y : ℕ} (hx : x < 1024) (hy : y < 1024) :
    mulE (dec x) (dec y) = dec (mulC T x y) := by
  rw [mulE_eq, dec_mulC hT hx hy]

theorem betaE_dec (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) {t i x : ℕ}
    (ht : t < 64) (hi : i < 36) (hx : x < 1024) : betaE t i (dec x) = dec (betaC T A t i x) := by
  rw [betaE_eq, dec_betaC hT hA hb ht hi hx]

theorem oneE_eq : oneE = dec 0 := by
  rw [dec_zero]
  rfl

theorem mem_z4 : ∀ a : ZMod 4, a ∈ OutCov.z4 := by decide

theorem mem_els {x : El} : x ∈ els ↔ x.1 < 64 := by
  obtain ⟨k, a, b⟩ := x
  unfold els
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk, a', -, b', -, rfl, -, -⟩
    exact hk
  · intro hk
    exact ⟨k, hk, a, mem_z4 a, b, mem_z4 b, rfl, rfl, rfl⟩

theorem dec_surj {x : El} (hx : x.1 < 64) : ∃ c < 1024, dec c = x := by
  obtain ⟨k, a, b⟩ := x
  refine ⟨mk k a.val b.val, mk_lt hx, ?_⟩
  rw [dec_mk, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem els_all {f : El → Bool} : els.all f = true ↔ ∀ c < 1024, f (dec c) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h c hc
    exact h _ (mem_els.2 (dec_lt hc))
  · intro h x hx
    obtain ⟨c, hc, rfl⟩ := dec_surj (mem_els.1 hx)
    exact h c hc

theorem els_any {f : El → Bool} : els.any f = true ↔ ∃ c < 1024, f (dec c) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨c, hc, rfl⟩ := dec_surj (mem_els.1 hx)
    exact ⟨c, hc, h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨_, mem_els.2 (dec_lt hc), h⟩

theorem rT_eq_yTab (t j : ℕ) : rT t j = yTab t j := rfl

variable {G Y : ℕ → ℕ}

theorem rT_eq (hG : GensG G) (hy : yOK G Y = true) {t j : ℕ} (ht : t < 64) (hj : j < 36) :
    rT t j = unpack 42 6 (Y (64 * j + t)) ∧ Cn (Y (64 * j + t)) := by
  obtain ⟨hc, e⟩ := yK_eq hG t hj
  rw [rT_eq_yTab, e, Y_eq hy ht hj]
  exact ⟨rfl, hc⟩

theorem commB_eq {x g : ℕ} (hx : Cn x) (hg : Cn g) :
    commB (unpack 42 6 x) (unpack 42 6 g) = commPt 42 6 x g := by
  unfold commB
  rw [Bool.eq_iff_iff, beq_iff_eq, commPt_iff hx hg]

theorem sq_eq {x : ℕ} (hx : Cn x) :
    (comp 42 (unpack 42 6 x) (unpack 42 6 x) == idTab 42) = invPt 42 6 x := by
  rw [Bool.eq_iff_iff, beq_iff_eq, invPt_iff hx]

theorem is2_eq {x : ℕ} (hx : Cn x) : is2 (unpack 42 6 x) = is2K x := by
  unfold is2 is2K
  rw [CFSG.KC.L34Scan.powTwoTab_unpack hx 8, idTab42,
    beq_unpack (CFSG.KC.L34Scan.pow2K_canon hx 8) cn_pidn]

theorem comp_eq {x g : ℕ} (hx : Cn x) (hg : Cn g) :
    comp 42 (unpack 42 6 x) (unpack 42 6 g) = unpack 42 6 (pc x g) :=
  comp_unpack' hx hg

theorem cn_pc {x g : ℕ} (hx : Cn x) (hg : Cn g) : Cn (pc x g) := CFSG.KC.BfsPin.canonK_pcomp hx hg

theorem cast_val_add (k₁ k₂ u v : ℕ) :
    ((k₁ : ZMod 4) * (u : ZMod 4) + (k₂ : ZMod 4) * (v : ZMod 4)).val = (k₁ * u + k₂ * v) % 4 := by
  rw [← ZMod.val_natCast]
  push_cast
  rfl

theorem invar_eq (hA : AlOf A) {k₁ k₂ i : ℕ} (hi : i < 36) (hκ : κ = ((k₁ : ZMod 4), (k₂ : ZMod 4)))
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) : invar κ i = invK A k₁ k₂ m i := by
  unfold invar invK
  rw [strictB_eq', strictB_eq', bitC_eq, hm, hA i 64 hi (by norm_num), hA i 65 hi (by norm_num), hκ]
  simp only [quad]
  rw [cast_val_add, cast_val_add]
  rfl

theorem dec_sixteen_add {k ab : ℕ} (hab : ab < 16) :
    dec (16 * k + ab) = (k, ((ab / 4 : ℕ) : ZMod 4), ((ab % 4 : ℕ) : ZMod 4)) := by
  have e1 : (16 * k + ab) / 16 = k := by omega
  have e2 : (16 * k + ab) / 4 % 4 = ab / 4 := by omega
  have e3 : (16 * k + ab) % 4 = ab % 4 := by omega
  rw [dec, e1, e2, e3]

theorem z4_any {f : ZMod 4 → Bool} :
    OutCov.z4.any f = true ↔ ∃ a : ZMod 4, f a = true := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, mem_z4 a, h⟩⟩

theorem fixP_eq (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) {i k : ℕ} (hi : i < 36) (hk : k < 64) :
    (OutCov.z4.any fun a => OutCov.z4.any fun b => eqE κ (betaE 0 i (k, a, b)) (k, a, b)) =
      CFSG.KLie.CT.notB (allN 16 fun ab => strictB (Nat.add (Nat.mul 16 k) ab) fun x =>
        CFSG.KLie.CT.notB (eqC m (betaC T A 0 i x) x)) := by
  rw [Bool.eq_iff_iff, notB_eq', Bool.not_eq_true', z4_any]
  constructor
  · rintro ⟨a, h⟩
    rw [z4_any] at h
    obtain ⟨b, h⟩ := h
    have ha4 := ZMod.val_lt a
    have hb4 := ZMod.val_lt b
    cases e : allN 16 fun ab => strictB (Nat.add (Nat.mul 16 k) ab) fun x =>
        CFSG.KLie.CT.notB (eqC m (betaC T A 0 i x) x)
    · rfl
    · have h2 := allN_iff'.1 e (4 * a.val + b.val) (by omega)
      rw [strictB_eq', notB_eq'] at h2
      have hx : Nat.add (Nat.mul 16 k) (4 * a.val + b.val) < 1024 := by
        change 16 * k + (4 * a.val + b.val) < 1024
        omega
      have hd : dec (Nat.add (Nat.mul 16 k) (4 * a.val + b.val)) = (k, a, b) := by
        change dec (16 * k + (4 * a.val + b.val)) = _
        rw [dec_sixteen_add (by omega)]
        have e1 : (4 * a.val + b.val) / 4 = a.val := by omega
        have e2 : (4 * a.val + b.val) % 4 = b.val := by omega
        rw [e1, e2, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [← eqE_dec hm, ← betaE_dec hT hA hb (by norm_num) hi hx, hd, h] at h2
      exact absurd h2 (by decide)
  · intro h
    have h' : ¬ ∀ ab < 16, (strictB (Nat.add (Nat.mul 16 k) ab) fun x =>
        CFSG.KLie.CT.notB (eqC m (betaC T A 0 i x) x)) = true := fun hh => by
      rw [allN_iff'.2 hh] at h
      exact absurd h (by decide)
    push Not at h'
    obtain ⟨ab, hab, h2⟩ := h'
    rw [strictB_eq', notB_eq'] at h2
    simp only [ne_eq, Bool.not_eq_true, Bool.not_eq_false'] at h2
    have hx : Nat.add (Nat.mul 16 k) ab < 1024 := by
      change 16 * k + ab < 1024
      omega
    rw [← eqE_dec hm, ← betaE_dec hT hA hb (by norm_num) hi hx] at h2
    change eqE κ (betaE 0 i (dec (16 * k + ab))) (dec (16 * k + ab)) = true at h2
    rw [dec_sixteen_add hab] at h2
    refine ⟨((ab / 4 : ℕ) : ZMod 4), ?_⟩
    rw [z4_any]
    exact ⟨((ab % 4 : ℕ) : ZMod 4), h2⟩

theorem sorted_eq {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ := by
  have hp : l₁.Perm l₂ := (List.perm_ext_iff_of_nodup h₁.nodup h₂.nodup).2 h
  exact List.Perm.eq_of_pairwise (fun a _ _ _ h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl a))
    h₁ h₂ hp

noncomputable abbrev fk (FK j : ℕ) : ℕ := pg 6 (mask 6) FK j

theorem fixK_eq (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) {i FK nF : ℕ} (hi : i < 36)
    (h : fixOK T A m i FK nF = true) : fixK κ 0 i = (List.range nF).map (fk FK) := by
  unfold fixOK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hF : ∀ j < nF, fk FK j < 64 ∧ (j + 1 < nF → fk FK j < fk FK (j + 1)) := fun j hj => by
    have h3 := allN_iff'.1 h2 j hj
    rw [bAnd_iff, bIf_eq'] at h3
    refine ⟨Nat.blt_eq.mp h3.1, fun hj1 => ?_⟩
    have hb1 : Nat.blt (Nat.succ j) nF = true := Nat.blt_eq.mpr hj1
    rw [if_pos hb1] at h3
    exact Nat.blt_eq.mp h3.2
  have hmono : ∀ a b, a < b → b < nF → fk FK a < fk FK b := by
    intro a b hab hb'
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
      · exact lt_trans (ih h' (by omega)) ((hF b (by omega)).2 hb')
      · subst h'
        exact (hF a (by omega)).2 hb'
  unfold fixK
  refine sorted_eq ((List.pairwise_lt_range (n := 64)).filter _)
    (List.pairwise_map.2 ((List.pairwise_lt_range (n := nF)).imp_of_mem
      fun _ hb' hab => hmono _ _ hab (List.mem_range.1 hb'))) fun k => ?_
  rw [List.mem_filter, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨hk, hp⟩
    have h3 := allN_iff'.1 h1 k hk
    rw [bEq_iff, ← fixP_eq hT hA hb hm hi hk, hp] at h3
    obtain ⟨j, hj, e⟩ := memL_iff.1 h3
    exact ⟨j, List.mem_range.2 hj, e⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' := List.mem_range.1 hj
    have hk := (hF j hj').1
    refine ⟨hk, ?_⟩
    have h3 := allN_iff'.1 h1 _ hk
    rw [bEq_iff, ← fixP_eq hT hA hb hm hi hk] at h3
    rw [← h3]
    exact memL_iff.2 ⟨j, hj', rfl⟩

theorem rT_code (hG : GensG G) (hy : yOK G Y = true) {n : ℕ} (hn : n < 2304) :
    rT (n % 64) (n / 64) = unpack 42 6 (Y n) ∧ Cn (Y n) := by
  have h := rT_eq hG hy (Nat.mod_lt n (by norm_num)) (show n / 64 < 36 by omega)
  rwa [Nat.div_add_mod] at h

theorem rT_zero (hG : GensG G) (hy : yOK G Y = true) {i : ℕ} (hi : i < 36) :
    rT 0 i = unpack 42 6 (Y (64 * i)) ∧ Cn (Y (64 * i)) := by
  have h := rT_eq hG hy (t := 0) (by norm_num) hi
  rwa [Nat.add_zero] at h

theorem cn_ft (hG : GensG G) {FK FT nF : ℕ} (hFT : ∀ j < nF, tabAt FT j = tgK G (fk FK j)) {j : ℕ}
    (hj : j < nF) : Cn (tabAt FT j) := by
  rw [hFT j hj]
  exact (tgK_eq hG _).1

theorem c3_sound (hG : GensG G) (hy : yOK G Y = true) {ST : ℕ → ℕ} {i FK FT nF S3 nS : ℕ}
    (hi : i < 36) (hFT : ∀ j < nF, tabAt FT j = tgK G (fk FK j))
    (hF : fixK κ 0 i = (List.range nF).map (fk FK))
    (h : c3K Y ST (Y (64 * i)) FT nF S3 nS = true) :
    c3Case (indexOf (pts 42 6 20160 ST)) (pts 42 6 20160 ST) κ 0 i = true := by
  obtain ⟨hρ, hP⟩ := rT_zero hG hy hi
  have hfd : ∀ X, (∃ q < 20160, ST q = X) →
      found (indexOf (pts 42 6 20160 ST)) (pts 42 6 20160 ST) (unpack 42 6 X) = true := by
    rintro X ⟨q, hq, e⟩
    unfold pts
    exact found_pts hq e
  unfold c3Case
  dsimp only
  rw [hρ, hF, allBelow_iff']
  intro t ht
  rw [allBelow_iff']
  intro j hj
  obtain ⟨hr, hc⟩ := rT_eq hG hy ht hj
  rw [hr]
  have key : (commB (unpack 42 6 (Y (64 * j + t))) (unpack 42 6 (Y (64 * i))) &&
      (comp 42 (unpack 42 6 (Y (64 * j + t))) (unpack 42 6 (Y (64 * j + t))) == idTab 42) &&
      ((List.range nF).map (fk FK)).all fun k =>
        commB (unpack 42 6 (Y (64 * j + t))) (wordTab (tg k))) =
      c3C (Y (64 * j + t)) (Y (64 * i)) FT nF := by
    unfold c3C
    rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, commB_eq hc hP, sq_eq hc, Bool.and_assoc]
    have e3 : (((List.range nF).map (fk FK)).all fun k =>
        commB (unpack 42 6 (Y (64 * j + t))) (wordTab (tg k))) =
        allN nF fun j' => commPt 42 6 (Y (64 * j + t)) (tabAt FT j') := by
      rw [Bool.eq_iff_iff, List.all_eq_true, allN_iff']
      constructor
      · intro h' j' hj'
        have := h' _ (List.mem_map.2 ⟨j', List.mem_range.2 hj', rfl⟩)
        rwa [(tgK_eq hG _).2, ← hFT j' hj', commB_eq hc (cn_ft hG hFT hj')] at this
      · intro h' s hs
        obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hs
        have hj'' := List.mem_range.1 hj'
        rw [(tgK_eq hG _).2, ← hFT j' hj'', commB_eq hc (cn_ft hG hFT hj'')]
        exact h' j' hj''
    rw [e3]
  rw [key]
  have hn : 64 * j + t < 2304 := by omega
  have h3 := allN_iff'.1 h (64 * j + t) hn
  rw [strictB_eq', bIf_eq'] at h3
  cases hcc : c3C (Y (64 * j + t)) (Y (64 * i)) FT nF
  · rfl
  · rw [if_pos hcc, notB_eq', Bool.not_eq_true'] at h3
    have h4 : ¬ ∀ e < nS, CFSG.KLie.CT.notB (wit3 ST (Y (64 * i)) (64 * j + t) (Y (64 * j + t))
        (pg 32 (mask 32) S3 e)) = true := fun hh => by
      rw [allN_iff'.2 hh] at h3
      exact absurd h3 (by decide)
    push Not at h4
    obtain ⟨e, -, h5⟩ := h4
    rw [notB_eq'] at h5
    simp only [ne_eq, Bool.not_eq_true, Bool.not_eq_false'] at h5
    unfold wit3 at h5
    rw [bAnd_iff, bAnd_iff] at h5
    obtain ⟨-, hq, h6⟩ := h5
    have hq' := Nat.blt_eq.mp hq
    have h7 := Nat.eq_of_beq_eq_true h6
    cases hf : Nat.beq (Nat.mod (Nat.div (pg 32 (mask 32) S3 e) 4096) 2) 0
    · rw [hf] at h7
      have h8 := hfd _ ⟨_, hq', h7⟩
      change found _ _ (unpack 42 6 (pc (Y (64 * j + t)) (Y (64 * i)))) = true at h8
      rw [← comp_eq hc hP] at h8
      simp [h8]
    · rw [hf] at h7
      have h8 := hfd _ ⟨_, hq', h7⟩
      simp [h8]

theorem liftC_all (hA : AlOf A) (hG : GensG G) (hy : yOK G Y = true) {P k₁ k₂ LT nL : ℕ}
    (hPc : Cn P) (hκ : κ = ((k₁ : ZMod 4), (k₂ : ZMod 4)))
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val))
    (hl : lOK Y A k₁ k₂ m P LT nL = true) {f : ℕ × ℕ → Bool}
    (hf : ∀ n < 2304, CFSG.KC.L34Scan2.memL nL (fun k => pg 12 (mask 12) LT k) n = true →
      f (n % 64, n / 64) = true) :
    (liftC κ (unpack 42 6 P)).all f = true := by
  rw [List.all_eq_true]
  intro x hx
  unfold liftC at hx
  rw [List.mem_filter, List.mem_flatMap] at hx
  obtain ⟨⟨t, ht, hx'⟩, hp⟩ := hx
  rw [List.mem_map] at hx'
  obtain ⟨j, hj, rfl⟩ := hx'
  rw [List.mem_range] at ht hj
  have hn : 64 * j + t < 2304 := by omega
  unfold lOK at hl
  rw [bAnd_iff] at hl
  have h1 := allN_iff'.1 hl.1 _ hn
  rw [bEq_iff] at h1
  obtain ⟨hr, hc⟩ := rT_eq hG hy ht hj
  have e1 : (64 * j + t) % 64 = t := by omega
  have e2 : (64 * j + t) / 64 = j := by omega
  have := hf _ hn ?_
  · rwa [e1, e2] at this
  · rw [← h1]
    unfold inLK
    rw [bAnd_iff]
    rw [Bool.and_eq_true, invar_eq hA hj hκ hm, hr, commB_eq hc hPc] at hp
    refine ⟨?_, hp.2⟩
    change invK A k₁ k₂ m ((64 * j + t) / 64) = true
    rw [e2]
    exact hp.1

theorem inTabs_eq {k cnt X : ℕ} {EG E PL POS SRT SRI : ℕ → ℕ}
    (hEp : ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false EG EG k cnt E PL POS SRT SRI i = true)
    (hX : Cn X) : inTabs (penumRec 42 6 cnt E PL).tabs (unpack 42 6 X) =
      CFSG.KC.L34Scan2.memL cnt E X := by
  unfold inTabs
  rw [Bool.eq_iff_iff, found_penumRec_iff hEp hX, memL_iff]

theorem invW_mem (hT : T1Of T) (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) {w : ℕ}
    (h : invW T m w = true) : w < 1024 ∧ dec w ∈ invsE κ := by
  unfold invW at h
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hw := Nat.blt_eq.mp h1
  refine ⟨hw, ?_⟩
  unfold invsE
  rw [List.mem_filter]
  refine ⟨mem_els.2 (dec_lt hw), ?_⟩
  rw [mulE_dec hT hw hw, oneE_eq, eqE_dec hm]
  have hne : w / 16 ≠ 0 := Nat.ne_of_beq_eq_false (bNot_iff.1 h3)
  have e : (dec w).1 = w / 16 := rfl
  rw [e, Bool.and_eq_true]
  exact ⟨h2, by simpa using hne⟩

theorem twoOK_eq (hG : GensG G) {x x₁ P FK FT nF : ℕ} (hx : Cn x) (h1 : Cn x₁) (hP : Cn P)
    (hFT : ∀ j < nF, tabAt FT j = tgK G (fk FK j)) :
    twoOK (unpack 42 6 x) ([unpack 42 6 x₁, unpack 42 6 P] ++
      ((List.range nF).map (fk FK)).map fun k => wordTab (tg k)) = twoK x x₁ P FT nF := by
  have hs : ∀ s, Cn s → (is2 (comp 42 (unpack 42 6 x) (unpack 42 6 s)) &&
      is2 (comp 42 (unpack 42 6 s) (unpack 42 6 x))) = two1 x s := fun s hs => by
    unfold two1
    rw [CFSG.KS.Raw.Orb.bAnd_eq, comp_eq hx hs, comp_eq hs hx, is2_eq (cn_pc hx hs),
      is2_eq (cn_pc hs hx)]
  unfold twoOK twoK
  rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, is2_eq hx,
    List.cons_append, List.cons_append, List.nil_append, List.all_cons, List.all_cons, hs _ h1,
    hs _ hP]
  have e3 : ((((List.range nF).map (fk FK)).map fun k => wordTab (tg k)).all fun s =>
      is2 (comp 42 (unpack 42 6 x) s) && is2 (comp 42 s (unpack 42 6 x))) =
      allN nF fun j => two1 x (tabAt FT j) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, allN_iff']
    constructor
    · intro h' j hj
      have := h' _ (List.mem_map.2 ⟨fk FK j, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, rfl⟩)
      rwa [(tgK_eq hG _).2, ← hFT j hj, hs _ (cn_ft hG hFT hj)] at this
    · intro h' s hs'
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hs'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk'
      have hj' := List.mem_range.1 hj
      rw [(tgK_eq hG _).2, ← hFT j hj', hs _ (cn_ft hG hFT hj')]
      exact h' j hj'
  rw [e3]

theorem genOK_parts {EG : ℕ → ℕ} {FK FT nF P k : ℕ} (h : genOK G EG FK FT nF P k = true) :
    (∀ j < nF, tabAt FT j = tgK G (fk FK j) ∧ EG j = tabAt FT j) ∧ EG nF = P ∧ k = nF + 1 := by
  unfold genOK at h
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  have h4 := allN_iff'.1 h1 j hj
  rw [bAnd_iff] at h4
  exact ⟨Nat.eq_of_beq_eq_true h4.1, Nat.eq_of_beq_eq_true h4.2⟩

theorem gensOK_of (hG : GensG G) {EG : ℕ → ℕ} {FK FT nF P k : ℕ} (hP : Cn P)
    (h : genOK G EG FK FT nF P k = true) :
    GensOK 42 6 k EG ((((List.range nF).map (fk FK)).map fun k => wordTab (tg k)) ++
      [unpack 42 6 P]).toArray := by
  obtain ⟨h1, h2, h3⟩ := genOK_parts h
  refine ⟨by simp [h3], fun j hj => ?_⟩
  rw [h3] at hj
  rw [getElem!_pos _ j (by simp; omega), List.getElem_toArray]
  rcases Nat.lt_or_ge j nF with hj' | hj'
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [(h1 j hj').2, (h1 j hj').1]
    exact ⟨(tgK_eq hG _).2, (tgK_eq hG _).1⟩
  · have e : j = nF := by omega
    subst e
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem_cons_zero]
    rw [h2]
    exact ⟨rfl, hP⟩

theorem c4_sound (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) (hG : GensG G)
    (hy : yOK G Y = true) {E EG PL POS SRT SRI : ℕ → ℕ} {i FK FT nF LT nL wA WB cnt k k₁ k₂ : ℕ}
    (hi : i < 36) (hκ : κ = ((k₁ : ZMod 4), (k₂ : ZMod 4)))
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val))
    (hF : fixK κ 0 i = (List.range nF).map (fk FK))
    (hgen : genOK G EG FK FT nF (Y (64 * i)) k = true)
    (hEh : penumHdK (pidn 42 6) cnt 64 E PL = true)
    (hEp : ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false EG EG k cnt E PL POS SRT SRI i = true)
    (hl : lOK Y A k₁ k₂ m (Y (64 * i)) LT nL = true)
    (h4a : c4AK Y T A E cnt m LT nL wA = true)
    (h4b : c4BK Y T A E cnt m (Y (64 * i)) FT nF LT nL WB = true) :
    c4Case κ 0 i = true := by
  obtain ⟨hρ, hP⟩ := rT_zero hG hy hi
  have hFT : ∀ j < nF, tabAt FT j = tgK G (fk FK j) := fun j hj => ((genOK_parts hgen).1 j hj).1
  have hen := penumK_left_sound (cap := 64) CFSG.KC.L34Scan.hsz42 (gensOK_of hG hP hgen) hEh hEp
  unfold c4Case ftabs
  dsimp only
  rw [hρ, hF, hen.1, Bool.and_eq_true]
  constructor
  · unfold c4A
    unfold c4AK at h4a
    rw [bAnd_iff] at h4a
    obtain ⟨hw, hall⟩ := h4a
    obtain ⟨hwl, hwm⟩ := invW_mem hT hm hw
    rw [List.any_eq_true]
    refine ⟨dec wA, hwm, liftC_all hA hG hy hP hκ hm hl fun n hn hmem => ?_⟩
    obtain ⟨q, hq, e⟩ := memL_iff.1 hmem
    have h1 := allN_iff'.1 hall q hq
    rw [strictB_eq', e, orK_eq] at h1
    obtain ⟨hr, hc⟩ := rT_code hG hy hn
    dsimp only
    rw [hr, inTabs_eq hEp hc, betaE_dec hT hA hb (Nat.mod_lt n (by norm_num)) (by omega) hwl,
      eqE_dec hm]
    rw [bNot_eq] at h1
    exact h1
  · unfold c4B
    unfold c4BK at h4b
    refine liftC_all hA hG hy hP hκ hm hl fun n₁ hn₁ hmem₁ => ?_
    obtain ⟨q₁, hq₁, e₁⟩ := memL_iff.1 hmem₁
    have h1 := allN_iff'.1 h4b q₁ hq₁
    rw [strictB_eq', e₁, strictB_eq', orK_eq, orK_eq, strictB_eq'] at h1
    obtain ⟨hr₁, hc₁⟩ := rT_code hG hy hn₁
    dsimp only
    rw [hr₁, inTabs_eq hEp hc₁, is2_eq hc₁]
    cases hmE : CFSG.KC.L34Scan2.memL cnt E (Y n₁)
    · cases h2 : is2K (Y n₁)
      · rfl
      · rw [hmE, h2, bNot_eq] at h1
        simp only [Bool.not_true, Bool.false_or] at h1
        rw [bAnd_iff] at h1
        obtain ⟨hw, hall⟩ := h1
        obtain ⟨hwl, hwm⟩ := invW_mem hT hm hw
        simp only [Bool.false_or, Bool.not_true]
        rw [List.any_eq_true]
        refine ⟨_, hwm, liftC_all hA hG hy hP hκ hm hl fun n hn hmem => ?_⟩
        obtain ⟨q, hq, e⟩ := memL_iff.1 hmem
        have h3 := allN_iff'.1 hall q hq
        rw [strictB_eq', e, orK_eq, bNot_eq] at h3
        obtain ⟨hr, hc⟩ := rT_code hG hy hn
        dsimp only
        rw [hr, betaE_dec hT hA hb (Nat.mod_lt n (by norm_num)) (by omega) hwl, eqE_dec hm,
          twoOK_eq hG hc hc₁ hP hFT]
        exact h3
    · rfl

theorem inverts_eq (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) {i : ℕ} (hi : i < 36) :
    inverts κ 0 i = invsK T A m i := by
  have d1 : ((0 : ℕ), (1 : ZMod 4), (0 : ZMod 4)) = dec 4 := by decide
  have d2 : ((0 : ℕ), (-1 : ZMod 4), (0 : ZMod 4)) = dec 12 := by decide
  have d3 : ((0 : ℕ), (0 : ZMod 4), (1 : ZMod 4)) = dec 1 := by decide
  have d4 : ((0 : ℕ), (0 : ZMod 4), (-1 : ZMod 4)) = dec 3 := by decide
  unfold inverts invsK
  rw [d1, d2, d3, d4, betaE_dec hT hA hb (by norm_num) hi (by norm_num),
    betaE_dec hT hA hb (by norm_num) hi (by norm_num), eqE_dec hm, eqE_dec hm,
    CFSG.KS.Raw.Orb.bAnd_eq]

theorem c5_sound (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val)) {i V : ℕ} (hi : i < 36)
    (h : c5K T A m i V = true) : c5Case κ 0 i = true := by
  unfold c5Case
  unfold c5K at h
  rw [orK_eq, bNot_eq] at h
  rw [inverts_eq hT hA hb hm hi]
  cases hinv : invsK T A m i
  · rfl
  · rw [hinv] at h
    simp only [Bool.not_true, Bool.false_or] at h ⊢
    rw [els_all]
    intro c hc
    have h1 := allN_iff'.1 h c hc
    rw [bIf_eq', CFSG.KS.Raw.Orb.bAnd_eq] at h1
    have hv : pg 10 (mask 10) V c < 1024 := lt_of_lt_of_eq (pg_lt' 10 V c) (by norm_num)
    rw [mulE_dec hT hc hc, oneE_eq, eqE_dec hm, betaE_dec hT hA hb (by norm_num) hi hc, eqE_dec hm]
    by_cases hcc : (eqC m (mulC T c c) 0 && eqC m (betaC T A 0 i c) c) = true
    · rw [hcc, Bool.not_true, Bool.false_or, els_any]
      rw [if_pos hcc, strictB_eq'] at h1
      refine ⟨_, hv, ?_⟩
      rw [betaE_dec hT hA hb (by norm_num) hi hv,
        mulE_dec hT (betaC_lt hb (by norm_num) hi hv) hc, eqE_dec hm]
      exact h1
    · rw [Bool.not_eq_true] at hcc
      rw [hcc]
      rfl

theorem case_sound (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) (hG : GensG G)
    (hy : yOK G Y = true) {ST E EG PL POS SRT SRI : ℕ → ℕ}
    {h FK FT LT S3 WB V cnt k i k₁ k₂ : ℕ}
    (hST : (enumBFS 42 gensS 20160).tabs = pts 42 6 20160 ST)
    (hEh : penumHdK (pidn 42 6) cnt 64 E PL = true)
    (hEp : ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false EG EG k cnt E PL POS SRT SRI i = true)
    (hi : i < 36) (h0 : hf h 0 = 64 * i) (h1 : hf h 1 = k₁) (h2 : hf h 2 = k₂) (h3 : hf h 3 = m)
    (hκ : κ = ((k₁ : ZMod 4), (k₂ : ZMod 4)))
    (hm : ∀ a b, inKb κ a b = m.testBit (4 * a.val + b.val))
    (hc : caseK Y ST T A G EG E h FK FT LT S3 WB V cnt k = true) :
    (c3Case (indexOf (enumBFS 42 gensS 20160).tabs) (enumBFS 42 gensS 20160).tabs κ 0 i &&
      c4Case κ 0 i && c5Case κ 0 i) = true := by
  unfold caseK at hc
  rw [strictB_eq', h0, h1, h2, h3] at hc
  have hdiv : Nat.div (64 * i) (nat_lit 64) = i := by
    change 64 * i / 64 = i
    omega
  rw [hdiv] at hc
  simp only [bAnd_iff] at hc
  obtain ⟨⟨hfx, hgen⟩, ⟨hl, hc3⟩, ⟨h4a, h4b⟩, hc5⟩ := hc
  have hF := fixK_eq hT hA hb hm hi hfx
  have hFT : ∀ j < hf h 4, tabAt FT j = tgK G (fk FK j) := fun j hj =>
    ((genOK_parts hgen).1 j hj).1
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, c4_sound hT hA hb hG hy hi hκ hm hF hgen hEh hEp hl h4a h4b⟩,
    c5_sound hT hA hb hm hi hc5⟩
  rw [hST]
  exact c3_sound hG hy hi hFT hF hc3

theorem invOKE_of (hT : T1Of T) (h : invOKK T = true) : invOKE = true := by
  unfold invOKE invOKK at *
  rw [allBelow_iff']
  intro t ht
  have h1 := Nat.eq_of_beq_eq_true (allN_iff'.1 h t ht)
  have hlt := invIdxC_lt (T := T) t
  rw [invIdxC_eq hT ht] at hlt h1
  rw [invIdx_eq, Bool.and_eq_true, hT t _ ht hlt, decide_eq_true_eq]
  refine ⟨hlt, ?_⟩
  simp only [quad, beq_iff_eq]
  exact h1

theorem match_iff (hG : GensG G) (hy : yOK G Y = true) {RP : ℕ → ℕ} (h : matchOK Y RP = true)
    {r t i : ℕ} (hr : r < 3) (hc : Cn (RP (r + 1))) (ht : t < 64) (hi : i < 36) :
    (rT t i == unpack 42 6 (RP (r + 1))) = true → t = 0 ∧ i = r + 1 := by
  intro e
  obtain ⟨hr', hc'⟩ := rT_eq hG hy ht hi
  rw [hr', beq_unpack hc' hc] at e
  have h1 := allN_iff'.1 h r hr
  rw [strictB_eq'] at h1
  have hn : 64 * i + t < 2304 := by omega
  have h2 := allN_iff'.1 h1 (64 * i + t) hn
  rw [bEq_iff, e] at h2
  have h3 := Nat.eq_of_beq_eq_true h2.symm
  change 64 * i + t = 64 * (r + 1) at h3
  omega

end CFSG.KC.L34W.OCS

end
