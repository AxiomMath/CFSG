module

public import Certificates.Data.Kernel.L34Syl.Defs
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
import CFSG.Certificates.Kernel.L34Syl.SoundBase
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KC.L34Syl

open CFSG.KC.Enum

@[expose] noncomputable def pp (n w m x : Nat) : Equiv.Perm (Fin n) :=
  CFSG.KS.PK.permOf n (pg w m x)

@[expose] def PermN (n w m x : Nat) : Prop := CFSG.KS.PK.IsPermN n (pg w m x)

@[expose] noncomputable def gen (n w m : Nat) (L : Nat → Nat) (ng : Nat) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ j < ng, pp n w m (L (2 * j)) = g}

@[expose] def mset (n s : Nat) : Set (Fin n) := {i | Nat.testBit s i}

@[expose] def LettersInv (n w m : Nat) (L : Nat → Nat) (ng : Nat) : Prop :=
  ∀ j < ng, PermN n w m (L (2 * j)) ∧ PermN n w m (L (2 * j + 1)) ∧
    pp n w m (L (2 * j + 1)) = (pp n w m (L (2 * j)))⁻¹

@[expose] def CanonGen {n : Nat} (p : Nat) (x : Equiv.Perm (Fin n)) : Prop :=
  ∃ a : Fin n, (∀ b : Fin n, b < a → x b = b) ∧ x a ≠ a ∧
    ∀ j, 2 ≤ j → j < p → ((x a : Fin n) : Nat) < (((x ^ j) a : Fin n) : Nat)

open CFSG.KS.PK
open scoped commutatorElement

private theorem pp_eq (n w m x : Nat) : pp n w m x = permOf n (pg w m x) := rfl

private theorem pp_apply {n w m x : Nat} (h : PermN n w m x) (i : Fin n) :
    (pp n w m x i : Nat) = pg w m x i :=
  permOf_apply h i

private theorem mset_img {n w m g : Nat} (s : Nat) (hg : PermN n w m g) :
    mset n (img n w m g s) = ⇑(pp n w m g) '' mset n s := by
  ext i
  change (img n w m g s).testBit i = true ↔ _
  rw [SB.img_testBit]
  constructor
  · rintro ⟨x, hx, h1, h2⟩
    refine ⟨⟨x, hx⟩, h1, Fin.ext ?_⟩
    rw [pp_apply hg]
    exact h2
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x.isLt, hx, (pp_apply hg x).symm⟩

private theorem letter_sp {n w m ng : Nat} {L : Nat → Nat} (hL : LettersInv n w m L ng) {l : Nat}
    (hl : l < 2 * ng) :
    PermN n w m (L l) ∧ pp n w m (L l) ∈ gen n w m L ng ∧ PermN n w m (L (Nat.xor l (nat_lit 1))) ∧
      pp n w m (L (Nat.xor l (nat_lit 1))) = (pp n w m (L l))⁻¹ := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' l
  · obtain ⟨h1, h2, h3⟩ := hL j (by omega)
    rw [SB.xor_even]
    exact ⟨h1, Subgroup.subset_closure ⟨j, by omega, rfl⟩, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := hL j (by omega)
    rw [SB.xor_odd]
    refine ⟨h2, ?_, h1, ?_⟩
    · rw [h3]
      exact inv_mem (Subgroup.subset_closure ⟨j, by omega, rfl⟩)
    · rw [h3, inv_inv]

private theorem wv_cons (w m : Nat) (L : Nat → Nat) (l : Nat) (ws : List Nat) :
    wv w m L (l :: ws) = fun x => wv w m L ws (pg w m (L l) x) := rfl

private theorem wvI_cons (w m : Nat) (L : Nat → Nat) (l : Nat) (ws : List Nat) :
    wvI w m L (l :: ws) = fun x => pg w m (L (Nat.xor l (nat_lit 1))) (wvI w m L ws x) := rfl

private theorem word_sp {n w m ng : Nat} {L : Nat → Nat} (hL : LettersInv n w m L ng) :
    ∀ ws : List Nat, ltL (2 * ng) ws = true →
      IsPermN n (wv w m L ws) ∧ permOf n (wv w m L ws) ∈ gen n w m L ng ∧
      IsPermN n (wvI w m L ws) ∧ permOf n (wvI w m L ws) = (permOf n (wv w m L ws))⁻¹
  | [], _ => by
    have e0 : wv w m L [] = fun x => x := rfl
    have e1 : wvI w m L [] = fun x => x := rfl
    rw [e0, e1, SB.permOf_id', inv_one]
    exact ⟨isPermN_id n, one_mem _, isPermN_id n, rfl⟩
  | l :: ws, h => by
    have h' : bAnd(Nat.blt l (2 * ng), ltL (2 * ng) ws) = true := h
    obtain ⟨h1, h2⟩ := SB.band h'
    obtain ⟨p1, g1, q1, e1⟩ := word_sp hL ws h2
    obtain ⟨pl, gl, pli, eli⟩ := letter_sp hL (SB.bltT h1)
    rw [wv_cons, wvI_cons]
    refine ⟨IsPermN.comp p1 pl, ?_, IsPermN.comp pli q1, ?_⟩
    · rw [← permOf_mul p1 pl]
      exact mul_mem g1 gl
    · rw [← permOf_mul pli q1, ← permOf_mul p1 pl, mul_inv_rev, ← e1]
      exact congrArg (· * permOf n (wvI w m L ws)) eli

theorem lettersOK_sound {n w m nw ng : Nat} {L : Nat → Nat} (h : lettersOK n w m nw L ng = true) :
    LettersInv n w m L ng := by
  intro j hj
  have h1 := SB.allN_sp h j hj
  simp only [SB.sB] at h1
  obtain ⟨ha, h2⟩ := SB.band h1
  obtain ⟨hb, hab⟩ := SB.band h2
  have hra := (SB.canonP_sp ha).2
  have hrb := (SB.canonP_sp hb).2
  have hinv : ∀ i < n, pg w m (L (2 * j + 1)) (pg w m (L (2 * j)) i) = i := SB.invPt_sp hab
  have hpa : PermN n w m (L (2 * j)) :=
    ⟨hra, fun x hx y hy hxy => by rw [← hinv x hx, ← hinv y hy, hxy]⟩
  have hpb : PermN n w m (L (2 * j + 1)) := by
    refine ⟨hrb, fun x hx y hy hxy => ?_⟩
    obtain ⟨x', hx', rfl⟩ := IsPermN.surj hpa hx
    obtain ⟨y', hy', rfl⟩ := IsPermN.surj hpa hy
    rw [hinv x' hx', hinv y' hy'] at hxy
    rw [hxy]
  refine ⟨hpa, hpb, eq_inv_of_mul_eq_one_left ?_⟩
  rw [pp_eq, pp_eq, permOf_mul hpb hpa]
  exact (permOf_eq_one_iff (IsPermN.comp hpb hpa)).2 hinv

theorem wordK_sound {n w m ng : Nat} {L : Nat → Nat} {ws : List Nat} {tgt : Nat}
    (hL : LettersInv n w m L ng) (h : wordK n w m (2 * ng) L ws tgt = true) :
    PermN n w m tgt ∧ pp n w m tgt ∈ gen n w m L ng := by
  unfold wordK at h
  obtain ⟨h1, h2⟩ := SB.band h
  obtain ⟨p1, g1, -, -⟩ := word_sp hL ws h1
  have e : ∀ i < n, wv w m L ws i = pg w m tgt i := fun i hi => SB.beqT (SB.allN_sp h2 i hi)
  refine ⟨SB.isPermN_congr' e p1, ?_⟩
  rw [pp_eq, ← permOf_congr e]
  exact g1

theorem commK_sound {n w m ng : Nat} {L : Nat → Nat} {u v : List Nat} {tgt : Nat}
    (hL : LettersInv n w m L ng) (h : commK n w m (2 * ng) L u v tgt = true) :
    PermN n w m tgt ∧ pp n w m tgt ∈ ⁅gen n w m L ng, gen n w m L ng⁆ := by
  unfold commK at h
  obtain ⟨hu, h2⟩ := SB.band h
  obtain ⟨hv, h3⟩ := SB.band h2
  obtain ⟨pu, gu, pui, eu⟩ := word_sp hL u hu
  obtain ⟨pv, gv, pvi, ev⟩ := word_sp hL v hv
  have e : ∀ i < n, wv w m L u (wv w m L v (wvI w m L u (wvI w m L v i))) = pg w m tgt i :=
    fun i hi => SB.beqT (SB.allN_sp h3 i hi)
  have hc := IsPermN.comp pu (IsPermN.comp pv (IsPermN.comp pui pvi))
  refine ⟨SB.isPermN_congr' e hc, ?_⟩
  rw [pp_eq, ← permOf_congr e]
  have e2 : permOf n (wv w m L u) * (permOf n (wv w m L v) *
      (permOf n (wvI w m L u) * permOf n (wvI w m L v))) =
      permOf n (fun i => wv w m L u (wv w m L v (wvI w m L u (wvI w m L v i)))) := by
    rw [permOf_mul pui pvi, permOf_mul pv (IsPermN.comp pui pvi),
      permOf_mul pu (IsPermN.comp pv (IsPermN.comp pui pvi))]
  have e3 : permOf n (wv w m L u) * (permOf n (wv w m L v) *
      ((permOf n (wv w m L u))⁻¹ * (permOf n (wv w m L v))⁻¹)) =
      ⁅permOf n (wv w m L u), permOf n (wv w m L v)⁆ := by
    rw [commutatorElement_def]
    simp only [mul_assoc]
  rw [← e2, eu, ev, e3]
  exact Subgroup.commutator_mem_commutator gu gv

theorem wordsK_sound {n w m ng : Nat} {L tg : Nat → Nat} {ws : List (List Nat)} {i : Nat}
    (hL : LettersInv n w m L ng) (h : wordsK n w m (2 * ng) L tg ws i = true) :
    ∀ k < ws.length, PermN n w m (tg (i + k)) ∧ pp n w m (tg (i + k)) ∈ gen n w m L ng := by
  induction ws generalizing i with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons u ws ih =>
    have h' : bAnd(strictB (tg i) (fun r => wordK n w m (2 * ng) L u r),
        wordsK n w m (2 * ng) L tg ws (Nat.succ i)) = true := h
    obtain ⟨h1, h2⟩ := SB.band h'
    rw [SB.sB] at h1
    intro k hk
    cases k with
    | zero => exact wordK_sound hL h1
    | succ k =>
      have := ih h2 k (by simpa using hk)
      have e : Nat.succ i + k = i + (k + 1) := by omega
      rwa [e] at this

theorem commsK_sound {n w m ng : Nat} {L tg : Nat → Nat} {prs : List (List Nat × List Nat)}
    {i : Nat} (hL : LettersInv n w m L ng) (h : commsK n w m (2 * ng) L tg prs i = true) :
    ∀ k < prs.length, PermN n w m (tg (i + k)) ∧
      pp n w m (tg (i + k)) ∈ ⁅gen n w m L ng, gen n w m L ng⁆ := by
  induction prs generalizing i with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons e prs ih =>
    obtain ⟨u, v⟩ := e
    have h' : bAnd(strictB (tg i) (fun r => commK n w m (2 * ng) L u v r),
        commsK n w m (2 * ng) L tg prs (Nat.succ i)) = true := h
    obtain ⟨h1, h2⟩ := SB.band h'
    rw [SB.sB] at h1
    intro k hk
    cases k with
    | zero => exact commK_sound hL h1
    | succ k =>
      have := ih h2 k (by simpa using hk)
      have e : Nat.succ i + k = i + (k + 1) := by omega
      rwa [e] at this

private theorem grpE_sp {n w m nw pm b bm ng T D N k : Nat} {L : Nat → Nat}
    (h : grpE n w m nw pm b bm L ng T D N k = true) :
    canonP n w m nw (lane nw pm T k) = true ∧
    (k ≠ 0 → lane nw pm T (k - 1) < lane nw pm T k) ∧
    (SB.gdep b ng D k = 0 → ∀ i < n, pg w m (lane nw pm T k) i = i) ∧
    (SB.gdep b ng D k ≠ 0 → ∃ par < N, ∃ l < 2 * ng, SB.gdep b ng D par + 1 = SB.gdep b ng D k ∧
      ∀ i < n, pg w m (lane nw pm T k) i = pg w m (L l) (pg w m (lane nw pm T par) i)) ∧
    ∀ j < ng, ∃ c < N, ∀ i < n,
      pg w m (lane nw pm T c) i = pg w m (L (2 * j)) (pg w m (lane nw pm T k) i) := by
  unfold grpE at h
  simp only [SB.sB] at h
  obtain ⟨h1, h2⟩ := SB.band h
  obtain ⟨h2, h3⟩ := SB.band h2
  obtain ⟨h3, h4⟩ := SB.band h3
  refine ⟨h1, fun hk => SB.bltT (SB.bIf_f h2 (SB.beq_ne hk)), fun hd => ?_, fun hd => ?_,
    fun j hj => ?_⟩
  · exact SB.idPt_sp (SB.bIf_t h3 (SB.beq_of_eq hd))
  · obtain ⟨hp, h5⟩ := SB.band (SB.bIf_f h3 (SB.beq_ne hd))
    obtain ⟨hl, h6⟩ := SB.band h5
    obtain ⟨hdp, he⟩ := SB.band h6
    exact ⟨_, SB.bltT hp, _, SB.bltT hl, SB.beqT hdp, SB.eq2_sp he⟩
  · obtain ⟨hc, he⟩ := SB.band (SB.allN_sp h4 j hj)
    exact ⟨_, SB.bltT hc, SB.eq2_sp he⟩

theorem grpK_sound {n w m nw pm b bm ng T D N : Nat} {L : Nat → Nat}
    (hnw : nw = n * w) (hm : m = 2 ^ w - 1) (hw : 0 < w) (hL : LettersInv n w m L ng)
    (h : grpK n w m nw pm b bm L ng T D N = true) :
    (∀ k < N, PermN n w m (lane nw pm T k)) ∧
    (∀ k < N, ∀ k' < N, pp n w m (lane nw pm T k) = pp n w m (lane nw pm T k') → k = k') ∧
    ∀ g, g ∈ gen n w m L ng ↔ ∃ k < N, pp n w m (lane nw pm T k) = g := by
  obtain ⟨hN, hall⟩ := SB.band h
  have hN := SB.bltT hN
  have hE := fun k hk => grpE_sp (SB.allN_sp hall k hk)
  have hP : ∀ k < N, PermN n w m (lane nw pm T k) ∧ pp n w m (lane nw pm T k) ∈ gen n w m L ng := by
    refine SB.depth_ind (dep := SB.gdep b ng D) (fun k hk hd => ?_) (fun k hk hd => ?_)
    · have hid := (hE k hk).2.2.1 hd
      have hp : PermN n w m (lane nw pm T k) :=
        SB.isPermN_congr' (fun i hi => (hid i hi).symm) (isPermN_id n)
      refine ⟨hp, ?_⟩
      rw [pp_eq, (permOf_eq_one_iff hp).2 hid]
      exact one_mem _
    · obtain ⟨par, hpar, l, hl, hdp, he⟩ := (hE k hk).2.2.2.1 hd
      refine ⟨par, hpar, hdp, fun hq => ?_⟩
      obtain ⟨pp1, g1⟩ := hq
      obtain ⟨pl, gl, -, -⟩ := letter_sp hL hl
      have hp : PermN n w m (lane nw pm T k) :=
        SB.isPermN_congr' (fun i hi => (he i hi).symm) (IsPermN.comp pl pp1)
      refine ⟨hp, ?_⟩
      rw [pp_eq, permOf_congr he, ← permOf_mul pl pp1]
      exact mul_mem gl g1
  have hlt := SB.mono_of_adj (f := lane nw pm T) (N := N) fun k hk hk0 => (hE k hk).2.1 hk0
  refine ⟨fun k hk => (hP k hk).1, fun k hk k' hk' e => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · have hfe : ∀ i < n, pg w m (lane nw pm T k) i = pg w m (lane nw pm T k') i :=
      (permOf_eq_iff (hP k hk).1 (hP k' hk').1).1 e
    have hx := (SB.canonP_sp (hE k hk).1).1
    have hy := (SB.canonP_sp (hE k' hk').1).1
    have ex : lane nw pm T k = lane nw pm T k' := by
      subst hnw hm
      refine CFSG.KS.PF.eq_of_fields hw hx hy ?_
      rw [SB.mask_eq]
      exact hfe
    rcases Nat.lt_trichotomy k k' with h1 | h1 | h1
    · exact absurd ex (Nat.ne_of_lt (hlt k hk k' hk' h1))
    · exact h1
    · exact absurd ex.symm (Nat.ne_of_lt (hlt k' hk' k hk h1))
  · have h1 : (1 : Equiv.Perm (Fin n)) ∈ {g | ∃ k < N, pp n w m (lane nw pm T k) = g} := by
      obtain ⟨k0, hk0, hd0⟩ := SB.exists_dep0 (dep := SB.gdep b ng D) hN fun k hk hd => by
        obtain ⟨par, hp, -, -, hdp, -⟩ := (hE k hk).2.2.2.1 hd
        exact ⟨par, hp, hdp⟩
      exact ⟨k0, hk0, (permOf_eq_one_iff (hP k0 hk0).1).2 ((hE k0 hk0).2.2.1 hd0)⟩
    refine SB.closure_sub h1 ?_ g hg
    rintro x ⟨j, hj, rfl⟩ y ⟨k, hk, rfl⟩
    obtain ⟨c, hc, he⟩ := (hE k hk).2.2.2.2 j hj
    refine ⟨c, hc, ?_⟩
    rw [pp_eq, permOf_congr he, ← permOf_mul (hL j hj).1 (hP k hk).1]
    rfl
  · rintro ⟨k, hk, rfl⟩
    exact (hP k hk).2

theorem powsK_sound {n w m nw pm p RT cnt : Nat} (hp : 2 ≤ p)
    (h : powsK n w m nw pm p RT cnt = true) :
    ∀ i < cnt, (∀ k < p - 1, PermN n w m (lane nw pm RT ((p - 1) * i + k)) ∧
        pp n w m (lane nw pm RT ((p - 1) * i + k)) = pp n w m (lane nw pm RT ((p - 1) * i)) ^ (k + 1)) ∧
      pp n w m (lane nw pm RT ((p - 1) * i)) ^ p = 1 ∧ pp n w m (lane nw pm RT ((p - 1) * i)) ≠ 1 := by
  intro i hi
  have h1 := SB.allN_sp h i hi
  simp only [SB.sB] at h1
  obtain ⟨hc, h2⟩ := SB.band h1
  obtain ⟨hnid, h3⟩ := SB.band h2
  obtain ⟨hst, hinv⟩ := SB.band h3
  have hc' : canonP n w m nw (lane nw pm RT ((p - 1) * i)) = true := hc
  have hinv' : ∀ j < n, pg w m (lane nw pm RT ((p - 1) * i + (p - 2)))
      (pg w m (lane nw pm RT ((p - 1) * i)) j) = j := SB.invPt_sp hinv
  have hst' : ∀ k < p - 2, ∀ j < n, pg w m (lane nw pm RT ((p - 1) * i + (k + 1))) j =
      pg w m (lane nw pm RT ((p - 1) * i + k)) (pg w m (lane nw pm RT ((p - 1) * i)) j) :=
    fun k hk => SB.eq2_sp (SB.allN_sp hst k hk)
  have hpr : PermN n w m (lane nw pm RT ((p - 1) * i)) :=
    ⟨(SB.canonP_sp hc').2, fun x hx y hy hxy => by rw [← hinv' x hx, ← hinv' y hy, hxy]⟩
  have hk : ∀ k < p - 1, PermN n w m (lane nw pm RT ((p - 1) * i + k)) ∧
      pp n w m (lane nw pm RT ((p - 1) * i + k)) =
        pp n w m (lane nw pm RT ((p - 1) * i)) ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.add_zero, pow_one]
      exact ⟨hpr, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨p1, e1⟩ := ih (by omega)
      have he := hst' k (by omega)
      refine ⟨SB.isPermN_congr' (fun j hj => (he j hj).symm) (IsPermN.comp p1 hpr), ?_⟩
      rw [pp_eq, permOf_congr he, ← permOf_mul p1 hpr, pow_succ, ← e1]
      rfl
  refine ⟨hk, ?_, fun e => ?_⟩
  · obtain ⟨pl, el⟩ := hk (p - 2) (by omega)
    have e1 : pp n w m (lane nw pm RT ((p - 1) * i + (p - 2))) *
        pp n w m (lane nw pm RT ((p - 1) * i)) = 1 := by
      rw [pp_eq, pp_eq, permOf_mul pl hpr]
      exact (permOf_eq_one_iff (IsPermN.comp pl hpr)).2 hinv'
    have e4 : pp n w m (lane nw pm RT ((p - 1) * i)) ^ p =
        pp n w m (lane nw pm RT ((p - 1) * i)) ^ (p - 2 + 1) *
          pp n w m (lane nw pm RT ((p - 1) * i)) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [e4, ← el]
    exact e1
  · have hid : idPt n w m (lane nw pm RT ((p - 1) * i)) = true :=
      SB.allN_in fun j hj => SB.beq_of_eq ((permOf_eq_one_iff hpr).1 e j hj)
    have hn : idPt n w m (lane nw pm RT ((p - 1) * i)) = false := SB.bNot_t hnid
    rw [hid] at hn
    exact absurd hn (by decide)

private theorem recE_sp {n w m nw pm p nc nt PT RT hi lo X ix : Nat}
    (h : recE n w m nw pm p nc nt PT RT hi lo X ix = true) :
    ∃ c < nc, ∃ t < nt, ∃ a < n, lo < X ∧ X ≤ hi ∧ X >>> nw = 0 ∧
      (∀ i < n, pg w m X (pg w m (lane nw pm PT c) i) =
        pg w m (lane nw pm PT c) (pg w m (lane nw pm RT t) i)) ∧
      (∀ i < a, pg w m X i = i) ∧ pg w m X a ≠ a ∧
      canonW w m X (pg w m X a) (p - 2) (pg w m X a) = true := by
  unfold recE at h
  simp only [SB.sB] at h
  obtain ⟨h1, h⟩ := SB.band h
  obtain ⟨h2, h⟩ := SB.band h
  obtain ⟨h3, h⟩ := SB.band h
  obtain ⟨h4, h⟩ := SB.band h
  obtain ⟨h5, h⟩ := SB.band h
  obtain ⟨h6, h⟩ := SB.band h
  obtain ⟨h7, h⟩ := SB.band h
  obtain ⟨h8, h9⟩ := SB.band h
  obtain ⟨h9, h10⟩ := SB.band h9
  refine ⟨_, SB.bltT h3, _, SB.bltT h4, _, SB.bltT h7, SB.bltT h1, SB.bleT h2, SB.beqT h5,
    SB.eq22_sp h6, fun i hi => SB.beqT (SB.allN_sp h8 i hi), fun e => ?_, h10⟩
  have h9' := SB.bNot_t h9
  rw [e, SB.beq_self] at h9'
  exact absurd h9' (by decide)

theorem recsK_sound {n w m nw pm p nc nt PT RT hi lo : Nat} {L : List (Nat × Nat)}
    (hPT : ∀ c < nc, PermN n w m (lane nw pm PT c)) (hRT : ∀ t < nt, PermN n w m (lane nw pm RT t))
    (h : recsK n w m nw pm p nc nt PT RT hi L lo = true) :
    (L.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ L, lo < e.1 ∧ e.1 ≤ hi ∧ e.1 < 2 ^ nw ∧
      PermN n w m e.1 ∧ CanonGen p (pp n w m e.1) ∧ ∃ c < nc, ∃ t < nt,
        pp n w m e.1 = pp n w m (lane nw pm PT c) * pp n w m (lane nw pm RT t) *
          (pp n w m (lane nw pm PT c))⁻¹ := by
  induction L generalizing lo with
  | nil => exact ⟨List.Pairwise.nil, fun e he => absurd he List.not_mem_nil⟩
  | cons e L ih =>
    obtain ⟨X, ix⟩ := e
    have h' : bAnd(recE n w m nw pm p nc nt PT RT hi lo X ix,
        recsK n w m nw pm p nc nt PT RT hi L X) = true := h
    obtain ⟨h1, h2⟩ := SB.band h'
    obtain ⟨hpw, hall⟩ := ih h2
    obtain ⟨c, hc, t, ht, a, ha, hlo, hhi, hsh, heq, hfix, hmv, hcw⟩ := recE_sp h1
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun b hb => ?_, hpw⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
      exact (hall e he).1
    rw [List.forall_mem_cons]
    refine ⟨?_, fun e he => ?_⟩
    swap
    · obtain ⟨h1', h2'⟩ := hall e he
      exact ⟨by omega, h2'⟩
    have hC := hPT c hc
    have hR := hRT t ht
    have hX : PermN n w m X := by
      refine ⟨fun y hy => ?_, fun y hy y' hy' hyy => ?_⟩
      · obtain ⟨z, hz, rfl⟩ := IsPermN.surj hC hy
        rw [heq z hz]
        exact hC.1 _ (hR.1 z hz)
      · obtain ⟨z, hz, rfl⟩ := IsPermN.surj hC hy
        obtain ⟨z', hz', rfl⟩ := IsPermN.surj hC hy'
        rw [heq z hz, heq z' hz'] at hyy
        rw [hR.2 z hz z' hz' (hC.2 _ (hR.1 z hz) _ (hR.1 z' hz') hyy)]
    refine ⟨hlo, hhi, SB.lt_of_shr hsh, hX, ⟨⟨a, ha⟩, fun b hb => ?_, fun e => ?_,
      fun j hj2 hjp => ?_⟩, c, hc, t, ht, ?_⟩
    · refine Fin.ext ?_
      rw [pp_apply hX]
      exact hfix b hb
    · apply hmv
      have := congrArg Fin.val e
      rwa [pp_apply hX] at this
    · rw [pp_apply hX, pp_eq, permOf_pow hX j, permOf_apply (SB.isPermN_itr' hX j)]
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 + 1 := ⟨j - 2, by omega⟩
      rw [SB.itr_succ']
      exact SB.canonW_sp hcw t (by omega)
    · apply eq_mul_inv_of_mul_eq
      rw [pp_eq, pp_eq, pp_eq, permOf_mul hX hC, permOf_mul hC hR]
      exact permOf_congr heq

private theorem orbE_sp {n w m om ng H OM OD N k : Nat} {L : Nat → Nat}
    (h : orbE n w m om L ng H OM OD N k = true) :
    (k ≠ 0 → lane n om OM (k - 1) < lane n om OM k) ∧
    (SB.odep OD k = 0 → lane n om OM k = H) ∧
    (SB.odep OD k ≠ 0 → ∃ par < N, ∃ g < ng, SB.odep OD par + 1 = SB.odep OD k ∧
      lane n om OM k = img n w m (L (2 * g)) (lane n om OM par)) ∧
    ∀ j < ng, ∃ c < N, lane n om OM c = img n w m (L (2 * j)) (lane n om OM k) := by
  unfold orbE at h
  simp only [SB.sB] at h
  obtain ⟨h1, h2⟩ := SB.band h
  obtain ⟨h2, h3⟩ := SB.band h2
  refine ⟨fun hk => SB.bltT (SB.bIf_f h1 (SB.beq_ne hk)), fun hd => ?_, fun hd => ?_,
    fun j hj => ?_⟩
  · exact SB.beqT (SB.bIf_t h2 (SB.beq_of_eq hd))
  · obtain ⟨hp, h5⟩ := SB.band (SB.bIf_f h2 (SB.beq_ne hd))
    obtain ⟨hl, h6⟩ := SB.band h5
    obtain ⟨hdp, he⟩ := SB.band h6
    exact ⟨_, SB.bltT hp, _, SB.bltT hl, SB.beqT hdp, SB.beqT he⟩
  · obtain ⟨hc, he⟩ := SB.band (SB.allN_sp h3 j hj)
    exact ⟨_, SB.bltT hc, SB.beqT he⟩

theorem orbK_sound {n w m om ng H OM OD N : Nat} {L : Nat → Nat} (hom : om = 2 ^ n - 1) (hN : 0 < N)
    (hL : ∀ j < ng, PermN n w m (L (2 * j))) (h : orbK n w m om L ng H OM OD N = true) :
    (∀ k < N, ∃ g ∈ gen n w m L ng, ⇑g '' mset n H = mset n (lane n om OM k)) ∧
    (∀ g ∈ gen n w m L ng, ∃ k < N, ⇑g '' mset n H = mset n (lane n om OM k)) ∧
    ∀ k < N, ∀ k' < N, k < k' → lane n om OM k < lane n om OM k' := by
  have hE := fun k hk => orbE_sp (SB.allN_sp h k hk)
  have hP : ∀ k < N, ∃ g ∈ gen n w m L ng, ⇑g '' mset n H = mset n (lane n om OM k) := by
    refine SB.depth_ind (dep := SB.odep OD) (fun k hk hd => ⟨1, one_mem _, ?_⟩) (fun k hk hd => ?_)
    · rw [(hE k hk).2.1 hd, Equiv.Perm.coe_one, Set.image_id]
    · obtain ⟨par, hp, g, hg, hdp, he⟩ := (hE k hk).2.2.1 hd
      refine ⟨par, hp, hdp, fun hq => ?_⟩
      obtain ⟨x, hx, ex⟩ := hq
      refine ⟨pp n w m (L (2 * g)) * x, mul_mem (Subgroup.subset_closure ⟨g, hg, rfl⟩) hx, ?_⟩
      rw [he, mset_img _ (hL g hg), ← ex, Equiv.Perm.coe_mul, Set.image_comp]
  have h1 : (1 : Equiv.Perm (Fin n)) ∈
      {g : Equiv.Perm (Fin n) | ∃ k < N, ⇑g '' mset n H = mset n (lane n om OM k)} := by
    obtain ⟨k0, hk0, hd0⟩ := SB.exists_dep0 (dep := SB.odep OD) hN fun k hk hd => by
      obtain ⟨par, hp, -, -, hdp, -⟩ := (hE k hk).2.2.1 hd
      exact ⟨par, hp, hdp⟩
    refine ⟨k0, hk0, ?_⟩
    rw [(hE k0 hk0).2.1 hd0, Equiv.Perm.coe_one, Set.image_id]
  refine ⟨hP, fun g hg => SB.closure_sub h1 ?_ g hg, SB.mono_of_adj fun k hk hk0 => (hE k hk).1 hk0⟩
  rintro x ⟨j, hj, rfl⟩ y ⟨k, hk, ey⟩
  obtain ⟨c, hc, ec⟩ := (hE k hk).2.2.2 j hj
  refine ⟨c, hc, ?_⟩
  rw [ec, mset_img _ (hL j hj), ← ey, Equiv.Perm.coe_mul, Set.image_comp]

@[expose] noncomputable def subLab (OD k : Nat) : Nat := (lane 64 18446744073709551615 OD k / 2 ^ 26) % 4

private theorem subLab_eq (OD k : Nat) :
    fld(lane (nat_lit 64) (nat_lit 18446744073709551615) OD k, nat_lit 26, nat_lit 3) =
      subLab OD k :=
  SB.fld_eq _ 26 2

private theorem subE_sp {n w m om nlab R OM OD N k : Nat} {LM : Nat → Nat}
    (h : subE n w m om LM nlab R OM OD N k = true) :
    subLab OD k < nlab ∧
    (SB.sdep OD k = 0 → (R / 2 ^ (6 * subLab OD k)) % 64 = k) ∧
    (SB.sdep OD k ≠ 0 → ∃ par < N, ∃ g < 3, subLab OD par = subLab OD k ∧
      SB.sdep OD par + 1 = SB.sdep OD k ∧
      lane n om OM k = img n w m (LM (2 * g)) (lane n om OM par)) := by
  unfold subE at h
  simp only [SB.sB, subLab_eq] at h
  obtain ⟨h1, h2⟩ := SB.band h
  refine ⟨SB.bltT h1, fun hd => ?_, fun hd => ?_⟩
  · have e := SB.beqT (SB.bIf_t h2 (SB.beq_of_eq hd))
    exact (SB.fld_eq R (6 * subLab OD k) 6).symm.trans e
  · obtain ⟨hp, h5⟩ := SB.band (SB.bIf_f h2 (SB.beq_ne hd))
    obtain ⟨hl, h6⟩ := SB.band h5
    obtain ⟨hc, h7⟩ := SB.band h6
    obtain ⟨hdp, he⟩ := SB.band h7
    exact ⟨_, SB.bltT hp, _, SB.bltT hl, SB.beqT hc, SB.beqT hdp, SB.beqT he⟩

theorem subK_sound {n w m om nlab R CN H OM OD N : Nat} {LM : Nat → Nat} (hom : om = 2 ^ n - 1)
    (hLM : ∀ j < 3, PermN n w m (LM (2 * j))) (h : subK n w m om LM nlab R CN H OM OD N = true) :
    (∀ j < 3, ⇑(pp n w m (LM (2 * j))) '' mset n H = mset n H) ∧
    (∀ k < N, subLab OD k < nlab ∧ ∃ g ∈ gen n w m LM 3,
      ⇑g '' mset n (lane n om OM ((R / 2 ^ (6 * subLab OD k)) % 64)) = mset n (lane n om OM k)) ∧
    ∀ c < nlab, ((Finset.range N).filter fun k => subLab OD k = c).card = (CN / 2 ^ (8 * c)) % 256 := by
  unfold subK at h
  obtain ⟨h1, h⟩ := SB.band h
  obtain ⟨h2, h3⟩ := SB.band h
  have hE := fun k hk => subE_sp (SB.allN_sp h2 k hk)
  refine ⟨fun j hj => ?_, fun k hk => ⟨(hE k hk).1, ?_⟩, fun c hc => ?_⟩
  · have e := SB.beqT (SB.allN_sp h1 j hj)
    rw [← mset_img _ (hLM j hj)]
    exact congrArg (mset n) e
  · refine SB.depth_ind (N := N) (dep := SB.sdep OD)
      (P := fun k => ∃ g : Equiv.Perm (Fin n), g ∈ gen n w m LM 3 ∧
        ⇑g '' mset n (lane n om OM ((R / 2 ^ (6 * subLab OD k)) % 64)) = mset n (lane n om OM k))
      (fun k hk hd => ⟨1, one_mem _, ?_⟩) (fun k hk hd => ?_) k hk
    · rw [Equiv.Perm.coe_one, Set.image_id, (hE k hk).2.1 hd]
    · obtain ⟨par, hp, g, hg, hl, hdp, he⟩ := (hE k hk).2.2 hd
      refine ⟨par, hp, hdp, fun hq => ?_⟩
      obtain ⟨x, hx, ex⟩ := hq
      refine ⟨pp n w m (LM (2 * g)) * x, mul_mem (Subgroup.subset_closure ⟨g, hg, rfl⟩) hx, ?_⟩
      rw [he, mset_img _ (hLM g hg), ← ex, hl, Equiv.Perm.coe_mul, Set.image_comp]
  · have hc' := SB.beqT (SB.allN_sp h3 c hc)
    rw [SB.cntK_eq] at hc'
    have e2 : (CN / 2 ^ (8 * c)) % 256 = fld(CN, Nat.mul (nat_lit 8) c, nat_lit 255) :=
      (SB.fld_eq CN (8 * c) 8).symm
    rw [e2, ← hc']
    refine congrArg Finset.card (Finset.filter_congr fun k _ => ?_)
    rw [Nat.beq_eq, subLab_eq]

theorem restrK_sound {n w m HP H : Nat} {LM SX : Nat → Nat} (hLM : ∀ j < 3, PermN n w m (LM (2 * j)))
    (h : restrK n w m LM SX HP H = true) :
    (∀ a < 6, pg w m HP a < n) ∧ (∀ a < 6, ∀ b < 6, pg w m HP a = pg w m HP b → a = b) ∧
    (∀ i : Fin n, i ∈ mset n H ↔ ∃ a < 6, pg w m HP a = i) ∧
    ∀ j < 3, ∀ k < 6, ∀ x : Fin n, (x : Nat) = pg w m HP k →
      ((pp n w m (LM (2 * j)) x : Fin n) : Nat) = pg w m HP (pg 3 7 (SX (2 * j)) k) := by
  unfold restrK at h
  obtain ⟨h1, h⟩ := SB.band h
  obtain ⟨h2, h3⟩ := SB.band h
  have hA := fun a ha => SB.band (SB.allN_sp h1 a ha)
  refine ⟨fun a ha => SB.bltT (hA a ha).1, fun a ha b hb e => ?_, fun i => ?_,
    fun j hj k hk x hx => ?_⟩
  · by_contra hab
    have h4 := SB.bNot_t (SB.bIf_f (SB.allN_sp (hA a ha).2 b hb) (SB.beq_ne hab))
    rw [e, SB.beq_self] at h4
    exact absurd h4 (by decide)
  · have hH := SB.beqT h2
    change H.testBit i = true ↔ _
    rw [← hH]
    exact SB.fold_testBit (pg w m HP) 6 i
  · rw [pp_apply (hLM j hj), hx]
    exact SB.beqT (SB.allN_sp (SB.allN_sp h3 j hj) k hk)

private theorem letX_inv {n w m nw pm LP r r' : Nat} (hLP : LettersInv n w m (lane nw pm LP) 2)
    (hr : PermN n w m r) (hr' : PermN n w m r') (e : pp n w m r' = (pp n w m r)⁻¹) :
    LettersInv n w m (letX nw pm LP r r') 3 := by
  intro j hj
  rcases j with _ | _ | _ | j
  · exact hLP 0 (by omega)
  · exact hLP 1 (by omega)
  · exact ⟨hr, hr', e⟩
  · omega

private theorem letX_gens (n w m nw pm LP r r' : Nat) :
    {g | ∃ j < 3, pp n w m (letX nw pm LP r r' (2 * j)) = g} =
      ({pp n w m (lane nw pm LP 0), pp n w m (lane nw pm LP 2), pp n w m r} :
        Set (Equiv.Perm (Fin n))) := by
  ext g
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases j with _ | _ | _ | j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩

theorem rowsK_sound {n w m nw pm p ntg LP RT TG i : Nat} {rows : List (Nat × List Nat)}
    (hLP : LettersInv n w m (lane nw pm LP) 2)
    (hr : ∀ k < rows.length, PermN n w m (lane nw pm RT ((p - 1) * (i + k))) ∧
      PermN n w m (lane nw pm RT ((p - 1) * (i + k) + (p - 2))) ∧
      pp n w m (lane nw pm RT ((p - 1) * (i + k) + (p - 2))) =
        (pp n w m (lane nw pm RT ((p - 1) * (i + k))))⁻¹)
    (h : rowsK n w m nw pm p ntg LP RT TG rows i = true) :
    ∀ k < rows.length, ∃ tg < ntg, PermN n w m (lane nw pm TG tg) ∧
      pp n w m (lane nw pm TG tg) ∈ Subgroup.closure
        {pp n w m (lane nw pm LP 0), pp n w m (lane nw pm LP 2),
          pp n w m (lane nw pm RT ((p - 1) * (i + k)))} := by
  induction rows generalizing i with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons e rows ih =>
    obtain ⟨tg, ws⟩ := e
    have h' : bAnd(Nat.blt tg ntg, bAnd(strictB (Nat.mul (Nat.sub p (nat_lit 1)) i) (fun base =>
        strictB (lane nw pm RT base) (fun r =>
        strictB (lane nw pm RT (Nat.add base (Nat.sub p (nat_lit 2)))) (fun r' =>
          wordK n w m (nat_lit 6) (letX nw pm LP r r') ws (lane nw pm TG tg)))),
        rowsK n w m nw pm p ntg LP RT TG rows (Nat.succ i))) = true := h
    simp only [SB.sB] at h'
    obtain ⟨htg, h2⟩ := SB.band h'
    obtain ⟨hw, hrest⟩ := SB.band h2
    obtain ⟨hr1, hr2, hr3⟩ := hr 0 (by simp)
    rw [Nat.add_zero] at hr1 hr2 hr3
    have hL3 := letX_inv hLP hr1 hr2 hr3
    have hW := wordK_sound (ng := 3) hL3 hw
    intro k hk
    cases k with
    | zero =>
      refine ⟨tg, SB.bltT htg, hW.1, ?_⟩
      have h4 := hW.2
      rw [gen, letX_gens] at h4
      rw [Nat.add_zero]
      exact h4
    | succ k =>
      have hr' : ∀ k < rows.length, PermN n w m (lane nw pm RT ((p - 1) * (i + 1 + k))) ∧
          PermN n w m (lane nw pm RT ((p - 1) * (i + 1 + k) + (p - 2))) ∧
          pp n w m (lane nw pm RT ((p - 1) * (i + 1 + k) + (p - 2))) =
            (pp n w m (lane nw pm RT ((p - 1) * (i + 1 + k))))⁻¹ := fun k hk => by
        have := hr (k + 1) (by simpa using hk)
        have e : i + (k + 1) = i + 1 + k := by omega
        rwa [e] at this
      have := ih (i := i + 1) hr' hrest k (by simpa using hk)
      have e : i + 1 + k = i + (k + 1) := by omega
      rwa [e] at this

end CFSG.KC.L34Syl

end
