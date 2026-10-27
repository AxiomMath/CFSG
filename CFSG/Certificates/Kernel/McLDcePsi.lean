module

public import CFSG.Certificates.Kernel.McLDceGroup
import CFSG.Certificates.Kernel.Co1DceLemmas
import CFSG.Certificates.Kernel.LceSP.Main
import Mathlib.Tactic.Group

namespace CFSG.Certificates.McLD

open CFSG.KC CFSG.KC.McL.Mat CFSG.Certificates.LCE

set_option exponentiation.threshold 700

section Words

variable {G : Type*} [Group G]

@[expose] public noncomputable def wv (gen : ℕ → G) (W n : ℕ) : G :=
  ((List.range n).map fun i => if wLet W i = 255 then 1 else gen (wLet W i)).prod

def ivF (gen : ℕ → G) (c : ℕ) : G := if c = 255 then 1 else gen c

theorem wv_eq (gen : ℕ → G) (W n : ℕ) : wv gen W n = Co1D.bvF (ivF gen) W n := rfl

theorem ivF_255 (gen : ℕ → G) : ivF gen 255 = 1 := by simp [ivF]

theorem ivF_of {gen : ℕ → G} {c : ℕ} (hc : c ≠ 255) : ivF gen c = gen c := by simp [ivF, hc]

theorem map_ivF (gen : ℕ → G) {w : List ℕ} (hw : ∀ c ∈ w, c < 3) :
    w.map (ivF gen) = w.map gen :=
  List.map_congr_left fun c hc => ivF_of (by have := hw c hc; omega)

theorem orB_iff (a b : Bool) : Th.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem anyRec_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) false (fun q acc => Th.orB acc (f q)) n = true →
      ∃ q < n, f q = true
  | 0 => fun h => absurd h Bool.false_ne_true
  | n + 1 => fun h => by
    change Th.orB (Nat.rec (motive := fun _ => Bool) false (fun q acc => Th.orB acc (f q)) n)
      (f n) = true at h
    rcases (orB_iff _ _).1 h with h1 | h1
    · obtain ⟨q, hq, h2⟩ := anyRec_iff f n h1
      exact ⟨q, by omega, h2⟩
    · exact ⟨n, by omega, h1⟩

theorem strip_eq (W n : ℕ) : Th.strip W n = strip W n := rfl

theorem rot_eq (r n s : ℕ) : Th.rot r n s = rot r n s := rfl

theorem freeRed_spec (f : ℕ → G) (hf : f 255 = 1) {LI NL W n : ℕ} (hNL : NL < 256)
    (hx : ∀ c < NL, f c * f c = 1) (hLI : ∀ c < NL, wLet LI c = c)
    (hlet : ∀ i < n, wLet W i < NL ∨ wLet W i = 255) : ∀ i ≤ n, ∃ l : List ℕ,
      Th.freeRed LI W i = Co1D.enc l ∧ (∀ y ∈ l, y < NL) ∧ Co1D.lval f l = Co1D.bvF f W i
  | 0, _ => ⟨[], rfl, by simp, rfl⟩
  | i + 1, hi => by
    obtain ⟨l, hl, hlL, hlv⟩ := freeRed_spec f hf hNL hx hLI hlet i (by omega)
    have e : Th.freeRed LI W (i + 1) = Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (Nat.add (Nat.mul (Th.freeRed LI W i) 256) (Nat.succ (wLet W i)))
        (Nat.shiftRight (Th.freeRed LI W i) 8)
        (Th.andB (Nat.blt 0 (Th.freeRed LI W i))
          (Nat.beq (Nat.land (Th.freeRed LI W i) 255) (Nat.succ (wLet LI (wLet W i))))))
      (Th.freeRed LI W i) (Nat.beq (wLet W i) 255) := rfl
    rw [e, Co1D.brec_eq, Co1D.bvF_succ, ← hlv, hl]
    split_ifs with h255
    · rw [Nat.beq_eq] at h255
      rw [h255, hf, mul_one]
      exact ⟨l, rfl, hlL, rfl⟩
    · rw [Nat.beq_eq] at h255
      have hxL : wLet W i < NL := (hlet i (by omega)).resolve_right h255
      rw [hLI _ hxL, Co1D.brec_eq]
      split_ifs with hcond
      · rw [andB_iff, Nat.blt_eq, Nat.beq_eq] at hcond
        obtain ⟨hpos, htop⟩ := hcond
        rcases l with _ | ⟨y, l'⟩
        · exact absurd hpos (by simp [Co1D.enc])
        · have hy := hlL y (by simp)
          have e1 : Nat.land (Co1D.enc (y :: l')) 255 = y + 1 := by
            change (Co1D.enc l' * 256 + (y + 1)) &&& (2 ^ 8 - 1) = _
            rw [Nat.and_two_pow_sub_one_eq_mod]
            omega
          rw [e1] at htop
          have hyx : y = wLet W i := Nat.succ.inj htop
          refine ⟨l', ?_, fun z hz => hlL z (by simp [hz]), ?_⟩
          · change (Co1D.enc l' * 256 + (y + 1)) >>> 8 = Co1D.enc l'
            rw [Nat.shiftRight_eq_div_pow]
            omega
          · rw [Co1D.lval_cons, hyx, mul_assoc, hx _ hxL, mul_one]
      · refine ⟨wLet W i :: l, rfl, ?_, Co1D.lval_cons f _ _⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hxL
        · exact hlL y hy

theorem chkWord_one (f : ℕ → G) (hf : f 255 = 1) {LI NL W n r m : ℕ} (hNL : NL < 256)
    (hx : ∀ c < NL, f c * f c = 1) (hLI : ∀ c < NL, wLet LI c = c)
    (hlet : ∀ i < n, wLet W i < NL ∨ wLet W i = 255) (hr : r < 256 ^ m)
    (h1 : Co1D.bvF f r m = 1) (h : Th.chkWord LI W n r m = true) : Co1D.bvF f W n = 1 := by
  unfold Th.chkWord at h
  rcases (orB_iff _ _).1 h with h | h
  · obtain ⟨l, hl, -, hv⟩ := freeRed_spec f hf hNL hx hLI hlet n le_rfl
    have h0 : Th.freeRed LI W n = 0 := Nat.eq_of_beq_eq_true h
    rw [← hv]
    rcases l with _ | ⟨y, l'⟩
    · rfl
    · rw [h0] at hl
      simp [Co1D.enc] at hl
  · unfold Th.isRelRot at h
    change Th.andB (Nat.beq (Th.strip W n).2 m) (Th.isRot r m (Th.strip W n).1) = true at h
    rw [andB_iff, Nat.beq_eq, strip_eq] at h
    obtain ⟨hk, hrot⟩ := h
    obtain ⟨s, hs, hseq⟩ := anyRec_iff (fun s => Nat.beq (Th.rot r m s) (strip W n).1) m hrot
    rw [Nat.beq_eq, rot_eq] at hseq
    rw [← (Co1D.strip_spec f hf W n).2, hk, ← hseq]
    exact Co1D.bvF_rot f hr hs h1

theorem wordOK_spec {WD RR : ℕ → ℕ} {LI NL NR WH w : ℕ}
    (h : McL.Dce.wordOK WD RR LI NL NR WH w = true) :
    McL.Dce.byte WH w < NR ∧
      (∀ i < LceS.wLen (WD w), wLet (LceS.wWord (WD w)) i < NL ∨ wLet (LceS.wWord (WD w)) i = 255) ∧
      Th.chkWord LI (LceS.wWord (WD w)) (LceS.wLen (WD w)) (LceS.wWord (RR (McL.Dce.byte WH w)))
        (LceS.wLen (RR (McL.Dce.byte WH w))) = true := by
  unfold McL.Dce.wordOK at h
  beta_reduce at h
  rw [andB_iff, andB_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun i hi => ?_, h3⟩
  have e := (allRec_iff (fun i => Th.orB (Nat.blt (McL.Dce.byte (LceS.wWord (WD w)) i) NL)
    (Nat.beq (McL.Dce.byte (LceS.wWord (WD w)) i) 255)) (LceS.wLen (WD w))).1 h2 i hi
  rw [orB_iff, Nat.blt_eq, Nat.beq_eq] at e
  exact e

variable {gen : ℕ → G} {LT LI TL NL : ℕ}

public theorem tsq_gen {RR : ℕ → ℕ} {NR hT : ℕ} (hTL : TL = 3)
    (htsq : McL.Dce.tsqOK RR TL NR hT = true)
    (hRR : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1) :
    gen TL * gen TL = 1 := by
  subst hTL
  unfold McL.Dce.tsqOK at htsq
  rw [andB_iff, Nat.blt_eq, Nat.beq_eq] at htsq
  have h := hRR hT htsq.1
  have e1 : LceS.wWord (RR hT) = 771 := by
    rw [htsq.2]
    decide +kernel
  have e2 : LceS.wLen (RR hT) = 2 := by
    rw [htsq.2]
    decide +kernel
  have e3 : wLet 771 0 = 3 := by decide +kernel
  have e4 : wLet 771 1 = 3 := by decide +kernel
  have hr : List.range 2 = [0, 1] := rfl
  rw [e1, e2] at h
  simpa [wv, hr, e3, e4] using h

section Model

variable (φ : Mg LT TL NL →* G) (hφ : ∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c)
  (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
include hφ hTL hNL hlet

public theorem gen_invol {RR : ℕ → ℕ} {NR hT : ℕ} (htsq : McL.Dce.tsqOK RR TL NR hT = true)
    (hRR : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1) :
    ∀ c < NL, gen c * gen c = 1 := by
  intro c hc
  by_cases h3 : c < 3
  · exact gen_sq φ hφ hTL hNL hlet h3
  · have e : c = TL := by omega
    rw [e]
    exact tsq_gen hTL htsq hRR

public theorem words_one {WD RR : ℕ → ℕ} {NR WH nW hT : ℕ}
    (htsq : McL.Dce.tsqOK RR TL NR hT = true) (hRRc : relsNorm RR NR = true)
    (hRR : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1)
    (hwords : McL.Dce.wordsOK WD RR LI NL NR WH nW = true) : ∀ w < nW,
      (∀ i < LceS.wLen (WD w),
        wLet (LceS.wWord (WD w)) i < NL ∨ wLet (LceS.wWord (WD w)) i = 255) ∧
      wv gen (LceS.wWord (WD w)) (LceS.wLen (WD w)) = 1 := by
  intro w hw
  have hok := (allRec_iff (fun w => McL.Dce.wordOK WD RR LI NL NR WH w) nW).1 hwords w hw
  obtain ⟨h1, h2, h3⟩ := wordOK_spec hok
  have hx := gen_invol φ hφ hTL hNL hlet htsq hRR
  refine ⟨h2, ?_⟩
  rw [wv_eq]
  refine chkWord_one (ivF gen) (ivF_255 gen) (by omega) (fun c hc => ?_)
    (fun c hc => ((lettersOK_spec hlet).2.2 c hc).1) h2 (LceP.relsNorm_spec hRRc _ h1)
    (hRR _ h1) h3
  rw [ivF_of (by omega)]
  exact hx c hc

end Model

end Words

noncomputable def segL (W o m : ℕ) : List ℕ := (List.range m).map fun k => wLet W (o + k)

theorem segL_succ (W o m : ℕ) : segL W o (m + 1) = segL W o m ++ [wLet W (o + m)] := by
  simp [segL, List.range_succ]

theorem wc_single (LT c : ℕ) : wc LT [c] = McL.Dce.let25 LT c := by
  rw [wc, List.foldl_cons, List.foldl_nil]
  exact ident_mul25 (let25_lt LT c)

theorem segProd_spec (LT TL NL W o : ℕ) : ∀ m, McL.Dce.segProd LT TL NL W o m = 0 ∨
    ((∀ k < m, McL.Dce.isN TL NL (wLet W (o + k)) = true) ∧
      McL.Dce.segProd LT TL NL W o m = wc LT (segL W o m))
  | 0 => Or.inr ⟨fun k hk => absurd hk (Nat.not_lt_zero k), rfl⟩
  | m + 1 => by
    have e : McL.Dce.segProd LT TL NL W o (m + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (mul25 (McL.Dce.segProd LT TL NL W o m) (McL.Dce.let25 LT (wLet W (o + m))))
        (McL.Dce.isN TL NL (wLet W (o + m))) := rfl
    rw [e]
    rcases segProd_spec LT TL NL W o m with h | ⟨h1, h2⟩
    · left
      rw [h, mul25_zero_left]
      cases McL.Dce.isN TL NL (wLet W (o + m)) <;> rfl
    · cases hk : McL.Dce.isN TL NL (wLet W (o + m))
      · exact Or.inl rfl
      · refine Or.inr ⟨fun k hk' => ?_, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h | rfl
          · exact h1 k h
          · exact hk
        · change mul25 (McL.Dce.segProd LT TL NL W o m) (McL.Dce.let25 LT (wLet W (o + m))) = _
          rw [h2, segL_succ, wc_append, wc_single]

theorem seg_lt3 {TL NL W o m : ℕ} (hTL : TL = 3) (hNL : NL = 4)
    (h : ∀ k < m, McL.Dce.isN TL NL (wLet W (o + k)) = true) : ∀ c ∈ segL W o m, c < 3 := by
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
  have := isN_iff.1 (h k (List.mem_range.1 hk))
  omega

theorem mul25_zero_right (B : ℕ) : mul25 B 0 = 0 :=
  eq_of_toMat_eq (mul25_lt _ _) (Nat.two_pow_pos _) (by rw [toMat_mul25, toMat_zero, mul_zero])

theorem InM_ne_zero {LT TL NL A : ℕ} (h : InM LT TL NL A) : A ≠ 0 := by
  rintro rfl
  obtain ⟨y, -, hy⟩ := h
  have e := y.mul_inv
  rw [hy, toMat_zero, zero_mul] at e
  apply ident_ne_zero
  exact eq_of_toMat_eq ident_lt (Nat.two_pow_pos _) (by rw [toMat_ident, toMat_zero, e])

theorem bvF_split {G : Type*} [Group G] (f : ℕ → G) (W a b : ℕ) :
    Co1D.bvF f W (a + b) = Co1D.bvF f W a * ((segL W a b).map f).prod := by
  unfold Co1D.bvF segL
  rw [List.range_add, List.map_append, List.prod_append, List.map_map, List.map_map]
  rfl

theorem bvF_one' {G : Type*} [Group G] (f : ℕ → G) (W : ℕ) : Co1D.bvF f W 1 = f (wLet W 0) := by
  simp [Co1D.bvF]

@[expose] public noncomputable def tPsi (HB TB : ℕ → ℕ) (e : ℕ) : ℕ :=
  McL.Dce.mat HB (McL.Dce.hi20 (McL.Dce.e40 TB e))

theorem tOK_spec {HB TB OB RR : ℕ → ℕ} {LT TL NL NR nH nT I0 e d : ℕ}
    (h : McL.Dce.tOK HB TB OB RR LT TL NL NR nH nT I0 e d = true) :
    McL.Dce.lo20 (McL.Dce.e40 TB e) < nH ∧ McL.Dce.hi20 (McL.Dce.e40 TB e) < nH ∧
      McL.Dce.bits d 42 17 < nT ∧ tPsi HB TB e = McL.Dce.tSig HB TB (McL.Dce.bits d 42 17) ∧
      vecmul (McL.Dce.pt OB I0) (McL.Dce.tSig HB TB e) = McL.Dce.pt OB I0 ∧
      ((∃ a b, a < e ∧ b < e ∧
          McL.Dce.tSig HB TB e = mul25 (McL.Dce.tSig HB TB a) (McL.Dce.tSig HB TB b) ∧
          tPsi HB TB e = mul25 (tPsi HB TB a) (tPsi HB TB b)) ∨
        ∃ r s ns, McL.Dce.relVisOK RR LT TL NL NR (McL.Dce.tSig HB TB e) (tPsi HB TB e) r s ns =
          true) := by
  unfold McL.Dce.tOK at h
  beta_reduce at h
  rw [andB_iff, andB_iff, andB_iff, andB_iff, andB_iff, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq,
    Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  revert h6
  generalize McL.Dce.bits d 2 40 = p
  generalize Nat.land d 3 = k
  cases Nat.beq k 0
  · cases Nat.beq k 1
    · intro h
      exact absurd h Bool.false_ne_true
    · intro h
      exact Or.inr ⟨McL.Dce.bits p 0 8, McL.Dce.bits p 8 10, McL.Dce.bits p 18 10, h⟩
  · intro h
    change Th.andB (Nat.blt (McL.Dce.bits p 0 17) e) (Th.andB (Nat.blt (McL.Dce.bits p 17 17) e)
      (Th.andB (Nat.beq (McL.Dce.tSig HB TB e) (mul25 (McL.Dce.tSig HB TB (McL.Dce.bits p 0 17))
        (McL.Dce.tSig HB TB (McL.Dce.bits p 17 17))))
        (Nat.beq (tPsi HB TB e) (mul25 (tPsi HB TB (McL.Dce.bits p 0 17))
          (tPsi HB TB (McL.Dce.bits p 17 17)))))) = true at h
    rw [andB_iff, andB_iff, andB_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq, Nat.beq_eq] at h
    exact Or.inl ⟨_, _, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

@[expose] public noncomputable def mE (LT TL NL A : ℕ) : Mg LT TL NL :=
  @dite _ (InM LT TL NL A) (Classical.propDecidable _)
    (fun h => ⟨Classical.choose h, (Classical.choose_spec h).1⟩) (fun _ => 1)

public theorem mE_val {LT TL NL A : ℕ} (h : InM LT TL NL A) :
    (((mE LT TL NL A : Mg LT TL NL) : Mat25ˣ) : Mat25) = toMat A := by
  unfold mE
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).2

@[expose] public noncomputable def sigE (LT TL NL : ℕ) (HB TB : ℕ → ℕ) (e : ℕ) : Mg LT TL NL :=
  mE LT TL NL (McL.Dce.tSig HB TB e)

section Psi

variable {G : Type*} [Group G] {gen : ℕ → G} {LT LI TL NL : ℕ}

public theorem tOK_stab {HB TB OB RR : ℕ → ℕ} {NR nH nT I0 : ℕ} {Ct : List ℕ}
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true) :
    ∀ e < nT, vecmul (McL.Dce.pt OB I0) (McL.Dce.tSig HB TB e) = McL.Dce.pt OB I0 := by
  intro e he
  obtain ⟨d, hd⟩ := runT_ok hpsi e he
  exact (tOK_spec hd).2.2.2.2.1

public theorem psi_mem (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {HB TB OB RR : ℕ → ℕ} {NR nH nT I0 : ℕ} {Ch Ct : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true) :
    ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) ∧
      ∃ e' < nT, tPsi HB TB e = McL.Dce.tSig HB TB e' := by
  intro e he
  obtain ⟨d, hd⟩ := runT_ok hpsi e he
  obtain ⟨h1, h2, h3, h4, -⟩ := tOK_spec hd
  have hH := hdr_mem hTL hNL hlet hhdr
  exact ⟨hH _ h1, hH _ h2, _, h3, h4⟩

public theorem stab_hyp (hTL : TL = 3) (hNL : NL = 4)
    (hlet : McL.Dce.lettersOK LT LI TL NL = true) {HB TB OB RR : ℕ → ℕ} {NR nH nT I0 : ℕ}
    {Ch Ct : List ℕ} (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true) :
    ∀ e < nT, actV (toVec (McL.Dce.pt OB I0)) ((sigE LT TL NL HB TB e : Mg LT TL NL) : Mat25ˣ) =
      toVec (McL.Dce.pt OB I0) := by
  intro e he
  unfold sigE
  rw [← toVec_vecmul_actV (mE_val (psi_mem hTL hNL hlet hhdr hpsi e he).1),
    tOK_stab hpsi e he]

theorem conj_mul (t x y : G) (ht : t * t = 1) : t * (x * y) * t = t * x * t * (t * y * t) := by
  calc t * (x * y) * t = t * x * (t * t) * y * t := by rw [ht]; group
    _ = t * x * t * (t * y * t) := by group

section Model

variable (φ : Mg LT TL NL →* G) (hφ : ∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c)
  (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
include hφ hTL hNL hlet

theorem relVis_rc {RR : ℕ → ℕ} {NR S P r s ns : ℕ} (hRRc : relsNorm RR NR = true)
    (hRR : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1)
    (hS : InM LT TL NL S) (h : McL.Dce.relVisOK RR LT TL NL NR S P r s ns = true) :
    gen TL * rc φ S * gen TL = rc φ P := by
  unfold McL.Dce.relVisOK at h
  beta_reduce at h
  change Th.andB (Nat.blt r NR) (Th.andB (Nat.blt s (LceS.wLen (RR r)))
    (Th.andB (Nat.ble (ns + 2) (LceS.wLen (RR r)))
    (Th.andB (Nat.beq (wLet (Th.rot (LceS.wWord (RR r)) (LceS.wLen (RR r)) s) 0) TL)
    (Th.andB (Nat.beq (wLet (Th.rot (LceS.wWord (RR r)) (LceS.wLen (RR r)) s) (ns + 1)) TL)
    (Th.andB (Nat.beq S (McL.Dce.segProd LT TL NL
      (Th.rot (LceS.wWord (RR r)) (LceS.wLen (RR r)) s) 1 ns))
    (Nat.beq (mul25 P (McL.Dce.segProd LT TL NL (Th.rot (LceS.wWord (RR r)) (LceS.wLen (RR r)) s)
      (ns + 2) (LceS.wLen (RR r) - (ns + 2)))) ident)))))) = true at h
  have hv : Co1D.bvF (ivF gen) (Th.rot (LceS.wWord (RR r)) (LceS.wLen (RR r)) s)
      (LceS.wLen (RR r)) = 1 := by
    rw [andB_iff, Nat.blt_eq, andB_iff, Nat.blt_eq] at h
    rw [rot_eq]
    exact Co1D.bvF_rot _ (LceP.relsNorm_spec hRRc r h.1) h.2.1 (hRR r h.1)
  rw [andB_iff, andB_iff, andB_iff, andB_iff, andB_iff, andB_iff, Nat.blt_eq, Nat.blt_eq,
    Nat.ble_eq, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨-, hs, hns, hb0, hb1, hSe, hPe⟩ := h
  generalize Th.rot (LceS.wWord (RR r)) (LceS.wLen (RR r)) s = Wd at hv hb0 hb1 hSe hPe
  generalize LceS.wLen (RR r) = n at hv hs hns hPe
  rcases segProd_spec LT TL NL Wd 1 ns with h0 | ⟨hall1, hS1⟩
  · exact absurd (hSe.trans h0) (InM_ne_zero hS)
  rcases segProd_spec LT TL NL Wd (ns + 2) (n - (ns + 2)) with h0 | ⟨hall2, hS2⟩
  · rw [h0, mul25_zero_right] at hPe
    exact absurd hPe.symm ident_ne_zero
  have hw1 := seg_lt3 hTL hNL hall1
  have hw2 := seg_lt3 hTL hNL hall2
  rw [hS2] at hPe
  rw [hSe, hS1, rc_wc φ hφ hTL hNL hlet hw1, rc_invL φ (InM_wc hTL hNL hlet hw2) hPe,
    rc_wc φ hφ hTL hNL hlet hw2]
  have hn : n = (ns + 2) + (n - (ns + 2)) := by omega
  have e3 : Co1D.bvF (ivF gen) Wd (ns + 2) =
      Co1D.bvF (ivF gen) Wd (1 + ns) * ivF gen (wLet Wd (ns + 1)) := by
    rw [Nat.add_comm 1 ns]
    exact Co1D.bvF_succ _ _ _
  rw [hn, bvF_split, e3, bvF_split, bvF_one', hb0, hb1, ivF_of (by omega), map_ivF gen hw1,
    map_ivF gen hw2] at hv
  exact eq_inv_of_mul_eq_one_left hv

public theorem psi_rc {HB TB OB RR : ℕ → ℕ} {NR nH nT I0 hT : ℕ} {Ch Ct : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true)
    (htsq : McL.Dce.tsqOK RR TL NR hT = true) (hRRc : relsNorm RR NR = true)
    (hRR : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1) :
    ∀ e < nT, gen TL * rc φ (McL.Dce.tSig HB TB e) * gen TL = rc φ (tPsi HB TB e) := by
  have hmem := psi_mem hTL hNL hlet hhdr hpsi
  have ht := tsq_gen hTL htsq hRR
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    obtain ⟨d, hd⟩ := runT_ok hpsi e he
    obtain ⟨-, -, -, -, -, hk⟩ := tOK_spec hd
    rcases hk with ⟨a, b, ha, hb, hS, hP⟩ | ⟨r, s, ns, hrv⟩
    · have ma := hmem a (by omega)
      have mb := hmem b (by omega)
      rw [hS, hP, rc_mul φ ma.1 mb.1, rc_mul φ ma.2.1 mb.2.1, conj_mul _ _ _ ht,
        ih a ha (by omega), ih b hb (by omega)]
    · exact relVis_rc φ hφ hTL hNL hlet hRRc hRR (hmem e he).1 hrv

omit hφ hTL hNL hlet in
public theorem rc_mE {A : ℕ} (h : InM LT TL NL A) : rc φ A = φ (mE LT TL NL A) :=
  rc_eq φ _ (mE_val h)

public theorem psi_hyp {HB TB OB RR : ℕ → ℕ} {NR nH nT I0 hT : ℕ} {Ch Ct : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true)
    (htsq : McL.Dce.tsqOK RR TL NR hT = true) (hRRc : relsNorm RR NR = true)
    (hRR : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1) :
    ∀ e < nT, ∃ e' < nT,
      (gen TL)⁻¹ * φ (sigE LT TL NL HB TB e) * gen TL = φ (sigE LT TL NL HB TB e') := by
  intro e he
  obtain ⟨m1, m2, e', he', hpe⟩ := psi_mem hTL hNL hlet hhdr hpsi e he
  refine ⟨e', he', ?_⟩
  have hinv : (gen TL)⁻¹ = gen TL := inv_eq_of_mul_eq_one_right (tsq_gen hTL htsq hRR)
  unfold sigE
  rw [hinv, ← rc_mE φ m1, psi_rc φ hφ hTL hNL hlet hhdr hpsi htsq hRRc hRR e he, hpe]
  rw [hpe] at m2
  exact rc_mE φ m2

omit hφ hNL hlet in
public theorem usq_hyp {RR : ℕ → ℕ} {NR hT : ℕ} (htsq : McL.Dce.tsqOK RR TL NR hT = true)
    (hRR : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1) :
    ∃ m, gen TL * gen TL = φ m :=
  ⟨1, by rw [tsq_gen hTL htsq hRR, map_one]⟩

end Model

public theorem gens_hX (hTL : TL = 3) (hNL : NL = 4) :
    ∀ x ∈ gen '' {c | c < NL}, x ∈ Nsub gen ∨ x = gen TL ∨ x = (gen TL)⁻¹ := by
  rintro _ ⟨c, hc, rfl⟩
  by_cases h3 : c < 3
  · exact Or.inl (Subgroup.subset_closure ⟨c, h3, rfl⟩)
  · have hc' : c < NL := hc
    have e : c = TL := by omega
    exact Or.inr (Or.inl (by rw [e]))

end Psi

end CFSG.Certificates.McLD
