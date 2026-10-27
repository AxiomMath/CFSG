module

public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.McL.RangeX
import CFSG.Certificates.Kernel.McLFreeSound
import CFSG.Certificates.Kernel.LceSP.Main
import CFSG.Certificates.Kernel.HOrbSound
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.McLS

open CFSG.KC CFSG.Certificates.LCE

@[expose] noncomputable def pval {G : Type*} [Group G] (gen : ℕ → G) (v : ℕ) : G :=
  bval gen (McL.Sub.pw v) (McL.Sub.pn v)

@[expose] noncomputable def fval {G : Type*} [Group G] (gen : ℕ → G) (F : ℕ → ℕ) (W n : ℕ) : G :=
  ((List.range n).map fun i => pval gen (F (wLet W i))).prod

@[expose] def smallTab (F : ℕ → ℕ) : Prop :=
  ∀ c < 256, McL.Sub.pn (F c) < 16 ∧ McL.Sub.pw (F c) < 2 ^ (8 * McL.Sub.pn (F c))

private theorem tabF {F : ℕ → ℕ} (hF : smallTab F) :
    ∀ c < 256, McL.Sub.pn (F c) < 16 ∧ McL.Sub.pw (F c) < 256 ^ McL.Sub.pn (F c) :=
  fun c hc => ⟨(hF c hc).1, by rw [← LceP.two_pow_eight_mul]; exact (hF c hc).2⟩

private theorem subst_ent {G : Type*} [Group G] (gen : ℕ → G) {F : ℕ → ℕ} (hF : smallTab F)
    (e : ℕ) : McLFree.pV gen (McL.Sub.subst F (McL.Sub.ofEnt e)) =
      fval gen F (LceS.wWord e) (LceS.wLen e) := by
  obtain ⟨o1, o2⟩ := McLFree.ofEnt_spec e
  have hl := McLFree.wLen_lt e
  obtain ⟨-, -, -, u4⟩ := McLFree.subst_spec gen (b := 256) (tabF hF)
    (fun _ _ _ _ => LceP.wLet_lt _ _) (v := McL.Sub.ofEnt e) (by omega)
  rw [u4, o1, o2]
  rfl

private def BindP {G : Type*} [Group G] (gen : ℕ → G) (F REL TW TL : ℕ → ℕ)
    (NR nT L1 L2 S : ℕ) : Prop :=
  ∀ r, S / 2 ^ (r + 1) % 2 = 1 → r < NR ∧ ∃ k < nT, (TL k = L1 ∨ TL k = L2) ∧
    fval gen F (LceS.wWord (REL r)) (LceS.wLen (REL r)) =
      bval gen (LceS.wWord (TW k)) (LceS.wLen (TW k))

private theorem bind_step (F REL TW TL : ℕ → ℕ) (NR nT L1 L2 m J S : ℕ) :
    McL.Sub.bindRun F REL TW TL NR nT L1 L2 (m + 1) J S =
      McL.Sub.bindRun F REL TW TL NR nT L1 L2 m (Nat.shiftRight J 24)
        (Bool.rec (motive := fun _ => ℕ) 0 (Nat.lor S (Nat.shiftLeft 2 (Nat.land J 255)))
          (andB (Nat.blt 0 S) (andB (Nat.blt (Nat.land J 255) NR)
            (andB (Nat.blt (Nat.land (Nat.shiftRight J 8) 65535) nT)
              (andB (orB (Nat.beq (TL (Nat.land (Nat.shiftRight J 8) 65535)) L1)
                  (Nat.beq (TL (Nat.land (Nat.shiftRight J 8) 65535)) L2))
                (McL.Sub.redEq (McL.Sub.subst F (McL.Sub.ofEnt (REL (Nat.land J 255))))
                  (McL.Sub.ofEnt (TW (Nat.land (Nat.shiftRight J 8) 65535))))))))) := rfl

theorem bindRun_sound {G : Type*} [Group G] (gen : ℕ → G) {F REL TW TL : ℕ → ℕ}
    {NR nT L1 L2 m J S : ℕ} (hF : smallTab F)
    (h : Nat.beq (McL.Sub.bindRun F REL TW TL NR nT L1 L2 m J (nat_lit 1)) S = true) :
    ∀ r, S / 2 ^ (r + 1) % 2 = 1 → r < NR ∧ ∃ k < nT, (TL k = L1 ∨ TL k = L2) ∧
      fval gen F (LceS.wWord (REL r)) (LceS.wLen (REL r)) =
        bval gen (LceS.wWord (TW k)) (LceS.wLen (TW k)) := by
  have step : ∀ m' J' S', BindP gen F REL TW TL NR nT L1 L2 S' →
      BindP gen F REL TW TL NR nT L1 L2 (McL.Sub.bindRun F REL TW TL NR nT L1 L2 m' J' S') := by
    intro m'
    induction m' with
    | zero => exact fun _ _ hS => hS
    | succ m ih =>
      intro J' S' hS
      rw [bind_step]
      apply ih
      generalize Nat.land J' 255 = r0
      generalize Nat.land (Nat.shiftRight J' 8) 65535 = k0
      rw [LceP.brec_eq]
      split_ifs with hc
      · simp only [LceP.andB_iff, LceP.orB_iff, Nat.blt_eq, Nat.beq_eq] at hc
        obtain ⟨-, hr0, hk0, hL, hred⟩ := hc
        intro r hr
        have hbit : (S' ||| 2 <<< r0).testBit (r + 1) = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq]
          exact decide_eq_true hr
        rw [Nat.testBit_or, Nat.shiftLeft_eq, ← pow_succ', Nat.testBit_two_pow,
          Bool.or_eq_true] at hbit
        rcases hbit with h1 | h1
        · rw [Nat.testBit_eq_decide_div_mod_eq] at h1
          exact hS r (of_decide_eq_true h1)
        · have hr : r = r0 := by
            have := of_decide_eq_true h1
            omega
          subst hr
          refine ⟨hr0, k0, hk0, hL, ?_⟩
          rw [← subst_ent gen hF, McLFree.redEq_val gen hred, McLFree.ofEnt_val]
      · intro r hr
        rw [Nat.zero_div, Nat.zero_mod] at hr
        exact absurd hr (by norm_num)
  have h0 : BindP gen F REL TW TL NR nT L1 L2 1 := by
    intro r hr
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le (by norm_num) (Nat.le_self_pow (by omega) 2)),
      Nat.zero_mod] at hr
    exact absurd hr (by norm_num)
  rw [← Nat.eq_of_beq_eq_true h]
  exact step m J 1 h0

theorem conjSubst_sound {G : Type*} [Group G] (gen : ℕ → G) {F RT : ℕ → ℕ} {R r ul E : ℕ}
    (hF : smallTab F)
    (hRT : ∀ r < R, LceS.wWord (RT r) < 2 ^ (8 * LceS.wLen (RT r)) ∧
      bval gen (LceS.wWord (RT r)) (LceS.wLen (RT r)) = 1)
    (h : McL.Sub.conjRelOK RT R r ul (McL.Sub.subst F (McL.Sub.ofEnt E)) = true) :
    fval gen F (LceS.wWord E) (LceS.wLen E) = 1 := by
  rw [← subst_ent gen hF]
  exact McLFree.conjRelOK_one gen hRT h

private theorem xtLt_spec {F : ℕ → ℕ} (h : McL.RangeX.xtLt F = true) :
    ∀ c < 256, ∀ i < McL.Sub.pn (F c), wLet (McL.Sub.pw (F c)) i < 254 := by
  intro c hc i hi
  have h1 := (LceP.allRec_iff (fun c => Nat.rec (motive := fun _ => Bool) true
    (fun i acc2 => andB acc2 (Nat.blt (wLet (McL.Sub.pw (F c)) i) (nat_lit 254)))
      (McL.Sub.pn (F c))) (nat_lit 256)).1 h c hc
  have h2 := (LceP.allRec_iff (fun i => Nat.blt (wLet (McL.Sub.pw (F c)) i) (nat_lit 254))
    (McL.Sub.pn (F c))).1 h1 i hi
  rwa [Nat.blt_eq] at h2

theorem subsOK_sound {G : Type*} [Group G] (gen : ℕ → G)
    {XT MG ST SL SN SH TWm TLm : ℕ → ℕ} {d nTm Lm K : ℕ} (hF : smallTab XT)
    (hXL : CFSG.KC.McL.RangeX.xtLt XT = true) (hSTc : relsNorm ST K = true)
    (hT : ∀ k < nTm, TLm k = Lm → bval gen (LceS.wWord (TWm k)) (LceS.wLen (TWm k)) = 1)
    (h : McL.Sub.subsOK XT MG ST SL SN SH TWm TLm d nTm Lm K = true) :
    ∀ j < K, SL j = McL.evalW MG d (LceS.wWord (SN j)) (LceS.wLen (SN j)) ∧
      bval gen (LceS.wWord (ST j)) (LceS.wLen (ST j)) =
        fval gen XT (LceS.wWord (SN j)) (LceS.wLen (SN j)) := by
  have hxl := xtLt_spec hXL
  have hn := LceP.relsNorm_spec hSTc
  intro j hj
  have hs := (LceP.allRec_iff _ K).1 h j hj
  unfold McL.Sub.subOK at hs
  rw [LceP.andB_iff] at hs
  obtain ⟨h1, h2⟩ := hs
  refine ⟨Nat.eq_of_beq_eq_true h1, ?_⟩
  obtain ⟨o1, o2⟩ := McLFree.ofEnt_spec (SN j)
  have hl := McLFree.wLen_lt (SN j)
  obtain ⟨u1, u2, u3, u4⟩ := McLFree.subst_spec gen (b := 254) (tabF hF) hxl
    (v := McL.Sub.ofEnt (SN j)) (by omega)
  have hsub : McLFree.pV gen (McL.Sub.subst XT (McL.Sub.ofEnt (SN j))) =
      fval gen XT (LceS.wWord (SN j)) (LceS.wLen (SN j)) := by
    rw [u4, o1, o2]
    rfl
  rw [← McLFree.ofEnt_val gen (ST j), ← hsub]
  rw [LceP.brec_eq] at h2
  split_ifs at h2 with hSH
  · exact McLFree.redEq_val gen h2
  · rw [LceP.brec_eq] at h2
    split_ifs at h2 with hodd
    · dsimp only at h2
      rw [LceP.andB_iff, LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at h2
      obtain ⟨hk, hL, hred⟩ := h2
      have hv := McLFree.redEq_val gen hred
      rw [McLFree.ofEnt_val gen, hT _ hk hL] at hv
      obtain ⟨p1, p2, -⟩ := McLFree.pinvW_spec (McL.Sub.subst XT (McL.Sub.ofEnt (SN j)))
      obtain ⟨e1, e2⟩ := McLFree.ofEnt_spec (ST j)
      have hl2 := McLFree.wLen_lt (ST j)
      have hcl : McL.Sub.pw (McL.Sub.ofEnt (ST j)) < 256 ^ McL.Sub.pn (McL.Sub.ofEnt (ST j)) := by
        rw [e1, e2]
        exact hn j hj
      obtain ⟨-, -, c3⟩ := McLFree.cat_spec gen hcl (by rw [p1]; exact p2) (by rw [e1, p1]; omega)
      rw [c3, McLFree.pinvW_val gen u3] at hv
      exact mul_inv_eq_one.1 hv

private theorem subst_inv {G : Type*} [Group G] (gen : ℕ → G) {XT : ℕ → ℕ} (hF : smallTab XT)
    (hXinv : ∀ c < 8, pval gen (XT (c ^^^ 1)) = (pval gen (XT c))⁻¹) {e : ℕ}
    (he : ∀ j < LceS.wLen e, wLet (LceS.wWord e) j < 6) :
    McLFree.pV gen (McL.Sub.subst XT (McL.Sub.pinvW (McL.Sub.ofEnt e))) =
      (fval gen XT (LceS.wWord e) (LceS.wLen e))⁻¹ := by
  obtain ⟨o1, o2⟩ := McLFree.ofEnt_spec e
  obtain ⟨p1, -, p3⟩ := McLFree.pinvW_spec (McL.Sub.ofEnt e)
  rw [o1, o2] at p3
  rw [o1] at p1
  have hl := McLFree.wLen_lt e
  obtain ⟨-, -, -, u4⟩ := McLFree.subst_spec gen (b := 256) (tabF hF)
    (fun _ _ _ _ => LceP.wLet_lt _ _) (v := McL.Sub.pinvW (McL.Sub.ofEnt e)) (by omega)
  rw [u4, p1]
  unfold fval
  rw [List.prod_inv_reverse, List.map_map, ← HO.map_range_rev]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [p3 k hk']
  exact hXinv _ (by have := he (LceS.wLen e - 1 - k) (by omega); omega)

private theorem k1_ident {G : Type*} [Group G] (gen : ℕ → G) (ψ : ℕ → G) (I : Set ℕ)
    {XT MG TW TL : ℕ → ℕ} {d sE qE k : ℕ} (hF : smallTab XT)
    (hXinv : ∀ c < 8, pval gen (XT (c ^^^ 1)) = (pval gen (XT c))⁻¹)
    (hmul : ∀ p ∈ I, ∀ q ∈ I, McL.pmul d p q ∈ I ∧ ψ (McL.pmul d p q) = ψ p * ψ q)
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW MG d W n ∈ I ∧ ψ (McL.evalW MG d W n) = fval gen XT W n)
    (hTk : TL k ∈ I ∧ bval gen (LceS.wWord (TW k)) (LceS.wLen (TW k)) = ψ (TL k))
    (hs : ∀ j < LceS.wLen sE, wLet (LceS.wWord sE) j < 6)
    (hq : ∀ j < LceS.wLen qE, wLet (LceS.wWord qE) j < 6)
    (hred : McL.Sub.redEq (McL.Sub.cat (McL.Sub.cat (McL.Sub.cat (XT 6)
        (McL.Sub.subst XT (McL.Sub.ofEnt sE))) (XT 6))
        (McL.Sub.subst XT (McL.Sub.pinvW (McL.Sub.ofEnt qE)))) (McL.Sub.ofEnt (TW k)) = true) :
    McL.evalW MG d (McL.Sub.pw (McL.Sub.ofEnt sE)) (McL.Sub.pn (McL.Sub.ofEnt sE)) ∈ I ∧
      McL.pmul d (TL k) (McL.evalW MG d (McL.Sub.pw (McL.Sub.ofEnt qE))
        (McL.Sub.pn (McL.Sub.ofEnt qE))) ∈ I ∧
      pval gen (XT 6) *
          ψ (McL.evalW MG d (McL.Sub.pw (McL.Sub.ofEnt sE)) (McL.Sub.pn (McL.Sub.ofEnt sE))) *
          pval gen (XT 6) =
        ψ (McL.pmul d (TL k) (McL.evalW MG d (McL.Sub.pw (McL.Sub.ofEnt qE))
          (McL.Sub.pn (McL.Sub.ofEnt qE)))) := by
  obtain ⟨o1, o2⟩ := McLFree.ofEnt_spec sE
  obtain ⟨q1, q2⟩ := McLFree.ofEnt_spec qE
  have ls := McLFree.wLen_lt sE
  have lq := McLFree.wLen_lt qE
  obtain ⟨t1, t2⟩ := tabF hF 6 (by norm_num)
  obtain ⟨a1, a2, -, -⟩ := McLFree.subst_spec gen (b := 256) (tabF hF)
    (fun _ _ _ _ => LceP.wLet_lt _ _) (v := McL.Sub.ofEnt sE) (by omega)
  obtain ⟨p1, -, -⟩ := McLFree.pinvW_spec (McL.Sub.ofEnt qE)
  obtain ⟨b1, b2, -, -⟩ := McLFree.subst_spec gen (b := 256) (tabF hF)
    (fun _ _ _ _ => LceP.wLet_lt _ _) (v := McL.Sub.pinvW (McL.Sub.ofEnt qE)) (by omega)
  obtain ⟨c1, c2, c3⟩ := McLFree.cat_spec gen t2 a2 (by omega)
  obtain ⟨d1, d2, d3⟩ := McLFree.cat_spec gen c2 t2 (by omega)
  obtain ⟨-, -, e3⟩ := McLFree.cat_spec gen d2 b2 (by omega)
  have hv := McLFree.redEq_val gen hred
  rw [e3, d3, c3, subst_ent gen hF sE, subst_inv gen hF hXinv hq, McLFree.ofEnt_val,
    hTk.2] at hv
  obtain ⟨msI, msv⟩ := hW _ _ hs
  obtain ⟨mqI, mqv⟩ := hW _ _ hq
  obtain ⟨pI, pv⟩ := hmul _ hTk.1 _ mqI
  rw [o1, o2, q1, q2]
  refine ⟨msI, pI, ?_⟩
  rw [msv, pv, mqv]
  exact mul_inv_eq_iff_eq_mul.1 hv

private theorem k1_sign {G : Type*} [Group G] (ψ : ℕ → G) (I : Set ℕ) {d : ℕ} {t : G}
    (ht : t * t = 1) (hinv : ∀ p ∈ I, McL.Sub.pinv d p ∈ I ∧ ψ (McL.Sub.pinv d p) = (ψ p)⁻¹)
    {a c : ℕ} (ha : a ∈ I) (hc : c ∈ I) (h : t * ψ a * t = ψ c) (sg : Bool) :
    Bool.rec (motive := fun _ => ℕ) a (McL.Sub.pinv d a) sg ∈ I ∧
      Bool.rec (motive := fun _ => ℕ) c (McL.Sub.pinv d c) sg ∈ I ∧
      t * ψ (Bool.rec (motive := fun _ => ℕ) a (McL.Sub.pinv d a) sg) * t =
        ψ (Bool.rec (motive := fun _ => ℕ) c (McL.Sub.pinv d c) sg) := by
  cases sg
  · exact ⟨ha, hc, h⟩
  · obtain ⟨a1, a2⟩ := hinv a ha
    obtain ⟨c1, c2⟩ := hinv c hc
    refine ⟨a1, c1, ?_⟩
    change t * ψ (McL.Sub.pinv d a) * t = ψ (McL.Sub.pinv d c)
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [a2, c2, ← h]
    simp only [mul_inv_rev, hti, mul_assoc]

private theorem k1_combine {G : Type*} [Group G] {t x y s r : G} (ht : t * t = 1)
    (h1 : t * x * t = y) (h2 : t * s * t = r) : t * (x * s) * t = y * r := by
  rw [← h1, ← h2]
  simp only [mul_assoc]
  rw [← mul_assoc t t, ht, one_mul]

private theorem pget_lt' (p i : ℕ) : McL.pget p i < 64 := by
  change Nat.land (Nat.shiftRight p (Nat.mul 6 i)) 63 < 64
  rw [LceP.land_lit _ 6 63 (by norm_num)]
  omega

private theorem pmul_lt' (d p q : ℕ) : McL.pmul d p q < 2 ^ (6 * d) := by
  induction d with
  | zero => exact Nat.one_pos
  | succ d ih =>
    change Nat.lor (McL.pmul d p q) (Nat.shiftLeft (McL.pget q (McL.pget p d)) (6 * d)) < _
    rw [LceP.lor_shl ih]
    have hg := pget_lt' q (McL.pget p d)
    have e : 2 ^ (6 * (d + 1)) = 64 * 2 ^ (6 * d) := by
      rw [mul_add, pow_add]
      ring
    rw [e]
    calc McL.pmul d p q + McL.pget q (McL.pget p d) * 2 ^ (6 * d)
        < 2 ^ (6 * d) + McL.pget q (McL.pget p d) * 2 ^ (6 * d) := by omega
      _ = (McL.pget q (McL.pget p d) + 1) * 2 ^ (6 * d) := by ring
      _ ≤ 64 * 2 ^ (6 * d) := Nat.mul_le_mul_right _ (by omega)

private noncomputable def kpack (d b X Y : ℕ) : ℕ :=
  Nat.lor b (Nat.lor (Nat.shiftLeft X 1) (Nat.shiftLeft Y (1 + 6 * d)))
private noncomputable def kX (d st : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight st 1) (Nat.sub (Nat.shiftLeft 1 (6 * d)) 1)
private noncomputable def kY (d st : ℕ) : ℕ := Nat.shiftRight st (1 + 6 * d)

private theorem kpack_read (d : ℕ) {b X : ℕ} (hb : b < 2) (hX : X < 2 ^ (6 * d)) (Y : ℕ) :
    Nat.land (kpack d b X Y) 1 = b ∧ kX d (kpack d b X Y) = X ∧ kY d (kpack d b X Y) = Y := by
  have hP : 0 < 2 ^ (6 * d) := by positivity
  have e1 : Nat.lor (Nat.shiftLeft X 1) (Nat.shiftLeft Y (1 + 6 * d)) =
      Nat.shiftLeft (X + Y * 2 ^ (6 * d)) 1 := by
    have hX2 : Nat.shiftLeft X 1 < 2 ^ (1 + 6 * d) := by
      change X <<< 1 < _
      rw [Nat.shiftLeft_eq, pow_add, pow_one]
      omega
    rw [LceP.lor_shl hX2]
    change X <<< 1 + Y * 2 ^ (1 + 6 * d) = (X + Y * 2 ^ (6 * d)) <<< 1
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, pow_add]
    ring
  have e : kpack d b X Y = b + (X + Y * 2 ^ (6 * d)) * 2 := by
    unfold kpack
    rw [e1, LceP.lor_shl (k := 1) (by norm_num; omega), pow_one]
  have e2 : (b + (X + Y * 2 ^ (6 * d)) * 2) / 2 ^ 1 = X + Y * 2 ^ (6 * d) := by
    rw [pow_one]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [LceP.land1, e]
    omega
  · unfold kX
    rw [LceP.land_mask, LceP.shr_eq, e, e2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hX]
  · unfold kY
    rw [LceP.shr_eq, e, pow_add, ← Nat.div_div_eq_div_mul, e2, Nat.add_mul_div_right _ _ hP,
      Nat.div_eq_of_lt hX, zero_add]

private noncomputable def kst (XT G TW TL S Q H : ℕ → ℕ) (d nT : ℕ) (i : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat)
      (Nat.lor (nat_lit 1) (Nat.lor (Nat.shiftLeft (McL.pid d) (nat_lit 1))
        (Nat.shiftLeft (McL.pid d) (Nat.add (nat_lit 1) (Nat.mul (nat_lit 6) d)))))
      (fun i acc => (fun k sg => (fun X Y s q =>
          (fun ms mq => Nat.lor
              (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
                (andB (Nat.beq (Nat.land acc (nat_lit 1)) (nat_lit 1)) (andB (Nat.blt k nT)
                  (McL.Sub.redEq (McL.Sub.cat (McL.Sub.cat (McL.Sub.cat (XT (nat_lit 6))
                      (McL.Sub.subst XT s)) (XT (nat_lit 6))) (McL.Sub.subst XT (McL.Sub.pinvW q)))
                    (McL.Sub.ofEnt (TW k))))))
              (Nat.lor (Nat.shiftLeft (McL.pmul d X
                  (Bool.rec (motive := fun _ => Nat) ms (McL.Sub.pinv d ms) sg)) (nat_lit 1))
                (Nat.shiftLeft (McL.pmul d Y (Bool.rec (motive := fun _ => Nat)
                    (McL.pmul d (TL k) mq) (McL.Sub.pinv d (McL.pmul d (TL k) mq)) sg))
                  (Nat.add (nat_lit 1) (Nat.mul (nat_lit 6) d)))))
            (McL.evalW G d (McL.Sub.pw s) (McL.Sub.pn s))
            (McL.evalW G d (McL.Sub.pw q) (McL.Sub.pn q)))
          (Nat.land (Nat.shiftRight acc (nat_lit 1))
            (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 6) d)) (nat_lit 1)))
          (Nat.shiftRight acc (Nat.add (nat_lit 1) (Nat.mul (nat_lit 6) d)))
          (McL.Sub.ofEnt (S i)) (McL.Sub.ofEnt (Q i)))
        (Nat.shiftRight (H i) (nat_lit 1)) (Nat.beq (Nat.land (H i) (nat_lit 1)) (nat_lit 1))) i

private theorem k1Run_eq (XT G TW TL S Q H : ℕ → ℕ) (d nT m K : ℕ) :
    McL.Sub.k1Run XT G TW TL S Q H d nT m K =
      andB (Nat.beq (Nat.land (kst XT G TW TL S Q H d nT m) 1) 1)
        (andB (Nat.beq (kX d (kst XT G TW TL S Q H d nT m)) (McL.pid d))
          (Nat.beq (kY d (kst XT G TW TL S Q H d nT m)) K)) := rfl

private theorem kst_zero (XT G TW TL S Q H : ℕ → ℕ) (d nT : ℕ) :
    kst XT G TW TL S Q H d nT 0 = kpack d 1 (McL.pid d) (McL.pid d) := rfl

private theorem kst_succ (XT G TW TL S Q H : ℕ → ℕ) (d nT i : ℕ) :
    kst XT G TW TL S Q H d nT (i + 1) = kpack d
      (Bool.rec (motive := fun _ => ℕ) 0 1
        (andB (Nat.beq (Nat.land (kst XT G TW TL S Q H d nT i) 1) 1)
          (andB (Nat.blt (Nat.shiftRight (H i) 1) nT)
            (McL.Sub.redEq (McL.Sub.cat (McL.Sub.cat (McL.Sub.cat (XT 6)
              (McL.Sub.subst XT (McL.Sub.ofEnt (S i)))) (XT 6))
              (McL.Sub.subst XT (McL.Sub.pinvW (McL.Sub.ofEnt (Q i)))))
              (McL.Sub.ofEnt (TW (Nat.shiftRight (H i) 1)))))))
      (McL.pmul d (kX d (kst XT G TW TL S Q H d nT i))
        (Bool.rec (motive := fun _ => ℕ)
          (McL.evalW G d (McL.Sub.pw (McL.Sub.ofEnt (S i))) (McL.Sub.pn (McL.Sub.ofEnt (S i))))
          (McL.Sub.pinv d (McL.evalW G d (McL.Sub.pw (McL.Sub.ofEnt (S i)))
            (McL.Sub.pn (McL.Sub.ofEnt (S i)))))
          (Nat.beq (Nat.land (H i) 1) 1)))
      (McL.pmul d (kY d (kst XT G TW TL S Q H d nT i))
        (Bool.rec (motive := fun _ => ℕ)
          (McL.pmul d (TL (Nat.shiftRight (H i) 1))
            (McL.evalW G d (McL.Sub.pw (McL.Sub.ofEnt (Q i))) (McL.Sub.pn (McL.Sub.ofEnt (Q i)))))
          (McL.Sub.pinv d (McL.pmul d (TL (Nat.shiftRight (H i) 1))
            (McL.evalW G d (McL.Sub.pw (McL.Sub.ofEnt (Q i))) (McL.Sub.pn (McL.Sub.ofEnt (Q i))))))
          (Nat.beq (Nat.land (H i) 1) 1))) := rfl

private theorem brec01 {c : Bool} (h : Bool.rec (motive := fun _ => ℕ) 0 1 c = 1) : c = true := by
  cases c
  · exact absurd h Nat.zero_ne_one
  · rfl

private theorem brec01_lt (c : Bool) : Bool.rec (motive := fun _ => ℕ) 0 1 c < 2 := by
  cases c
  · exact Nat.zero_lt_two
  · exact Nat.one_lt_two

theorem k1Run_sound {G : Type*} [Group G] (gen : ℕ → G) (ψ : ℕ → G) (I : Set ℕ)
    {XT MG TW TL S Q H : ℕ → ℕ} {d nT m K : ℕ} (hF : smallTab XT)
    (hXinv : ∀ c < 8, pval gen (XT (c ^^^ 1)) = (pval gen (XT c))⁻¹)
    (hid : McL.pid d ∈ I ∧ ψ (McL.pid d) = 1)
    (hmul : ∀ p ∈ I, ∀ q ∈ I, McL.pmul d p q ∈ I ∧ ψ (McL.pmul d p q) = ψ p * ψ q)
    (hinv : ∀ p ∈ I, McL.Sub.pinv d p ∈ I ∧ ψ (McL.Sub.pinv d p) = (ψ p)⁻¹)
    (hW : ∀ W n, (∀ i < n, wLet W i < 6) →
      McL.evalW MG d W n ∈ I ∧ ψ (McL.evalW MG d W n) = fval gen XT W n)
    (hT : ∀ k < nT, TL k ∈ I ∧ bval gen (LceS.wWord (TW k)) (LceS.wLen (TW k)) = ψ (TL k))
    (hSQ : ∀ i < m, (∀ j < LceS.wLen (S i), wLet (LceS.wWord (S i)) j < 6) ∧
      (∀ j < LceS.wLen (Q i), wLet (LceS.wWord (Q i)) j < 6))
    (ht : pval gen (XT 6) * pval gen (XT 6) = 1)
    (h : McL.Sub.k1Run XT MG TW TL S Q H d nT m K = true) :
    ψ K = 1 := by
  rw [k1Run_eq] at h
  simp only [LceP.andB_iff, Nat.beq_eq] at h
  obtain ⟨hb, hX, hY⟩ := h
  have hpid : McL.pid d < 2 ^ (6 * d) := by
    rw [← hX]
    unfold kX
    rw [LceP.land_mask]
    exact Nat.mod_lt _ (by positivity)
  have inv : ∀ i ≤ m, ∃ b X Y, kst XT MG TW TL S Q H d nT i = kpack d b X Y ∧ b < 2 ∧
      X < 2 ^ (6 * d) ∧ (b = 1 → X ∈ I ∧ Y ∈ I ∧
        pval gen (XT 6) * ψ X * pval gen (XT 6) = ψ Y) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨1, McL.pid d, McL.pid d, kst_zero .., Nat.one_lt_two, hpid,
        fun _ => ⟨hid.1, hid.1, ?_⟩⟩
      rw [hid.2, mul_one, ht]
    | succ i ih =>
      intro hi
      obtain ⟨b, X, Y, hst, hb2, hX2, hI⟩ := ih (by omega)
      obtain ⟨r1, r2, r3⟩ := kpack_read d hb2 hX2 Y
      rw [kst_succ, hst, r1, r2, r3]
      refine ⟨_, _, _, rfl, brec01_lt _, pmul_lt' _ _ _, fun h1 => ?_⟩
      have hc := brec01 h1
      simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at hc
      obtain ⟨hb1, hkn, hred⟩ := hc
      obtain ⟨hXI, hYI, hXY⟩ := hI hb1
      obtain ⟨hSi, hQi⟩ := hSQ i (by omega)
      obtain ⟨msI, ρI, hid'⟩ := k1_ident gen ψ I hF hXinv hmul hW (hT _ hkn) hSi hQi hred
      obtain ⟨σI, ρI', hσ⟩ := k1_sign ψ I ht hinv msI ρI hid' (Nat.beq (Nat.land (H i) 1) 1)
      obtain ⟨x1, x2⟩ := hmul _ hXI _ σI
      obtain ⟨y1, y2⟩ := hmul _ hYI _ ρI'
      refine ⟨x1, y1, ?_⟩
      rw [x2, y2]
      exact k1_combine ht hXY hσ
  obtain ⟨b, X, Y, hst, hb2, hX2, hI⟩ := inv m le_rfl
  obtain ⟨r1, r2, r3⟩ := kpack_read d hb2 hX2 Y
  rw [hst, r1] at hb
  rw [hst, r2] at hX
  rw [hst, r3] at hY
  obtain ⟨-, -, h3⟩ := hI hb
  rw [hX, hY, hid.2, mul_one, ht] at h3
  exact h3.symm

end CFSG.Certificates.McLS

end
