module

public import CFSG.Certificates.Kernel.McL.Lab
public import CFSG.Certificates.Kernel.McL.Sub
public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.LceSP.Main
import CFSG.Certificates.Kernel.HOrbSound
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Certificates.McLLab

open CFSG.KC CFSG.Certificates.LCE

private theorem dig_concat {B A v k i : ℕ} (hB : 0 < B) (hA : A < B ^ k) :
    (A + v * B ^ k) / B ^ i % B = if i < k then A / B ^ i % B else v / B ^ (i - k) % B := by
  split_ifs with hi
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hi
    have e : v * B ^ (i + t + 1) = B ^ i * (B * (v * B ^ t)) := by ring
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    have e : (A + v * B ^ k) / B ^ (k + j) = v / B ^ j := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm v, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hA, Nat.zero_add]
    rw [e, Nat.add_sub_cancel_left]

private theorem pget_eq (p i : ℕ) : McL.pget p i = p / 64 ^ i % 64 := by
  change (p >>> (6 * i)) &&& (2 ^ 6 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

private theorem pget_lt (p i : ℕ) : McL.pget p i < 64 := by
  rw [pget_eq]
  exact Nat.mod_lt _ (by norm_num)

private noncomputable def fold6 (f : ℕ → ℕ) (d : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul 6 i))) d

private theorem fold6_spec (f : ℕ → ℕ) : ∀ d, (∀ i < d, f i < 64) →
    fold6 f d < 64 ^ d ∧ ∀ i, McL.pget (fold6 f d) i = if i < d then f i else 0
  | 0, _ => ⟨by simp [fold6], fun i => by
      rw [pget_eq]
      simp [fold6]⟩
  | d + 1, hf => by
    obtain ⟨hlt, hb⟩ := fold6_spec f d (fun i hi => hf i (by omega))
    have hlt2 : fold6 f d < 2 ^ (6 * d) := by
      rw [pow_mul]
      norm_num
      exact hlt
    have e : fold6 f (d + 1) = fold6 f d + f d * 64 ^ d := by
      change fold6 f d ||| f d <<< (6 * d) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt2, Nat.shiftLeft_eq, pow_mul,
        Nat.add_comm]
      norm_num
    have hfd := hf d (by omega)
    rw [e]
    refine ⟨?_, fun i => ?_⟩
    · calc fold6 f d + f d * 64 ^ d < 64 ^ d + f d * 64 ^ d := by omega
        _ = (f d + 1) * 64 ^ d := by ring
        _ ≤ 64 * 64 ^ d := Nat.mul_le_mul_right _ (by omega)
        _ = 64 ^ (d + 1) := by ring
    · have hbi := hb i
      rw [pget_eq] at hbi ⊢
      rw [dig_concat (by norm_num) hlt]
      split_ifs with h1 h2 h2
      · rw [hbi]
        simp only [h1, ↓reduceIte]
      · omega
      · have : i = d := by omega
        subst this
        simp [Nat.mod_eq_of_lt hfd]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt (show d < i by omega)
        rw [show d + j + 1 - d = j + 1 by omega, Nat.div_eq_of_lt (lt_of_lt_of_le hfd
          (Nat.le_self_pow (by omega) 64)), Nat.zero_mod]

private theorem pmul_eq (d p q : ℕ) : McL.pmul d p q = fold6 (fun i => McL.pget q (McL.pget p i)) d :=
  rfl

private theorem pid_eq (d : ℕ) : McL.pid d = fold6 (fun i => i) d := rfl

private theorem pcyc_eq (n : ℕ) : McL.pcyc n = fold6 (fun i => (i + 1) % n) n := rfl

private theorem pget_pmul (d p q : ℕ) {i : ℕ} (hi : i < d) :
    McL.pget (McL.pmul d p q) i = McL.pget q (McL.pget p i) := by
  rw [pmul_eq, (fold6_spec _ d (fun _ _ => pget_lt _ _)).2]
  simp only [hi, ↓reduceIte]

private theorem pmul_lt (d p q : ℕ) : McL.pmul d p q < 64 ^ d := by
  rw [pmul_eq]
  exact (fold6_spec _ d (fun _ _ => pget_lt _ _)).1

private theorem pget_pid {d i : ℕ} (hd : d ≤ 64) (hi : i < d) : McL.pget (McL.pid d) i = i := by
  rw [pid_eq, (fold6_spec _ d (fun j hj => by omega)).2]
  simp only [hi, ↓reduceIte]

private theorem pid_lt {d : ℕ} (hd : d ≤ 64) : McL.pid d < 64 ^ d := by
  rw [pid_eq]
  exact (fold6_spec _ d (fun j hj => by omega)).1

private theorem pget_pcyc {n i : ℕ} (hn : 0 < n) (hn64 : n ≤ 64) :
    McL.pget (McL.pcyc n) i = if i < n then (i + 1) % n else 0 := by
  rw [pcyc_eq, (fold6_spec _ n (fun j hj => lt_of_lt_of_le (Nat.mod_lt _ hn) hn64)).2]

private theorem pair_inj {d p q x y : ℕ} (hd : d ≤ 64) (hpq : McL.pmul d p q = McL.pid d)
    (hx : x < d) (hy : y < d) (h : McL.pget p x = McL.pget p y) : x = y := by
  have h1 := congrArg (fun r => McL.pget r x) hpq
  have h2 := congrArg (fun r => McL.pget r y) hpq
  rw [pget_pmul d p q hx, pget_pid hd hx] at h1
  rw [pget_pmul d p q hy, pget_pid hd hy] at h2
  rw [← h1, ← h2, h]

private theorem pairOK_spec {d p q : ℕ} (h : McL.pairOK d p q = true) :
    McL.pmul d p q = McL.pid d ∧ ∀ i < d, McL.pget p i < d := by
  unfold McL.pairOK at h
  simp only [LceP.andB_iff, Nat.beq_eq] at h
  obtain ⟨-, -, hr, -, hm⟩ := h
  refine ⟨hm, fun i hi => ?_⟩
  unfold McL.inRange at hr
  have := (LceP.allRec_iff (fun i => Nat.blt (McL.pget p i) d) d).1 hr i hi
  exact LceP.blt_true this


private noncomputable def sh (d x : ℕ) (j : ℤ) : ℕ := (((x : ℤ) + j) % (d : ℤ)).toNat

private theorem sh_cast {d x : ℕ} {j : ℤ} (hd : 0 < d) : (sh d x j : ℤ) = ((x : ℤ) + j) % d := by
  unfold sh
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

private theorem sh_lt {d : ℕ} (x : ℕ) (j : ℤ) (hd : 0 < d) : sh d x j < d := by
  have h1 := sh_cast (x := x) (j := j) hd
  have h2 : ((x : ℤ) + j) % d < d := Int.emod_lt_of_pos _ (by omega)
  omega

private theorem sh_sh {d : ℕ} (x : ℕ) (j k : ℤ) (hd : 0 < d) : sh d (sh d x j) k = sh d x (j + k) := by
  have h1 := sh_cast (x := sh d x j) (j := k) hd
  have h2 := sh_cast (x := x) (j := j + k) hd
  have h3 := sh_cast (x := x) (j := j) hd
  have : (sh d (sh d x j) k : ℤ) = sh d x (j + k) := by
    rw [h1, h2, h3, Int.emod_add_emod, add_assoc]
  exact_mod_cast this

private theorem sh_zero {d x : ℕ} (hx : x < d) : sh d x 0 = x := by
  unfold sh
  rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

private def Sh (d p : ℕ) (j : ℤ) : Prop := ∀ x < d, McL.pget p x = sh d x j

private theorem Sh_pmul {d p q : ℕ} {j k : ℤ} (hp : Sh d p j) (hq : Sh d q k) :
    Sh d (McL.pmul d p q) (j + k) := by
  intro x hx
  rw [pget_pmul d p q hx, hp x hx, hq _ (sh_lt x j (by omega)), sh_sh x j k (by omega)]

private theorem Sh_pid {d : ℕ} (hd : d ≤ 64) : Sh d (McL.pid d) 0 := by
  intro x hx
  rw [pget_pid hd hx, sh_zero hx]

private theorem Sh_inv {d p q : ℕ} {j : ℤ} (hd : d ≤ 64) (hp : Sh d p j)
    (hpq : McL.pmul d p q = McL.pid d) : Sh d q (-j) := by
  intro y hy
  have hd0 : 0 < d := by omega
  have hx := sh_lt y (-j) hd0
  have h1 := congrArg (fun r => McL.pget r (sh d y (-j))) hpq
  rw [pget_pmul d p q hx, pget_pid hd hx, hp _ hx, sh_sh y (-j) j hd0, neg_add_cancel,
    sh_zero hy] at h1
  exact h1

private def ShL (d A L : ℕ) (jb ja : ℤ) : Prop :=
  ∀ x < d, McL.pget A x = sh d (McL.pget L (sh d x jb)) ja

private theorem solve_label {d A L : ℕ} {jb ja t : ℤ} (hd : d ≤ 64) (hA : ShL d A L jb ja)
    (hL : ∀ y < d, McL.pget L y < d) (ht : Sh d A t) : Sh d L (t - jb - ja) := by
  intro y hy
  have hd0 : 0 < d := by omega
  set x := sh d y (-jb)
  have hx : x < d := sh_lt y (-jb) hd0
  have e1 : sh d x jb = y := by
    rw [sh_sh y (-jb) jb hd0, neg_add_cancel, sh_zero hy]
  have h := hA x hx
  rw [e1, ht x hx] at h
  have h2 : sh d (sh d (McL.pget L y) ja) (-ja) = sh d (sh d x t) (-ja) := by rw [h]
  rw [sh_sh _ ja (-ja) hd0, add_neg_cancel, sh_zero (hL y hy), sh_sh x t (-ja) hd0,
    sh_sh y (-jb) _ hd0] at h2
  rw [h2]
  congr 1
  ring

private theorem ShL_inj {d A L : ℕ} {jb ja : ℤ} (hA : ShL d A L jb ja)
    (hLlt : ∀ y < d, McL.pget L y < d)
    (hLinj : ∀ x < d, ∀ y < d, McL.pget L x = McL.pget L y → x = y) :
    (∀ x < d, McL.pget A x < d) ∧ ∀ x < d, ∀ y < d, McL.pget A x = McL.pget A y → x = y := by
  refine ⟨fun x hx => by rw [hA x hx]; exact sh_lt _ _ (by omega), fun x hx y hy h => ?_⟩
  have hd0 : 0 < d := by omega
  rw [hA x hx, hA y hy] at h
  have h2 : sh d (sh d (McL.pget L (sh d x jb)) ja) (-ja) =
      sh d (sh d (McL.pget L (sh d y jb)) ja) (-ja) := by rw [h]
  rw [sh_sh _ ja (-ja) hd0, sh_sh _ ja (-ja) hd0, add_neg_cancel,
    sh_zero (hLlt _ (sh_lt x jb hd0)), sh_zero (hLlt _ (sh_lt y jb hd0))] at h2
  have h3 := hLinj _ (sh_lt x jb hd0) _ (sh_lt y jb hd0) h2
  have h4 : sh d (sh d x jb) (-jb) = sh d (sh d y jb) (-jb) := by rw [h3]
  rw [sh_sh x jb (-jb) hd0, sh_sh y jb (-jb) hd0, add_neg_cancel, sh_zero hx, sh_zero hy] at h4
  exact h4

private theorem lor_ge_right (a b : ℕ) : b ≤ a ||| b := by
  rw [Nat.or_comm]
  exact Nat.left_le_or

private theorem pcyc_ge (n : ℕ) : ∀ k, ∀ i < k, (i + 1) % n * 64 ^ i ≤ Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.mod (Nat.succ i) n) (Nat.mul 6 i))) k
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, i, hi => by
    change _ ≤ Nat.lor _ (Nat.shiftLeft (Nat.mod (Nat.succ k) n) (Nat.mul 6 k))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact le_trans (pcyc_ge n k i hi) Nat.left_le_or
    · refine le_trans (le_of_eq ?_) (lor_ge_right _ _)
      have e : Nat.shiftLeft (Nat.mod (Nat.succ i) n) (Nat.mul 6 i) =
          (Nat.mod (Nat.succ i) n) <<< (6 * i) := rfl
      rw [e, Nat.shiftLeft_eq, pow_mul]
      norm_num
      rfl

private theorem pcyc_cases {d n A : ℕ} (hd : d ≤ 64) (hn : 0 < n) (hA : A < 64 ^ d)
    (hAe : A = McL.pcyc n) (hlt : ∀ x < d, McL.pget A x < d)
    (hinj : ∀ x < d, ∀ y < d, McL.pget A x = McL.pget A y → x = y) :
    (n = d ∧ 0 < d) ∨ (d = 0 ∧ n = 1) := by
  have hge := pcyc_ge n n
  change ∀ i < n, (i + 1) % n * 64 ^ i ≤ McL.pcyc n at hge
  rw [← hAe] at hge
  have hle : n ≤ d + 1 := by
    by_contra h
    have h1 := hge d (by omega)
    rw [Nat.mod_eq_of_lt (by omega)] at h1
    have : 64 ^ d ≤ (d + 1) * 64 ^ d := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    exact Or.inr ⟨rfl, by omega⟩
  left
  refine ⟨?_, hd0⟩
  rcases Nat.lt_trichotomy n d with h | h | h
  · exfalso
    have hn64 : n ≤ 64 := by omega
    have e1 := pget_pcyc (i := n - 1) hn hn64
    have e2 := pget_pcyc (i := n) hn hn64
    rw [← hAe] at e1 e2
    have c1 : n - 1 < n := by omega
    have c2 : ¬ n < n := lt_irrefl n
    simp only [c1, c2, ↓reduceIte] at e1 e2
    rw [show n - 1 + 1 = n by omega, Nat.mod_self] at e1
    have := hinj (n - 1) (by omega) n h (by rw [e1, e2])
    omega
  · exact h
  · exfalso
    have hnd : n = d + 1 := by omega
    rcases Nat.lt_or_ge d 64 with h64 | h64
    · have e1 := pget_pcyc (i := d - 1) hn (by omega)
      have c1 : d - 1 < n := by omega
      rw [← hAe] at e1
      simp only [c1, ↓reduceIte] at e1
      rw [show d - 1 + 1 = d by omega, Nat.mod_eq_of_lt (by omega)] at e1
      have := hlt (d - 1) (by omega)
      omega
    · have h1 := hge (d - 1) (by omega)
      rw [show d - 1 + 1 = d by omega, Nat.mod_eq_of_lt (by omega)] at h1
      have : d * 64 ^ (d - 1) = 64 ^ d := by
        rw [show d = 64 by omega]
        norm_num
      omega


private theorem rx_eq (R : ℕ) : McL.Lab.rx R = R % 1048576 := LceP.land20 R
private theorem rc_eq (R : ℕ) : McL.Lab.rc R = R / 1048576 % 256 := by
  change Nat.land (Nat.shiftRight R 20) 255 = _
  rw [LceP.land8, LceP.shr20]
private theorem ry_eq (R : ℕ) : McL.Lab.ry R = R / 268435456 % 1048576 := by
  change Nat.land (Nat.shiftRight R 28) 1048575 = _
  rw [LceP.land20, LceP.shr28]
private theorem ric_eq (R : ℕ) : McL.Lab.ric R = R / 281474976710656 % 256 := by
  change Nat.land (Nat.shiftRight R 48) 255 = _
  rw [LceP.land8, LceP.shr48]
private theorem rxc_eq (R : ℕ) : McL.Lab.rxc R = McL.Lab.rx R + 1048576 * McL.Lab.rc R := by
  change Nat.land R 268435455 = _
  rw [LceP.land28, rx_eq, rc_eq]
  omega
private theorem ryic_eq (R : ℕ) : McL.Lab.ryic R = McL.Lab.ry R + 1048576 * McL.Lab.ric R := by
  change Nat.land (Nat.shiftRight R 28) 268435455 = _
  rw [LceP.land28, LceP.shr28, ry_eq, ric_eq]
  have : R / 281474976710656 = R / 268435456 / 1048576 := by
    rw [Nat.div_div_eq_div_mul]
  omega

private theorem rx_lt (R : ℕ) : McL.Lab.rx R < 1048576 := by rw [rx_eq]; omega
private theorem ry_lt (R : ℕ) : McL.Lab.ry R < 1048576 := by rw [ry_eq]; omega
private theorem rc_lt (R : ℕ) : McL.Lab.rc R < 256 := by rw [rc_eq]; omega
private theorem ric_lt (R : ℕ) : McL.Lab.ric R < 256 := by rw [ric_eq]; omega

private theorem msF_cases (R st : ℕ) : McL.Lab.sF R st = 0 ∨
    (st % 268435456 = McL.Lab.rxc R ∧ McL.Lab.sF R st = McL.Lab.ry R + st / 268435456 * 1048576) := by
  unfold McL.Lab.sF
  rw [LceP.brec_eq]
  split_ifs with h
  · right
    rw [Nat.beq_eq] at h
    change Nat.land st 268435455 = _ at h
    rw [LceP.land28] at h
    refine ⟨h, ?_⟩
    change Nat.lor (McL.Lab.ry R) (Nat.shiftLeft (Nat.shiftRight st 28) 20) = _
    rw [LceP.shr28, LceP.lor20 _ (ry_lt R)]
  · exact Or.inl rfl

private theorem msB_cases (R st : ℕ) : McL.Lab.sB R st = 0 ∨
    (st % 268435456 = McL.Lab.ryic R ∧ McL.Lab.sB R st = McL.Lab.rx R + st / 268435456 * 1048576) := by
  unfold McL.Lab.sB
  rw [LceP.brec_eq]
  split_ifs with h
  · right
    rw [Nat.beq_eq] at h
    change Nat.land st 268435455 = _ at h
    rw [LceP.land28] at h
    refine ⟨h, ?_⟩
    change Nat.lor (McL.Lab.rx R) (Nat.shiftLeft (Nat.shiftRight st 28) 20) = _
    rw [LceP.shr28, LceP.lor20 _ (rx_lt R)]
  · exact Or.inl rfl

private theorem mfwd {R st cur W p : ℕ} (hcur : cur < 1048576)
    (hst : st = cur + 1048576 * (W / 256 ^ p)) (hm : st % 268435456 = McL.Lab.rxc R) :
    cur = McL.Lab.rx R ∧ wLet W p = McL.Lab.rc R ∧
      McL.Lab.ry R + st / 268435456 * 1048576 = McL.Lab.ry R + 1048576 * (W / 256 ^ (p + 1)) := by
  rw [rxc_eq] at hm
  have hfx := rx_lt R
  have hfc := rc_lt R
  have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
    rw [← LceP.div256_succ]
    omega
  refine ⟨by omega, ?_, by rw [h3]; ring⟩
  rw [LceP.wLet_eq]
  omega

private theorem mbwd {R st cur W p : ℕ} (hcur : cur < 1048576)
    (hst : st = cur + 1048576 * (W / 256 ^ p)) (hm : st % 268435456 = McL.Lab.ryic R) :
    cur = McL.Lab.ry R ∧ wLet W p = McL.Lab.ric R ∧
      McL.Lab.rx R + st / 268435456 * 1048576 = McL.Lab.rx R + 1048576 * (W / 256 ^ (p + 1)) := by
  rw [ryic_eq] at hm
  have hfy := ry_lt R
  have hic := ric_lt R
  have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
    rw [← LceP.div256_succ]
    omega
  refine ⟨by omega, ?_, by rw [h3]; ring⟩
  rw [LceP.wLet_eq]
  omega

private theorem mrec_spec {INV d lw lm nC R : ℕ} (h : McL.Lab.recOK INV d lw lm nC R = true) :
    McL.Lab.rx R < nC ∧ McL.Lab.ry R < nC ∧ McL.Lab.ric R = inv16 INV (McL.Lab.rc R) ∧
      McL.pairOK d (McL.Lab.rlab lm R) (McL.Lab.rlabI lw lm R) = true := by
  unfold McL.Lab.recOK at h
  simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

private theorem mlv_ric {G : Type*} [Group G] (gen : ℕ → G) {INV INV8 L d lw lm nC R : ℕ}
    (hinv : LceS.invOK INV INV8 L = true) (hR : McL.Lab.recOK INV d lw lm nC R = true) :
    LceP.lv gen (McL.Lab.ric R) = (LceP.lv gen (McL.Lab.rc R))⁻¹ := by
  obtain ⟨-, -, hfic, -⟩ := mrec_spec hR
  obtain ⟨hL, -, hc⟩ := LceP.invOK_spec hinv
  obtain ⟨h1, h2, h3⟩ := hc _ (rc_lt R)
  have hlt := ric_lt R
  rcases Nat.lt_or_ge (McL.Lab.rc R) L with hcL | hcL
  · rw [(h1 hcL).1] at hfic
    rw [hfic, LceP.lv_xor_one gen (by omega)]
  · by_cases h255 : McL.Lab.rc R = 255
    · rw [h2 hcL h255] at hfic
      rw [hfic, h255, LceP.lv_255, inv_one]
    · rw [h3 hcL h255] at hfic
      omega

section Walk

variable {G : Type*} [Group G] (gen : ℕ → G) (c0 : G) (d lw lm : ℕ)

private noncomputable def elM (rep : ℕ → G) (R : ℕ) : G :=
  rep (McL.Lab.rx R) * LceP.lv gen (McL.Lab.rc R) * (rep (McL.Lab.ry R))⁻¹

private def MRefs (FB : ℕ → ℕ) (rw INV nC : ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, McL.Lab.recOK INV d lw lm nC (McL.Lab.fct FB rw h) = true ∧ ∃ j : ℤ,
    Sh d (McL.Lab.rlab lm (McL.Lab.fct FB rw h)) j ∧ elM gen rep (McL.Lab.fct FB rw h) = c0 ^ j

private def WM (rep : ℕ → G) (s W ft : ℕ) (u : G) (L p st A : ℕ) : Prop :=
  A < 64 ^ d ∧ (st / 1048576 = 0 ∨ ∃ cur < 1048576, st = cur + 1048576 * (W / 256 ^ p) ∧
    ((p ≤ ft ∧ ∃ j : ℤ, Sh d A j ∧ rep s * LceP.bv gen W p * (rep cur)⁻¹ = c0 ^ j) ∨
      (ft < p ∧ ∃ jb ja : ℤ, ShL d A L jb ja ∧
        c0 ^ jb * u * c0 ^ ja = rep s * LceP.bv gen W p * (rep cur)⁻¹)))

private theorem WM_start (rep : ℕ → G) {s : ℕ} (W ft : ℕ) (u : G) (L : ℕ) (hd : d ≤ 64)
    (hs : s < 1048576) : WM gen c0 d rep s W ft u L 0 (wStart s W) (McL.pid d) := by
  refine ⟨pid_lt hd, Or.inr ⟨s, hs, ?_, Or.inl ⟨Nat.zero_le _, 0, Sh_pid hd, ?_⟩⟩⟩
  · unfold wStart
    rw [LceP.lor20 _ hs, pow_zero, Nat.div_one]
    ring
  · rw [LceP.bv_zero, mul_one, mul_inv_cancel, zpow_zero]

private theorem WM_ext {rep : ℕ → G} {s W ft : ℕ} {u : G} {L p A cur cur' l : ℕ} {k : ℤ}
    (hp : p ≠ ft)
    (hX : (p ≤ ft ∧ ∃ j : ℤ, Sh d A j ∧ rep s * LceP.bv gen W p * (rep cur)⁻¹ = c0 ^ j) ∨
      (ft < p ∧ ∃ jb ja : ℤ, ShL d A L jb ja ∧
        c0 ^ jb * u * c0 ^ ja = rep s * LceP.bv gen W p * (rep cur)⁻¹))
    (hl : Sh d l k) (he : rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹ = c0 ^ k) :
    ((p + 1 ≤ ft ∧ ∃ j : ℤ, Sh d (McL.pmul d A l) j ∧
        rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ = c0 ^ j) ∨
      (ft < p + 1 ∧ ∃ jb ja : ℤ, ShL d (McL.pmul d A l) L jb ja ∧
        c0 ^ jb * u * c0 ^ ja = rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹)) := by
  have e : rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ =
      (rep s * LceP.bv gen W p * (rep cur)⁻¹) * (rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹) := by
    rw [LceP.bv_succ]
    group
  rcases hX with ⟨hp', j, hj, hE⟩ | ⟨hp', jb, ja, hA, hE⟩
  · refine Or.inl ⟨by omega, j + k, Sh_pmul hj hl, ?_⟩
    rw [e, hE, he, zpow_add]
  · refine Or.inr ⟨by omega, jb, ja + k, fun x hx => ?_, ?_⟩
    · rw [pget_pmul d A l hx, hA x hx, hl _ (sh_lt _ _ (by omega)), sh_sh _ _ _ (by omega)]
    · rw [e, ← hE, he, zpow_add]
      group

end Walk


section Walk2

variable {G : Type*} [Group G] (gen : ℕ → G) (c0 : G) (d lw lm : ℕ)

private theorem WM_ref {FB : ℕ → ℕ} {rw INV INV8 L nC i : ℕ} (hd : d ≤ 64)
    (hinv : LceS.invOK INV INV8 L = true) {rep : ℕ → G} {s W ft : ℕ} {u : G} {Lb p st A : ℕ}
    (e : ℕ) (k : ℕ → ℕ → ℕ) (hrefs : MRefs gen c0 d lw lm FB rw INV nC rep i) (hp : p ≠ ft)
    (hI : WM gen c0 d rep s W ft u Lb p st A) :
    ∃ st' A', McL.Lab.refStep FB rw d lw lm i e st A k = k st' A' ∧
      WM gen c0 d rep s W ft u Lb (p + 1) st' A' := by
  unfold McL.Lab.refStep
  rw [LceP.brec_eq]
  split_ifs with hh
  · rw [Nat.blt_eq] at hh
    simp only [LceP.strictN_eq]
    obtain ⟨hrec, j, hj, hel⟩ := hrefs _ hh
    set R := McL.Lab.fct FB rw (Nat.shiftRight e (nat_lit 1))
    obtain ⟨-, -, -, hpair⟩ := mrec_spec hrec
    obtain ⟨hpq, -⟩ := pairOK_spec hpair
    have hlv := mlv_ric gen hinv hrec
    rw [LceP.brec_eq]
    split_ifs with hdir
    · refine ⟨_, _, rfl, pmul_lt _ _ _, ?_⟩
      rcases hI with ⟨-, hdead | ⟨cur, hcur, hst, hX⟩⟩
      · left
        rcases msB_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := rx_lt R
          omega
      · rcases msB_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := mbwd hcur hst hm
          refine ⟨McL.Lab.rx R, rx_lt R, by rw [h1, hs], ?_⟩
          refine WM_ext gen c0 d hp hX (Sh_inv hd hj hpq) ?_
          rw [hw, hlv, hc, zpow_neg, ← hel]
          unfold elM
          group
    · refine ⟨_, _, rfl, pmul_lt _ _ _, ?_⟩
      rcases hI with ⟨-, hdead | ⟨cur, hcur, hst, hX⟩⟩
      · left
        rcases msF_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := ry_lt R
          omega
      · rcases msF_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := mfwd hcur hst hm
          refine ⟨McL.Lab.ry R, ry_lt R, by rw [h1, hs], ?_⟩
          refine WM_ext gen c0 d hp hX hj ?_
          rw [hw, hc, ← hel]
          rfl
  · exact ⟨0, A, rfl, hI.1, Or.inl rfl⟩

private theorem WM_own {rep : ℕ → G} {s W ft Ri p st A : ℕ} (hp : p = ft)
    (hLr : ∀ y < d, McL.pget (McL.Lab.rlab lm Ri) y < d)
    (hI : WM gen c0 d rep s W ft (elM gen rep Ri) (McL.Lab.rlab lm Ri) p st A) :
    WM gen c0 d rep s W ft (elM gen rep Ri) (McL.Lab.rlab lm Ri) (p + 1) (McL.Lab.sF Ri st)
      (McL.pmul d A (McL.Lab.rlab lm Ri)) := by
  refine ⟨pmul_lt _ _ _, ?_⟩
  rcases hI with ⟨-, hdead | ⟨cur, hcur, hst, hX⟩⟩
  · left
    rcases msF_cases Ri st with h0 | ⟨hm, h1⟩
    · rw [h0]
    · rw [h1]
      have := ry_lt Ri
      omega
  · rcases msF_cases Ri st with h0 | ⟨hm, h1⟩
    · left
      rw [h0]
    · right
      obtain ⟨hc, hw, hs⟩ := mfwd hcur hst hm
      refine ⟨McL.Lab.ry Ri, ry_lt Ri, by rw [h1, hs], Or.inr ⟨by omega, ?_⟩⟩
      rcases hX with ⟨-, j, hj, hE⟩ | ⟨hlt, -⟩
      · refine ⟨j, 0, fun x hx => ?_, ?_⟩
        · rw [pget_pmul d A _ hx, hj x hx, sh_zero (hLr _ (sh_lt x j (by omega)))]
        · rw [hc] at hE
          rw [zpow_zero, mul_one, LceP.bv_succ, hw]
          have e : rep s * (LceP.bv gen W p * LceP.lv gen (McL.Lab.rc Ri)) *
              (rep (McL.Lab.ry Ri))⁻¹ = (rep s * LceP.bv gen W p * (rep (McL.Lab.rx Ri))⁻¹) *
              elM gen rep Ri := by
            unfold elM
            group
          rw [e, hE]
      · omega

private theorem res_spec {A st : ℕ} (hA : A < 2 ^ lw) :
    Nat.shiftRight (Nat.lor A (Nat.shiftLeft st lw)) lw = st ∧
      Nat.land (Nat.lor A (Nat.shiftLeft st lw)) (2 ^ lw - 1) = A := by
  rw [LceP.lor_shl hA]
  refine ⟨?_, ?_⟩
  · rw [LceP.shr_eq, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hA, Nat.zero_add]
  · change (A + st * 2 ^ lw) &&& (2 ^ lw - 1) = A
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hA]

private theorem walk_go {FB : ℕ → ℕ} {rw INV INV8 L nC i : ℕ} (hd : d ≤ 64)
    (hinv : LceS.invOK INV INV8 L = true) {rep : ℕ → G} {s W Ri ft n : ℕ}
    (hrefs : MRefs gen c0 d lw lm FB rw INV nC rep i)
    (hLr : ∀ y < d, McL.pget (McL.Lab.rlab lm Ri) y < d) :
    ∀ k ≤ n, ∀ J st A, WM gen c0 d rep s W ft (elM gen rep Ri) (McL.Lab.rlab lm Ri) (n - k) st A →
      ∃ st' A', McL.Lab.walkGo FB rw d lw lm i Ri ft n k J st A =
          Nat.lor A' (Nat.shiftLeft st' lw) ∧
        WM gen c0 d rep s W ft (elM gen rep Ri) (McL.Lab.rlab lm Ri) n st' A'
  | 0, _, J, st, A, hI => ⟨st, A, rfl, by rw [Nat.sub_zero] at hI; exact hI⟩
  | k + 1, hk, J, st, A, hI => by
    change ∃ st' A', Bool.rec (motive := fun _ => ℕ)
      (McL.Lab.refStep FB rw d lw lm i (Nat.land J 4294967295) st A
        (McL.Lab.walkGo FB rw d lw lm i Ri ft n k (Nat.shiftRight J 32)))
      (CFSG.KC.Loop.strictN (McL.Lab.sF Ri st) (fun st' => CFSG.KC.Loop.strictN
        (McL.pmul d A (McL.Lab.rlab lm Ri)) (McL.Lab.walkGo FB rw d lw lm i Ri ft n k J st')))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft) = _ ∧ _
    have e : n - k = n - (k + 1) + 1 := by omega
    cases hb : Nat.beq (Nat.sub n (Nat.succ k)) ft
    · dsimp only
      have hp : n - (k + 1) ≠ ft := by
        intro h
        have h2 : Nat.beq (Nat.sub n (Nat.succ k)) ft = true := by
          rw [Nat.beq_eq]
          exact h
        rw [hb] at h2
        exact Bool.false_ne_true h2
      obtain ⟨st1, A1, h1, hI1⟩ := WM_ref gen c0 d lw lm hd hinv (Nat.land J 4294967295)
        (McL.Lab.walkGo FB rw d lw lm i Ri ft n k (Nat.shiftRight J 32)) hrefs hp hI
      rw [h1]
      exact walk_go hd hinv hrefs hLr k (by omega) _ _ _ (by rw [e]; exact hI1)
    · dsimp only
      rw [LceP.strictN_eq, LceP.strictN_eq]
      exact walk_go hd hinv hrefs hLr k (by omega) _ _ _
        (by rw [e]; exact WM_own gen c0 d lm (Nat.eq_of_beq_eq_true hb) hLr hI)

private theorem trace_go {FB : ℕ → ℕ} {rw INV INV8 L nC i : ℕ} (hd : d ≤ 64)
    (hinv : LceS.invOK INV INV8 L = true) {rep : ℕ → G} {s W n Lb : ℕ} {u : G}
    (hrefs : MRefs gen c0 d lw lm FB rw INV nC rep i) :
    ∀ k ≤ n, ∀ J st A, WM gen c0 d rep s W n u Lb (n - k) st A →
      ∃ st' A', McL.Lab.traceGo FB rw d lw lm i k J st A = Nat.lor A' (Nat.shiftLeft st' lw) ∧
        WM gen c0 d rep s W n u Lb n st' A'
  | 0, _, J, st, A, hI => ⟨st, A, rfl, by rw [Nat.sub_zero] at hI; exact hI⟩
  | k + 1, hk, J, st, A, hI => by
    change ∃ st' A', McL.Lab.refStep FB rw d lw lm i (Nat.land J 4294967295) st A
      (McL.Lab.traceGo FB rw d lw lm i k (Nat.shiftRight J 32)) = _ ∧ _
    obtain ⟨st1, A1, h1, hI1⟩ := WM_ref gen c0 d lw lm hd hinv (Nat.land J 4294967295)
      (McL.Lab.traceGo FB rw d lw lm i k (Nat.shiftRight J 32)) hrefs (by omega) hI
    rw [h1]
    exact trace_go hd hinv hrefs k (by omega) _ _ _ (by rw [show n - k = n - (k + 1) + 1 by omega]; exact hI1)

end Walk2


private theorem msI_eq (S : ℕ) : McL.Lab.sI S = S % 4294967296 := LceP.land32 S
private theorem msN_eq (S : ℕ) : McL.Lab.sN S = S / 4294967296 := LceP.shr_eq S 32
private theorem msI_lt (S : ℕ) : McL.Lab.sI S < 4294967296 := by rw [msI_eq]; omega
private theorem mmkS_eq {i : ℕ} (nx : ℕ) (hi : i < 4294967296) :
    McL.Lab.mkS i nx = i + nx * 4294967296 := LceP.lor32 nx hi

private theorem Sh_pcyc {d n : ℕ} (hd : d ≤ 64) (h : (n = d ∧ 0 < d) ∨ (d = 0 ∧ n = 1)) :
    Sh d (McL.pcyc n) 1 := by
  intro x hx
  rcases h with ⟨rfl, hd0⟩ | ⟨rfl, -⟩
  · rw [pget_pcyc hd0 hd]
    simp only [hx, ↓reduceIte]
    unfold sh
    have : (((x : ℤ) + 1) % (n : ℤ)) = (((x + 1) % n : ℕ) : ℤ) := by push_cast; rfl
    rw [this, Int.toNat_natCast]
  · omega

section Facts

variable {G : Type*} [Group G] (gen : ℕ → G) (c0 : G) (d lw lm : ℕ)

private def MInv (FB : ℕ → ℕ) (rw INV nC i N : ℕ) : Prop :=
  ∃ rep : ℕ → G, rep 0 = 1 ∧ ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) →
    MRefs gen c0 d lw lm FB rw INV nC rep' i

private def MGood (FB : ℕ → ℕ) (rw INV nC S : ℕ) : Prop :=
  S = 0 ∨ (1 ≤ McL.Lab.sN S ∧ MInv gen c0 d lw lm FB rw INV nC (McL.Lab.sI S) (McL.Lab.sN S))

private theorem MGood_mkS {FB : ℕ → ℕ} {rw INV nC i N : ℕ} (hi : i ≤ 4294967296) (hN : 1 ≤ N)
    (hF : i < 4294967296 → MInv gen c0 d lw lm FB rw INV nC i N) :
    MGood gen c0 d lw lm FB rw INV nC (McL.Lab.mkS i N) := by
  right
  rcases Nat.lt_or_ge i 4294967296 with hlt | hge
  · rw [msN_eq, msI_eq, mmkS_eq N hlt]
    have e1 : (i + N * 4294967296) / 4294967296 = N := by omega
    have e2 : (i + N * 4294967296) % 4294967296 = i := by omega
    rw [e1, e2]
    exact ⟨hN, hF hlt⟩
  · have hi' : i = 4294967296 := by omega
    subst hi'
    have e : McL.Lab.mkS 4294967296 N = (1 ||| N) * 4294967296 := by
      change (1 <<< 32) ||| (N <<< 32) = _
      rw [← Nat.shiftLeft_or_distrib, Nat.shiftLeft_eq]
    rw [msN_eq, msI_eq, e, Nat.mul_div_cancel _ (by norm_num), Nat.mul_mod_left]
    exact ⟨le_trans (by norm_num) Nat.left_le_or,
      ⟨fun _ => 1, rfl, fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩⟩

private def MWords (c : G) (WT : ℕ → ℕ) : Prop :=
  ∀ id < 65536, WT id = 0 ∨
    ((McL.Lab.wKind (WT id) = 2 →
        LceP.bv gen (McL.Lab.wWord (WT id)) (McL.Lab.wLen (WT id)) = 1) ∧
      (McL.Lab.wKind (WT id) = 3 → McL.Lab.wHint (WT id) = 0 ∧
        LceP.bv gen (McL.Lab.wWord (WT id)) (McL.Lab.wLen (WT id)) = c))

private theorem mfactStep_good {FB WT SL : ℕ → ℕ} {INV INV8 rw nC L n : ℕ} {c : G} (hd : d ≤ 64)
    (hinv : LceS.invOK INV INV8 L = true) (hW : MWords gen c WT) (hn : 0 < n)
    (hSL : SL 0 = McL.pcyc n) (hlw : lw = 6 * d) (hlm : lm = 2 ^ lw - 1)
    (hc0 : (n = d ∧ 0 < d) ∨ (d = 0 ∧ n = 1) → c0 = c) {S J w : ℕ}
    (hS : MGood gen c0 d lw lm FB rw INV nC S)
    (hw : Nat.land J 1 = 1 → ∃ id < 65536, w = WT id) :
    MGood gen c0 d lw lm FB rw INV nC (McL.Lab.factStep FB SL INV rw d lw lm nC L J S w) := by
  unfold McL.Lab.factStep
  dsimp only
  rcases hS with h0 | ⟨hN, rep, hrep0, hrefs⟩
  · left
    rw [h0]
    rfl
  set i := McL.Lab.sI S with hidef
  set N := McL.Lab.sN S with hNdef
  have hS0 : Nat.blt (nat_lit 0) S = true := by
    rw [Nat.blt_eq]
    change 0 < S
    have : S / 4294967296 ≥ 1 := by rw [← msN_eq]; exact hN
    omega
  rw [hS0]
  dsimp only
  set R := McL.Lab.fct FB rw i
  cases hJ : Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)
  ·
    dsimp only
    cases ht : McL.Lab.treeOK INV d lw lm nC L N R
    · left
      rfl
    dsimp only
    refine MGood_mkS gen c0 d lw lm (Nat.succ_le_of_lt (msI_lt S)) (by omega) fun _ => ?_
    unfold McL.Lab.treeOK at ht
    simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at ht
    obtain ⟨hrR, hry, hrx, -, hl1, -⟩ := ht
    refine ⟨Function.update rep N (rep (McL.Lab.rx R) * LceP.lv gen (McL.Lab.rc R)), ?_,
      fun rep' hag h hh => ?_⟩
    · rw [Function.update_of_ne (show (0 : ℕ) ≠ N by omega)]
      exact hrep0
    have hag' : ∀ k < N, rep' k = rep k := by
      intro k hk
      rw [hag k (by omega), Function.update_of_ne (show k ≠ N by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag' h hh
    · refine ⟨hrR, 0, by rw [hl1]; exact Sh_pid hd, ?_⟩
      unfold elM
      rw [hry, hag N (by omega), Function.update_self, hag' _ hrx, mul_inv_cancel, zpow_zero]
  ·
    dsimp only
    obtain ⟨id, hid, rfl⟩ := hw (Nat.eq_of_beq_eq_true hJ)
    set w := WT id
    set fs := Nat.land (Nat.shiftRight J (nat_lit 17)) McL.Lab.m20
    set ft := Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)
    cases hwk : McL.Lab.walkOK FB SL INV rw d lw lm nC i R w fs ft J
    · left
      rfl
    dsimp only
    refine MGood_mkS gen c0 d lw lm (Nat.succ_le_of_lt (msI_lt S)) hN fun _ => ?_
    refine ⟨rep, hrep0, fun rep' hag h hh => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag h hh
    unfold McL.Lab.walkOK at hwk
    simp only [LceP.andB_iff, LceP.orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hwk
    obtain ⟨hrec, hft, hkind, hres1, hres2⟩ := hwk
    refine ⟨hrec, ?_⟩
    obtain ⟨-, -, -, hpair⟩ := mrec_spec hrec
    obtain ⟨hpq, hLr⟩ := pairOK_spec hpair
    have hfs : fs < 1048576 := by
      change Nat.land (Nat.shiftRight J 17) 1048575 < 1048576
      rw [LceP.land20]
      omega
    have hrefs' := hrefs rep' hag
    have hstart := WM_start gen c0 d rep' (McL.Lab.wWord w) ft (elM gen rep' R)
      (McL.Lab.rlab lm R) hd hfs
    obtain ⟨st', A', heq, hA', hWM⟩ := walk_go gen c0 d lw lm hd hinv hrefs' hLr
      (McL.Lab.wLen w) le_rfl (Nat.shiftRight J 53) _ _ (by rw [Nat.sub_self]; exact hstart)
    have hlt : A' < 2 ^ lw := by rw [hlw, pow_mul]; norm_num; exact hA'
    obtain ⟨r1, r2⟩ := res_spec lw hlt (st := st')
    rw [heq, r1] at hres1
    rw [heq, hlm, r2] at hres2
    rcases hWM with hdead | ⟨cur, hcur, hst, hX⟩
    · exfalso
      omega
    have hc : cur = fs := by omega
    rcases hX with ⟨hle, -⟩ | ⟨-, jb, ja, hAL, hE⟩
    · exfalso
      omega
    rw [hc] at hE
    rcases hW id hid with hw0 | ⟨hk2, hk3⟩
    · exfalso
      have hw0' : w = 0 := hw0
      rw [hw0'] at hkind
      rcases hkind with h | ⟨h, -⟩ <;> exact absurd h (by decide)
    rcases hkind with hkd | ⟨hkd, hfs0⟩
    ·
      have htg : McL.Lab.wTarget SL d w = McL.pid d := by
        unfold McL.Lab.wTarget
        rw [show Nat.beq (McL.Lab.wKind w) (nat_lit 3) = false by rw [hkd]; rfl]
      rw [htg] at hres2
      refine ⟨0 - jb - ja, solve_label hd hAL hLr (by rw [hres2]; exact Sh_pid hd), ?_⟩
      have hb := hk2 hkd
      rw [hb, mul_one, mul_inv_cancel] at hE
      have e : elM gen rep' R = c0 ^ (-jb) * (c0 ^ jb * elM gen rep' R * c0 ^ ja) * c0 ^ (-ja) := by
        rw [zpow_neg, zpow_neg]
        group
      rw [e, hE]
      group
    ·
      obtain ⟨hh0, hb⟩ := hk3 hkd
      have htg : McL.Lab.wTarget SL d w = McL.pcyc n := by
        unfold McL.Lab.wTarget
        rw [show Nat.beq (McL.Lab.wKind w) (nat_lit 3) = true by rw [hkd]; rfl]
        dsimp only
        rw [hh0, hSL]
      rw [htg] at hres2
      obtain ⟨hAr, hAi⟩ := ShL_inj hAL hLr (fun x hx y hy e => pair_inj hd hpq hx hy e)
      have hP := pcyc_cases hd hn hA' hres2 hAr hAi
      have hcc := hc0 hP
      refine ⟨1 - jb - ja, solve_label hd hAL hLr (by rw [hres2]; exact Sh_pcyc hd hP), ?_⟩
      have h0 : rep' 0 = 1 := by rw [hag 0 (by omega), hrep0]
      rw [hfs0, h0, one_mul, inv_one, mul_one, hb, ← hcc] at hE
      have e : elM gen rep' R = c0 ^ (-jb) * (c0 ^ jb * elM gen rep' R * c0 ^ ja) * c0 ^ (-ja) := by
        rw [zpow_neg, zpow_neg]
        group
      rw [e, hE]
      group

end Facts

section Loops

variable {G : Type*} [Group G] (gen : ℕ → G) (c0 : G) (d lw lm : ℕ)

private theorem mchunk_good {FB WT SL : ℕ → ℕ} {INV INV8 rw nC L n : ℕ} {c : G} (hd : d ≤ 64)
    (hinv : LceS.invOK INV INV8 L = true) (hW : MWords gen c WT) (hn : 0 < n)
    (hSL : SL 0 = McL.pcyc n) (hlw : lw = 6 * d) (hlm : lm = 2 ^ lw - 1)
    (hc0 : (n = d ∧ 0 < d) ∨ (d = 0 ∧ n = 1) → c0 = c) :
    ∀ k J S, MGood gen c0 d lw lm FB rw INV nC S →
      MGood gen c0 d lw lm FB rw INV nC (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
          (ih (Nat.shiftRight J (nat_lit 1)) (McL.Lab.factStep FB SL INV rw d lw lm nC L J S (nat_lit 0)))
          (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
            (nat_lit 65535)) WT) (fun w =>
            CFSG.KC.Loop.strictN (McL.Lab.factStep FB SL INV rw d lw lm nC L J S w)
              (ih (Nat.shiftRight J (McL.Lab.jLen J w)))))
          (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k J S)
  | 0, _, _, hS => hS
  | k + 1, J, S, hS => by
    dsimp only
    cases hJ : Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)
    · dsimp only
      apply mchunk_good hd hinv hW hn hSL hlw hlm hc0 k
      refine mfactStep_good gen c0 d lw lm hd hinv hW hn hSL hlw hlm hc0 hS fun h1 => ?_
      rw [h1] at hJ
      exact absurd hJ (by decide)
    · dsimp only
      rw [LceP.strictN_eq, LceP.strictN_eq, LceP.strictN_eq]
      apply mchunk_good hd hinv hW hn hSL hlw hlm hc0 k
      refine mfactStep_good gen c0 d lw lm hd hinv hW hn hSL hlw hlm hc0 hS fun _ => ?_
      refine ⟨_, ?_, rfl⟩
      change Nat.land (Nat.shiftRight J 1) 65535 < 65536
      rw [LceP.land_lit _ 16 65535 (by norm_num)]
      omega

private theorem mruns_good {FB WT SL : ℕ → ℕ} {INV INV8 rw nC L n : ℕ} {c : G} (hd : d ≤ 64)
    (hinv : LceS.invOK INV INV8 L = true) (hW : MWords gen c WT) (hn : 0 < n)
    (hSL : SL 0 = McL.pcyc n) (hlw : lw = 6 * d) (hlm : lm = 2 ^ lw - 1)
    (hc0 : (n = d ∧ 0 < d) ∨ (d = 0 ∧ n = 1) → c0 = c) :
    ∀ (Cs : List ℕ) S, MGood gen c0 d lw lm FB rw INV nC S →
      MGood gen c0 d lw lm FB rw INV nC (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L Cs S)
  | [], _, hS => hS
  | C :: Cs, S, hS => by
    change MGood gen c0 d lw lm FB rw INV nC (CFSG.KC.Loop.strictN
      (McL.Lab.runChunk FB WT SL INV rw d lw lm nC L C S)
      (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L Cs))
    rw [LceP.strictN_eq]
    exact mruns_good hd hinv hW hn hSL hlw hlm hc0 Cs _
      (mchunk_good gen c0 d lw lm hd hinv hW hn hSL hlw hlm hc0 _ _ _ hS)

end Loops

private def TGood (FB TW TL : ℕ → ℕ) (rw d lw lm nF S : ℕ) : Prop :=
  S = 0 ∨ ∀ k, k + 1 < S → ∃ J, McL.Lab.targetOK FB TW TL rw d lw lm nF k J = true

private theorem tchunk_good {FB TW TL : ℕ → ℕ} {rw d lw lm nF : ℕ} : ∀ k J S,
    TGood FB TW TL rw d lw lm nF S →
    TGood FB TW TL rw d lw lm nF (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
            (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S)
              (McL.Lab.targetOK FB TW TL rw d lw lm nF (Nat.sub S (nat_lit 1)) J)))
          (ih2 (Nat.shiftRight J (Nat.mul (nat_lit 32) (LceS.wLen (TW (Nat.sub S (nat_lit 1))))))))
        k J S)
  | 0, _, _, hS => hS
  | k + 1, J, S, hS => by
    dsimp only
    rw [LceP.strictN_eq]
    apply tchunk_good k
    cases hc : andB (Nat.blt (nat_lit 0) S)
        (McL.Lab.targetOK FB TW TL rw d lw lm nF (Nat.sub S (nat_lit 1)) J)
    · exact Or.inl rfl
    · right
      rw [LceP.andB_iff, Nat.blt_eq] at hc
      obtain ⟨hpos, hok⟩ := hc
      rcases hS with h0 | hS
      · change 0 < S at hpos
        omega
      intro k' hk'
      change k' + 1 < S + 1 at hk'
      rcases Nat.lt_or_ge (k' + 1) S with h | h
      · exact hS k' h
      · have : k' = Nat.sub S 1 := by
          change 0 < S at hpos
          change k' = S - 1
          omega
        exact ⟨J, this ▸ hok⟩

private theorem truns_good {FB TW TL : ℕ → ℕ} {rw d lw lm nF : ℕ} : ∀ (Ts : List ℕ) S,
    TGood FB TW TL rw d lw lm nF S →
    TGood FB TW TL rw d lw lm nF (McL.Lab.runTargets FB TW TL rw d lw lm nF Ts S)
  | [], _, hS => hS
  | C :: Ts, S, hS => by
    change TGood FB TW TL rw d lw lm nF (CFSG.KC.Loop.strictN _ _)
    rw [LceP.strictN_eq]
    exact truns_good Ts _ (tchunk_good _ _ _ hS)


section Anchor

variable {G : Type*} [Group G] (gen : ℕ → G)

private noncomputable def pV (v : ℕ) : G := LceP.bv gen (McL.Sub.pw v) (McL.Sub.pn v)

private theorem pk_spec {n W : ℕ} (hn : n < 65536) :
    McL.Sub.pn (McL.Sub.pk n W) = n ∧ McL.Sub.pw (McL.Sub.pk n W) = W := by
  have e : McL.Sub.pk n W = n + W * 2 ^ 16 := LceP.lor_shl (k := 16) (by norm_num; omega)
  constructor
  · change Nat.land (McL.Sub.pk n W) 65535 = n
    rw [LceP.land_lit _ 16 65535 (by norm_num), e]
    omega
  · change Nat.shiftRight (McL.Sub.pk n W) 16 = W
    rw [LceP.shr_eq, e]
    omega

private theorem pn_lt (v : ℕ) : McL.Sub.pn v < 65536 := by
  change Nat.land v 65535 < 65536
  rw [LceP.land_lit _ 16 65535 (by norm_num)]
  omega

private theorem cat_spec {a b : ℕ} (ha : McL.Sub.pw a < 256 ^ McL.Sub.pn a)
    (hb : McL.Sub.pw b < 256 ^ McL.Sub.pn b) (hn : McL.Sub.pn a + McL.Sub.pn b < 65536) :
    McL.Sub.pn (McL.Sub.cat a b) = McL.Sub.pn a + McL.Sub.pn b ∧
      McL.Sub.pw (McL.Sub.cat a b) < 256 ^ McL.Sub.pn (McL.Sub.cat a b) ∧
      pV gen (McL.Sub.cat a b) = pV gen a * pV gen b := by
  have hW : Nat.lor (McL.Sub.pw a) (Nat.shiftLeft (McL.Sub.pw b) (Nat.mul 8 (McL.Sub.pn a))) =
      McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a := by
    rw [LceP.lor_shl (by change _ < 2 ^ (8 * _); rw [LceP.two_pow_eight_mul]; exact ha)]
    change _ + _ * 2 ^ (8 * _) = _
    rw [LceP.two_pow_eight_mul]
  have e : McL.Sub.cat a b = McL.Sub.pk (McL.Sub.pn a + McL.Sub.pn b)
      (McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a) := by
    unfold McL.Sub.cat
    rw [← hW]
    rfl
  obtain ⟨h1, h2⟩ := pk_spec (W := McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a) hn
  rw [e]
  unfold pV
  rw [h1, h2]
  refine ⟨rfl, ?_, LceP.bv_concat gen ha⟩
  calc McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a
      < 256 ^ McL.Sub.pn a + McL.Sub.pw b * 256 ^ McL.Sub.pn a := by omega
    _ = (McL.Sub.pw b + 1) * 256 ^ McL.Sub.pn a := by ring
    _ ≤ 256 ^ McL.Sub.pn b * 256 ^ McL.Sub.pn a := Nat.mul_le_mul_right _ (by omega)
    _ = 256 ^ (McL.Sub.pn a + McL.Sub.pn b) := by ring

private theorem powW_spec {v : ℕ} (hv : McL.Sub.pw v < 256 ^ McL.Sub.pn v) :
    ∀ k, k * McL.Sub.pn v < 65536 →
      McL.Sub.pn (McL.Sub.powW v k) = k * McL.Sub.pn v ∧
      McL.Sub.pw (McL.Sub.powW v k) < 256 ^ McL.Sub.pn (McL.Sub.powW v k) ∧
      pV gen (McL.Sub.powW v k) = (pV gen v) ^ k
  | 0, _ => by
    obtain ⟨h1, h2⟩ := pk_spec (n := 0) (W := 0) (by norm_num)
    have e : McL.Sub.powW v 0 = McL.Sub.pk 0 0 := rfl
    unfold pV
    rw [e, h1, h2, Nat.zero_mul, LceP.bv_zero]
    exact ⟨rfl, by norm_num, (pow_zero _).symm⟩
  | k + 1, hk => by
    obtain ⟨h1, h2, h3⟩ := powW_spec hv k
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ k)) hk)
    have e : McL.Sub.powW v (k + 1) = McL.Sub.cat (McL.Sub.powW v k) v := rfl
    obtain ⟨c1, c2, c3⟩ := cat_spec gen h2 hv (by rw [h1, ← Nat.succ_mul]; exact hk)
    rw [e]
    refine ⟨by rw [c1, h1]; ring, c2, by rw [c3, h3, pow_succ]⟩

private theorem mkK_spec {c s : ℕ} (hc : c < 65536) :
    Bind.kCnt (Bind.mkK c s) = c ∧ Bind.kStk (Bind.mkK c s) = s := by
  have e : Bind.mkK c s = c + s * 2 ^ 16 := LceP.lor_shl (k := 16) (by norm_num; omega)
  constructor
  · change Nat.land (Bind.mkK c s) 65535 = c
    rw [LceP.land_lit _ 16 65535 (by norm_num), e]
    omega
  · change Nat.shiftRight (Bind.mkK c s) 16 = s
    rw [LceP.shr_eq, e]
    omega

private noncomputable def redAt (v q : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun q P => Bool.rec (motive := fun _ => ℕ) (Bind.push (nat_lit 1) P (wLet (McL.Sub.pw v) q)) P
      (Nat.beq (wLet (McL.Sub.pw v) q) (nat_lit 255))) q

private theorem redAt_spec (v : ℕ) : ∀ q ≤ McL.Sub.pn v, ∃ l : List ℕ,
    redAt v q = Bind.mkK l.length (LceP.enc l) ∧ l.length ≤ q ∧ (∀ x ∈ l, x < 255) ∧
      LceP.lval gen l = LceP.bv gen (McL.Sub.pw v) q
  | 0, _ => ⟨[], rfl, le_rfl, by simp, rfl⟩
  | q + 1, hq => by
    obtain ⟨l, hl, hlen, hlt, hlv⟩ := redAt_spec v q (by omega)
    have hq' := pn_lt v
    have e : redAt v (q + 1) = Bool.rec (motive := fun _ => ℕ)
        (Bind.push 1 (redAt v q) (wLet (McL.Sub.pw v) q)) (redAt v q)
        (Nat.beq (wLet (McL.Sub.pw v) q) 255) := rfl
    rw [e, LceP.brec_eq, LceP.bv_succ, ← hlv, hl]
    set x := wLet (McL.Sub.pw v) q
    have hx := LceP.wLet_lt (McL.Sub.pw v) q
    split_ifs with h255
    · rw [Nat.beq_eq] at h255
      rw [h255, LceP.lv_255, mul_one]
      exact ⟨l, rfl, by omega, hlt, rfl⟩
    · rw [Nat.beq_eq] at h255
      obtain ⟨k1, k2⟩ := mkK_spec (s := LceP.enc l) (show l.length < 65536 by omega)
      unfold Bind.push
      rw [k1, k2, LceP.brec_eq]
      split_ifs with hc
      · simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at hc
        obtain ⟨hpos, htop⟩ := hc
        rcases l with _ | ⟨y, l'⟩
        · exact absurd hpos (by simp)
        · have hy := hlt y (by simp)
          have e1 : Nat.land (LceP.enc (y :: l')) 255 = y + 1 := by
            change (LceP.enc l' * 256 + (y + 1)) &&& (2 ^ 8 - 1) = _
            rw [Nat.and_two_pow_sub_one_eq_mod]
            omega
          rw [e1] at htop
          have hyx : y = x ^^^ 1 := by
            change y + 1 = Nat.xor x 1 + 1 at htop
            exact Nat.succ.inj htop
          have hx254 : x < 254 := by
            rcases Nat.lt_or_ge x 254 with h | h
            · exact h
            · exfalso
              have : x = 254 := by omega
              rw [this] at hyx
              have : (254 : ℕ) ^^^ 1 = 255 := by decide
              omega
          refine ⟨l', ?_, by simp at hlen ⊢; omega, fun z hz => hlt z (by simp [hz]), ?_⟩
          · have e2 : Nat.shiftRight (LceP.enc (y :: l')) 8 = LceP.enc l' := by
              change (LceP.enc l' * 256 + (y + 1)) >>> 8 = LceP.enc l'
              rw [Nat.shiftRight_eq_div_pow]
              omega
            have e3 : Nat.sub (y :: l').length 1 = l'.length := by simp
            rw [e2, e3]
          · rw [LceP.lval_cons, hyx, LceP.lv_xor_one gen hx254, mul_assoc, inv_mul_cancel, mul_one]
      · refine ⟨x :: l, ?_, by simp; omega, ?_, LceP.lval_cons gen _ _⟩
        · rfl
        · intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · omega
          · exact hlt z hz

private theorem enc_byte : ∀ (l : List ℕ), (∀ x ∈ l, x < 255) → ∀ i < l.length,
    LceP.enc l / 256 ^ i % 256 = l[i]! + 1
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | y :: l, hl, i, hi => by
    have hy := hl y (by simp)
    rcases i with _ | i
    · change (LceP.enc l * 256 + (y + 1)) / 1 % 256 = y + 1
      omega
    · have := enc_byte l (fun z hz => hl z (by simp [hz])) i (by simpa using hi)
      change (LceP.enc l * 256 + (y + 1)) / 256 ^ (i + 1) % 256 = l[i]! + 1
      rw [pow_succ', ← Nat.div_div_eq_div_mul, show (LceP.enc l * 256 + (y + 1)) / 256 = LceP.enc l by
        omega]
      exact this

private theorem stkW_spec {l : List ℕ} (hl : ∀ x ∈ l, x < 255) (hn : l.length < 65536) :
    McL.Sub.pn (McL.Sub.stkW (Bind.mkK l.length (LceP.enc l))) = l.length ∧
      (∀ q < l.length, wLet (McL.Sub.pw (McL.Sub.stkW (Bind.mkK l.length (LceP.enc l)))) q < 255) ∧
      pV gen (McL.Sub.stkW (Bind.mkK l.length (LceP.enc l))) = LceP.lval gen l := by
  obtain ⟨k1, k2⟩ := mkK_spec (s := LceP.enc l) hn
  set P := Bind.mkK l.length (LceP.enc l)
  set f : ℕ → ℕ := fun q => Bind.kByte P (l.length - (q + 1)) - 1
  have hbyte : ∀ i < l.length, Bind.kByte P i = l[i]! + 1 := by
    intro i hi
    change Nat.land (Nat.shiftRight (Bind.kStk P) (Nat.mul 8 i)) 255 = _
    rw [k2, LceP.land8, LceP.shr_eq]
    change LceP.enc l / 2 ^ (8 * i) % 256 = _
    rw [LceP.two_pow_eight_mul]
    exact enc_byte l hl i hi
  have hf : ∀ j, f j < 256 := fun j => by
    have := LceP.wLet_lt (Bind.kStk P) (l.length - (j + 1))
    change wLet (Bind.kStk P) (l.length - (j + 1)) - 1 < 256
    omega
  have e : McL.Sub.stkW P = McL.Sub.pk l.length (HO.byteFold f l.length) := by
    unfold McL.Sub.stkW
    rw [k1]
    rfl
  obtain ⟨hb1, hb2⟩ := HO.byteFold_spec f hf l.length
  obtain ⟨p1, p2⟩ := pk_spec (W := HO.byteFold f l.length) hn
  rw [e, p1, p2]
  refine ⟨rfl, fun q hq => ?_, ?_⟩
  · rw [LceP.wLet_eq, hb2 q hq]
    change Bind.kByte P (l.length - (q + 1)) - 1 < 255
    rw [hbyte _ (by omega)]
    have := hl (l[l.length - (q + 1)]!) (by
      rw [getElem!_pos l _ (by omega)]
      exact List.getElem_mem _)
    omega
  · unfold pV
    rw [p1, p2]
    rw [show LceP.bv gen (HO.byteFold f l.length) l.length =
      bval gen (HO.byteFold f l.length) l.length from rfl, HO.bval_byteFold gen f hf]
    unfold LceP.lval
    congr 1
    apply List.ext_getElem (by simp)
    intro q h1 h2
    have hq : q < l.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse]
    change LceP.lv gen (Bind.kByte P (l.length - (q + 1)) - 1) = LceP.lv gen _
    rw [hbyte _ (by omega), Nat.add_sub_cancel, getElem!_pos l _ (by omega)]
    congr 2
    omega

end Anchor

section Anchor2

variable {G : Type*} [Group G] (gen : ℕ → G)

private theorem bv_mod (x n : ℕ) : LceP.bv gen x n = LceP.bv gen (x % 256 ^ n) n := by
  apply HO.bval_congr gen
  intro i hi
  conv_lhs => rw [← Nat.mod_add_div x (256 ^ n), Nat.mul_comm]
  exact HO.byte_add_high hi

private theorem conjRot_one {e ul U : ℕ}
    (hr : LceS.wWord e < 2 ^ (8 * LceS.wLen e) ∧ bval gen (LceS.wWord e) (LceS.wLen e) = 1)
    (hU : ∀ q < McL.Sub.pn U, wLet (McL.Sub.pw U) q < 255)
    (h : McL.Sub.isConjRot e ul U = true) : pV gen U = 1 := by
  unfold McL.Sub.isConjRot at h
  simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨hlen, hmir, -, hrot⟩ := h
  set m := LceS.wLen e
  set X := McL.Sub.pw U
  have hlen' : McL.Sub.pn U = ul + (m + ul) := by
    change McL.Sub.pn U = 2 * ul + m at hlen
    omega
  set A := X % 256 ^ ul
  set B := X / 256 ^ ul
  set M := B % 256 ^ m
  set C := B / 256 ^ m
  have hA : A < 256 ^ ul := Nat.mod_lt _ (by positivity)
  have hM : M < 256 ^ m := Nat.mod_lt _ (by positivity)
  have eX : X = A + B * 256 ^ ul := by rw [Nat.mul_comm]; exact (Nat.mod_add_div X _).symm
  have eB : B = M + C * 256 ^ m := by rw [Nat.mul_comm]; exact (Nat.mod_add_div B _).symm
  unfold pV
  change LceP.bv gen X (McL.Sub.pn U) = 1
  rw [hlen', eX, LceP.bv_concat gen hA, eB, LceP.bv_concat gen hM]
  have hmid : M = Nat.land (Nat.shiftRight X (Nat.mul 8 ul))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 8 m)) 1) := by
    rw [LceP.land_mask, LceP.shr_eq]
    change B % 256 ^ m = X / 2 ^ (8 * ul) % 2 ^ (8 * m)
    rw [LceP.two_pow_eight_mul, LceP.two_pow_eight_mul]
  rw [← hmid] at hrot
  obtain ⟨s, hs, hseq⟩ := LceP.anyRec_iff _ m hrot
  rw [Nat.beq_eq] at hseq
  have hr' : LceS.wWord e < 256 ^ m := by rw [← LceP.two_pow_eight_mul]; exact hr.1
  have h1 : LceP.bv gen M m = 1 := by
    rw [← hseq]
    exact LceP.bv_rot gen hr' hs hr.2
  have hmir' := (LceP.allRec_iff (fun q => Nat.beq (Nat.xor (McL.Sub.pl U q) 1)
    (McL.Sub.pl U (Nat.sub (McL.Sub.pn U) (Nat.succ q)))) ul).1 hmir
  have hletA : ∀ q < ul, wLet A q = wLet X q := by
    intro q hq
    rw [LceP.wLet_eq, LceP.wLet_eq, eX]
    exact (HO.byte_add_high hq).symm
  have hletC : ∀ t < ul, wLet C t = wLet X (ul + m + t) := by
    intro t ht
    rw [LceP.wLet_eq, LceP.wLet_eq]
    rw [pow_add, pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have hA254 : ∀ q < ul, wLet A q < 254 := by
    intro q hq
    have hm := Nat.eq_of_beq_eq_true (hmir' q hq)
    rw [hletA q hq]
    have h2 := hU (ul + (m + ul) - (q + 1)) (by omega)
    change wLet X q ^^^ 1 = wLet X (McL.Sub.pn U - (q + 1)) at hm
    rw [hlen'] at hm
    rw [← hm] at h2
    have h3 := hU q (by omega)
    rcases Nat.lt_or_ge (wLet X q) 254 with h4 | h4
    · exact h4
    · have : wLet X q = 254 := by omega
      rw [this] at h2
      exact absurd h2 (by decide)
  have hC : LceP.bv gen C ul = (LceP.bv gen A ul)⁻¹ := by
    change bval gen C ul = (bval gen A ul)⁻¹
    rw [← HO.bval_invW gen (fun q hq => hA254 q hq)]
    apply HO.bval_congr gen
    intro k hk
    rw [HO.invW_eq, (HO.byteFold_spec _ (fun k => HO.byte_xor_lt A _) ul).2 k hk, ← LceP.wLet_eq,
      hletC k hk]
    change _ = wLet A (ul - 1 - k) ^^^ 1
    rw [hletA _ (by omega)]
    have hm := Nat.eq_of_beq_eq_true (hmir' (ul - 1 - k) (by omega))
    change wLet X (ul - 1 - k) ^^^ 1 = wLet X (McL.Sub.pn U - (ul - 1 - k + 1)) at hm
    rw [hm, hlen']
    congr 1
    omega
  rw [h1, hC, one_mul, mul_inv_cancel]

private theorem anchor_pow {RT ST SL : ℕ → ℕ} {R n r ul : ℕ}
    (hRT : ∀ r < R, LceS.wWord (RT r) < 2 ^ (8 * LceS.wLen (RT r)) ∧
      bval gen (LceS.wWord (RT r)) (LceS.wLen (RT r)) = 1)
    (hST : LceS.wWord (ST 0) < 2 ^ (8 * LceS.wLen (ST 0)) ∧ LceS.wLen (ST 0) * n < 65536)
    (hanc : McL.Sub.anchorOK RT ST SL R n r ul = true) :
    0 < n ∧ SL 0 = McL.pcyc n ∧ (LceP.bv gen (LceS.wWord (ST 0)) (LceS.wLen (ST 0))) ^ n = 1 := by
  unfold McL.Sub.anchorOK at hanc
  simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at hanc
  obtain ⟨hn, hSL, hcr⟩ := hanc
  refine ⟨hn, hSL, ?_⟩
  set v0 := McL.Sub.ofEnt (ST 0)
  have hlen : LceS.wLen (ST 0) < 65536 := by
    change Nat.land (Nat.shiftRight (ST 0) 2) 1023 < 65536
    rw [LceP.land_lit _ 10 1023 (by norm_num)]
    omega
  obtain ⟨p1, p2⟩ := pk_spec (W := LceS.wWord (ST 0)) hlen
  have hv0 : McL.Sub.pw v0 < 256 ^ McL.Sub.pn v0 := by
    change McL.Sub.pw (McL.Sub.pk _ _) < 256 ^ McL.Sub.pn (McL.Sub.pk _ _)
    rw [p1, p2, ← LceP.two_pow_eight_mul]
    exact hST.1
  have hval : pV gen v0 = LceP.bv gen (LceS.wWord (ST 0)) (LceS.wLen (ST 0)) := by
    change LceP.bv gen (McL.Sub.pw (McL.Sub.pk _ _)) (McL.Sub.pn (McL.Sub.pk _ _)) = _
    rw [p1, p2]
  have hpn : n * McL.Sub.pn v0 < 65536 := by
    change n * McL.Sub.pn (McL.Sub.pk _ _) < 65536
    rw [p1, Nat.mul_comm]
    exact hST.2
  obtain ⟨w1, -, w3⟩ := powW_spec gen hv0 n hpn
  set V := McL.Sub.powW v0 n
  obtain ⟨l, hl, hll, hlt, hlv⟩ := redAt_spec gen V (McL.Sub.pn V) le_rfl
  have hred : McL.Sub.red V = redAt V (McL.Sub.pn V) := rfl
  obtain ⟨s1, s2, s3⟩ := stkW_spec gen hlt (by have := pn_lt V; omega)
  unfold McL.Sub.conjRelOK at hcr
  simp only [LceP.andB_iff, Nat.blt_eq] at hcr
  obtain ⟨hrR, hconj⟩ := hcr
  rw [hred, hl] at hconj
  have h1 := conjRot_one gen (hRT r hrR) (fun q hq => s2 q (by rw [s1] at hq; exact hq)) hconj
  rw [s3, hlv] at h1
  rw [← hval, ← w3]
  exact h1

end Anchor2

theorem targets_sound {G : Type*} [Group G] (gen : ℕ → G) {FB WT SL RT ST TW TL : ℕ → ℕ}
    {INV INV8 rw d lw lm nC L R K m nF nT n r ul S0 S1 T0 T1 nF' : ℕ} {Cs Ts : List ℕ}
    (hRT : ∀ r < R, LceS.wWord (RT r) < 2 ^ (8 * LceS.wLen (RT r)) ∧
      bval gen (LceS.wWord (RT r)) (LceS.wLen (RT r)) = 1)
    (hWT : ∀ k < 65536, WT k = 0 ∨ ∃ k' < m, WT k = WT k')
    (hwords : McL.Lab.wordsOK WT RT ST INV INV8 R K m = true)
    (hinv : LceS.invOK INV INV8 L = true)
    (hgeom : lw = 6 * d ∧ rw = 56 + 2 * lw ∧ lm = 2 ^ lw - 1) (hd : d ≤ 64) (hK : K = 1)
    (hST : LceS.wWord (ST 0) < 2 ^ (8 * LceS.wLen (ST 0)) ∧ LceS.wLen (ST 0) * n < 65536)
    (hanc : McL.Sub.anchorOK RT ST SL R n r ul = true) (_hnC : nC ≤ 2 ^ 20)
    (hS0 : S0 = McL.Lab.mkS 0 1)
    (hfacts : Nat.beq (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L Cs S0) S1 = true)
    (hS1 : S1 = McL.Lab.mkS nF nC) (hnF : nF < 2 ^ 32)
    (htg : Nat.beq (McL.Lab.runTargets FB TW TL rw d lw lm nF' Ts T0) T1 = true)
    (hT0 : T0 = 1) (hT1 : T1 = nT + 1) (hnF' : nF' = nF) :
    ∀ k < nT, TL k = McL.pid d → bval gen (LceS.wWord (TW k)) (LceS.wLen (TW k)) = 1 := by
  obtain ⟨hlw, -, hlm⟩ := hgeom
  subst nF'
  obtain ⟨hn, hSL, hcn⟩ := anchor_pow gen hRT hST hanc
  set c := LceP.bv gen (LceS.wWord (ST 0)) (LceS.wLen (ST 0)) with hcdef
  classical
  set P : Prop := (n = d ∧ 0 < d) ∨ (d = 0 ∧ n = 1) with hPdef
  set c0 : G := if P then c else 1 with hc0def
  have hc0 : P → c0 = c := fun h => by simp only [hc0def, h, ↓reduceIte]
  have hW : MWords gen c WT := by
    intro id hid
    rcases hWT id hid with h0 | ⟨k', hk', hk⟩
    · exact Or.inl h0
    right
    rw [hk]
    have hw := (LceP.allRec_iff (fun w => McL.Lab.wordOK RT ST INV INV8 R K (WT w)) m).1 hwords k' hk'
    unfold McL.Lab.wordOK at hw
    refine ⟨fun h2 => ?_, fun h3 => ?_⟩
    · have hb : Nat.beq (McL.Lab.wKind (WT k')) (nat_lit 2) = true := by rw [h2]; rfl
      rw [hb] at hw
      obtain ⟨hh, hrel⟩ := (LceP.andB_iff _ _).1 hw
      have hr := hRT _ (LceP.blt_true hh)
      exact LceP.wRel_sound gen hinv hrel hr.1 hr.2
    · have hb2 : Nat.beq (McL.Lab.wKind (WT k')) (nat_lit 2) = false := by rw [h3]; rfl
      have hb3 : Nat.beq (McL.Lab.wKind (WT k')) (nat_lit 3) = true := by rw [h3]; rfl
      rw [hb2, hb3] at hw
      obtain ⟨hh, hsub⟩ := (LceP.andB_iff _ _).1 hw
      have hh' := LceP.blt_true hh
      rw [hK] at hh'
      have h0 : McL.Lab.wHint (WT k') = 0 := by omega
      refine ⟨h0, ?_⟩
      rw [LceP.wSub_sound gen hsub, h0]
  have hG0 : MGood gen c0 d lw lm FB rw INV nC S0 := by
    rw [hS0]
    exact MGood_mkS gen c0 d lw lm (by norm_num) le_rfl
      (fun _ => ⟨fun _ => 1, rfl, fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩)
  have hG1 := mruns_good gen c0 d lw lm hd hinv hW hn hSL hlw hlm hc0 Cs S0 hG0
  rw [Nat.eq_of_beq_eq_true hfacts, hS1] at hG1
  have hnF2 : nF < 4294967296 := by simpa using hnF
  have hL : ∃ rep : ℕ → G, rep 0 = 1 ∧ MRefs gen c0 d lw lm FB rw INV nC rep nF := by
    rcases hG1 with h0 | ⟨-, rep, hrep0, hrefs⟩
    · rw [mmkS_eq nC hnF2] at h0
      have h0' : nF = 0 := by omega
      exact ⟨fun _ => 1, rfl, fun h hh => absurd hh (by omega)⟩
    · have e1 : McL.Lab.sI (McL.Lab.mkS nF nC) = nF := by
        rw [msI_eq, mmkS_eq nC hnF2]
        omega
      rw [e1] at hrefs
      exact ⟨rep, hrep0, hrefs rep fun _ _ => rfl⟩
  obtain ⟨rep, hrep0, hrefs⟩ := hL
  have hT := truns_good Ts T0 (Or.inr fun k hk => by rw [hT0] at hk; omega)
    (FB := FB) (TW := TW) (TL := TL) (rw := rw) (d := d) (lw := lw) (lm := lm) (nF := nF)
  rw [Nat.eq_of_beq_eq_true htg, hT1] at hT
  rcases hT with h0 | hT
  · omega
  intro k hk hTL
  obtain ⟨J, hJ⟩ := hT k (by omega)
  unfold McL.Lab.targetOK at hJ
  simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at hJ
  obtain ⟨hn0, hres1, hres2⟩ := hJ
  set e := TW k
  set n' := LceS.wLen e
  set W' := Nat.lor (LceS.wWord e) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) n'))
  have hstart := WM_start gen c0 d rep (s := 0) W' n' 1 0 hd (by norm_num)
  obtain ⟨st', A', heq, hA', hWM⟩ := trace_go gen c0 d lw lm hd hinv hrefs n' le_rfl J _ _
    (by rw [Nat.sub_self]; exact hstart)
  have hlt : A' < 2 ^ lw := by rw [hlw, pow_mul]; norm_num; exact hA'
  obtain ⟨r1, r2⟩ := res_spec lw hlt (st := st')
  rw [heq, r1] at hres1
  rw [heq, hlm, r2, hTL] at hres2
  rcases hWM with hdead | ⟨cur, hcur, hst, hX⟩
  · exfalso
    rw [hres1] at hdead
    omega
  have hc : cur = 0 := by omega
  rcases hX with ⟨-, j, hj, hE⟩ | ⟨hlt', -⟩
  swap
  · exact absurd hlt' (lt_irrefl _)
  rw [hc, hrep0, one_mul, inv_one, mul_one] at hE
  have hbW : LceP.bv gen W' n' = bval gen (LceS.wWord e) n' := by
    rw [bv_mod gen W' n']
    change _ = LceP.bv gen (LceS.wWord e) n'
    rw [bv_mod gen (LceS.wWord e) n']
    congr 1
    change (LceS.wWord e ||| 1 <<< (8 * n')) % 256 ^ n' = _
    rw [← LceP.two_pow_eight_mul, Nat.or_mod_two_pow, Nat.one_shiftLeft, Nat.mod_self, Nat.or_zero]
  change bval gen (LceS.wWord e) n' = 1
  rw [← hbW, hE]
  by_cases hP : P
  · rw [hc0 hP]
    rcases hP with ⟨rfl, hn0'⟩ | ⟨rfl, rfl⟩
    · have h0 := hj 0 hn0'
      rw [hres2, pget_pid hd hn0'] at h0
      unfold sh at h0
      have h1 : (0 : ℤ) ≤ ((0 : ℕ) + j) % (n : ℤ) := Int.emod_nonneg _ (by omega)
      have h2 : ((0 : ℕ) + j) % (n : ℤ) = 0 := by omega
      rw [Nat.cast_zero, zero_add] at h2
      obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero h2
      rw [hq, zpow_mul, zpow_natCast, hcn, one_zpow]
    · rw [pow_one] at hcn
      rw [hcn, one_zpow]
  · simp only [hc0def, hP, ↓reduceIte, one_zpow]

private theorem fold6_congr {f g : ℕ → ℕ} : ∀ d, (∀ i < d, f i = g i) → fold6 f d = fold6 g d
  | 0, _ => rfl
  | d + 1, h => by
    change fold6 f d ||| f d <<< (6 * d) = fold6 g d ||| g d <<< (6 * d)
    rw [fold6_congr d (fun i hi => h i (by omega)), h d (by omega)]

private theorem fold6_self (p : ℕ) : ∀ d, fold6 (fun i => McL.pget p i) d = p % 64 ^ d
  | 0 => by
    rw [pow_zero, Nat.mod_one]
    rfl
  | d + 1 => by
    have hlt : fold6 (fun i => McL.pget p i) d < 2 ^ (6 * d) := by
      rw [pow_mul]
      norm_num
      exact (fold6_spec _ d (fun _ _ => pget_lt _ _)).1
    have e : fold6 (fun i => McL.pget p i) (d + 1) =
        fold6 (fun i => McL.pget p i) d + McL.pget p d * 64 ^ d := by
      change fold6 _ d ||| McL.pget p d <<< (6 * d) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, pow_mul,
        Nat.add_comm]
      norm_num
    rw [e, fold6_self p d, pget_eq, Nat.mod_pow_succ]
    ring

private theorem perm_ext {d p q : ℕ} (hp : p < 64 ^ d) (hq : q < 64 ^ d)
    (h : ∀ i < d, McL.pget p i = McL.pget q i) : p = q := by
  rw [← Nat.mod_eq_of_lt hp, ← Nat.mod_eq_of_lt hq, ← fold6_self, ← fold6_self]
  exact fold6_congr d h

private theorem canon_iff {d p : ℕ} : Nat.shiftRight p (Nat.mul 6 d) = 0 ↔ p < 64 ^ d := by
  rw [LceP.shr_eq, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  change p < 2 ^ (6 * d) ↔ _
  rw [pow_mul]
  norm_num

private theorem pairOK_full {d p q : ℕ} (h : McL.pairOK d p q = true) :
    p < 64 ^ d ∧ q < 64 ^ d ∧ (∀ i < d, McL.pget p i < d) ∧ (∀ i < d, McL.pget q i < d) ∧
      McL.pmul d p q = McL.pid d := by
  have h' := h
  unfold McL.pairOK at h'
  simp only [LceP.andB_iff, Nat.beq_eq] at h'
  obtain ⟨hp, hq, -, hr, -⟩ := h'
  obtain ⟨hm, hpr⟩ := pairOK_spec h
  unfold McL.inRange at hr
  refine ⟨canon_iff.1 hp, canon_iff.1 hq, hpr, fun i hi => ?_, hm⟩
  exact LceP.blt_true ((LceP.allRec_iff (fun i => Nat.blt (McL.pget q i) d) d).1 hr i hi)

private theorem pair_surj {d p q : ℕ} (hd : d ≤ 64) (h : McL.pairOK d p q = true) :
    ∀ x < d, ∃ i < d, McL.pget p i = x := by
  obtain ⟨-, -, hpr, -, hm⟩ := pairOK_full h
  let f : Fin d → Fin d := fun i => ⟨McL.pget p i.val, hpr i.val i.isLt⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact pair_inj hd hm a.isLt b.isLt (congrArg Fin.val hab)
  intro x hx
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x, hx⟩
  exact ⟨i.val, i.isLt, congrArg Fin.val hi⟩

private theorem pair_inv {d p q : ℕ} (hd : d ≤ 64) (h : McL.pairOK d p q = true) :
    (∀ i < d, McL.pget q (McL.pget p i) = i) ∧ ∀ x < d, McL.pget p (McL.pget q x) = x := by
  obtain ⟨-, -, -, -, hm⟩ := pairOK_full h
  have h1 : ∀ i < d, McL.pget q (McL.pget p i) = i := fun i hi => by
    have := congrArg (fun r => McL.pget r i) hm
    rwa [pget_pmul d p q hi, pget_pid hd hi] at this
  refine ⟨h1, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := pair_surj hd h x hx
  rw [h1 i hi]

private theorem pair_unique {d p q q' : ℕ} (hd : d ≤ 64) (h : McL.pairOK d p q = true)
    (h' : McL.pairOK d p q' = true) : q = q' := by
  obtain ⟨-, hq, -⟩ := pairOK_full h
  obtain ⟨-, hq', -⟩ := pairOK_full h'
  refine perm_ext hq hq' fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := pair_surj hd h x hx
  rw [(pair_inv hd h).1 i hi, (pair_inv hd h').1 i hi]

private theorem pmul_assoc' {d X Y Z : ℕ} (hX : ∀ i < d, McL.pget X i < d) :
    McL.pmul d (McL.pmul d X Y) Z = McL.pmul d X (McL.pmul d Y Z) := by
  rw [pmul_eq d (McL.pmul d X Y) Z, pmul_eq d X (McL.pmul d Y Z)]
  refine fold6_congr d fun i hi => ?_
  rw [pget_pmul d X Y hi, pget_pmul d Y Z (hX i hi)]

private theorem pmul_pid {d X : ℕ} (hd : d ≤ 64) (hX : X < 64 ^ d) (hXr : ∀ i < d, McL.pget X i < d) :
    McL.pmul d X (McL.pid d) = X := by
  refine perm_ext (pmul_lt _ _ _) hX fun i hi => ?_
  rw [pget_pmul d X _ hi, pget_pid hd (hXr i hi)]

section ThmB

variable {G : Type*} [Group G] (gen ψ : ℕ → G) (I : Set ℕ) (d lw lm : ℕ)

private def ModelI : Prop :=
  (McL.pid d ∈ I ∧ ψ (McL.pid d) = 1) ∧
    (∀ p ∈ I, ∀ q ∈ I, McL.pmul d p q ∈ I ∧ ψ (McL.pmul d p q) = ψ p * ψ q) ∧
    (∀ p ∈ I, McL.Sub.pinv d p ∈ I ∧ ψ (McL.Sub.pinv d p) = (ψ p)⁻¹) ∧
    (∀ p ∈ I, McL.pairOK d p (McL.Sub.pinv d p) = true)

private theorem model_inv {p q : ℕ} (hd : d ≤ 64) (hM : ModelI ψ I d) (hp : p ∈ I)
    (h : McL.pairOK d p q = true) : q ∈ I ∧ ψ q = (ψ p)⁻¹ := by
  obtain ⟨-, -, hinv, hval⟩ := hM
  rw [pair_unique hd h (hval p hp)]
  exact hinv p hp

private theorem model_range {p : ℕ} (hM : ModelI ψ I d) (hp : p ∈ I) :
    p < 64 ^ d ∧ ∀ i < d, McL.pget p i < d := by
  obtain ⟨h1, -, h3, -, -⟩ := pairOK_full (hM.2.2.2 p hp)
  exact ⟨h1, h3⟩

private theorem model_solve {B C L T : ℕ} (hd : d ≤ 64) (hM : ModelI ψ I d) (hB : B ∈ I)
    (hC : C ∈ I) (hT : T ∈ I) (hL : L < 64 ^ d) (hLr : ∀ i < d, McL.pget L i < d)
    (hE : T = McL.pmul d (McL.pmul d B L) C) :
    L ∈ I ∧ ψ L = (ψ B)⁻¹ * ψ T * (ψ C)⁻¹ := by
  obtain ⟨-, hmul, hinv, hval⟩ := hM
  set Bi := McL.Sub.pinv d B
  set Ci := McL.Sub.pinv d C
  have hBr := (pair_inv hd (hval B hB)).2
  have hCl := (pair_inv hd (hval C hC)).1
  have hBir := (pairOK_full (hval B hB)).2.2.2.1
  have e : L = McL.pmul d (McL.pmul d Bi T) Ci := by
    refine perm_ext hL (pmul_lt _ _ _) fun i hi => ?_
    rw [pget_pmul d _ _ hi, pget_pmul d _ _ hi, hE, pget_pmul d _ _ (hBir i hi),
      pget_pmul d _ _ (hBir i hi), hBr i hi, hCl _ (hLr i hi)]
  obtain ⟨hBi, hBiψ⟩ := hinv B hB
  obtain ⟨hCi, hCiψ⟩ := hinv C hC
  obtain ⟨h1, h1ψ⟩ := hmul Bi hBi T hT
  obtain ⟨h2, h2ψ⟩ := hmul _ h1 Ci hCi
  rw [e]
  exact ⟨h2, by rw [h2ψ, h1ψ, hBiψ, hCiψ]⟩

private def BRefs (FB : ℕ → ℕ) (rw INV nC : ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, McL.Lab.recOK INV d lw lm nC (McL.Lab.fct FB rw h) = true ∧
    McL.Lab.rlab lm (McL.Lab.fct FB rw h) ∈ I ∧
    elM gen rep (McL.Lab.fct FB rw h) = ψ (McL.Lab.rlab lm (McL.Lab.fct FB rw h))

private def WB (rep : ℕ → G) (s W ft : ℕ) (u : G) (L p st A : ℕ) : Prop :=
  A < 64 ^ d ∧ (st / 1048576 = 0 ∨ ∃ cur < 1048576, st = cur + 1048576 * (W / 256 ^ p) ∧
    ((p ≤ ft ∧ A ∈ I ∧ rep s * LceP.bv gen W p * (rep cur)⁻¹ = ψ A) ∨
      (ft < p ∧ ∃ B ∈ I, ∃ C ∈ I, A = McL.pmul d (McL.pmul d B L) C ∧
        ψ B * u * ψ C = rep s * LceP.bv gen W p * (rep cur)⁻¹)))

private theorem WB_start (rep : ℕ → G) {s : ℕ} (W ft : ℕ) (u : G) (L : ℕ) (hd : d ≤ 64)
    (hM : ModelI ψ I d) (hs : s < 1048576) :
    WB gen ψ I d rep s W ft u L 0 (wStart s W) (McL.pid d) := by
  refine ⟨pid_lt hd, Or.inr ⟨s, hs, ?_, Or.inl ⟨Nat.zero_le _, hM.1.1, ?_⟩⟩⟩
  · unfold wStart
    rw [LceP.lor20 _ hs, pow_zero, Nat.div_one]
    ring
  · rw [LceP.bv_zero, mul_one, mul_inv_cancel, hM.1.2]

private theorem WB_ext {rep : ℕ → G} {s W ft : ℕ} {u : G} {L p A cur cur' l : ℕ}
    (hM : ModelI ψ I d) (hLr : ∀ i < d, McL.pget L i < d) (hp : p ≠ ft)
    (hX : (p ≤ ft ∧ A ∈ I ∧ rep s * LceP.bv gen W p * (rep cur)⁻¹ = ψ A) ∨
      (ft < p ∧ ∃ B ∈ I, ∃ C ∈ I, A = McL.pmul d (McL.pmul d B L) C ∧
        ψ B * u * ψ C = rep s * LceP.bv gen W p * (rep cur)⁻¹))
    (hl : l ∈ I) (he : rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹ = ψ l) :
    (p + 1 ≤ ft ∧ McL.pmul d A l ∈ I ∧
        rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ = ψ (McL.pmul d A l)) ∨
      (ft < p + 1 ∧ ∃ B ∈ I, ∃ C ∈ I, McL.pmul d A l = McL.pmul d (McL.pmul d B L) C ∧
        ψ B * u * ψ C = rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹) := by
  have e : rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ =
      (rep s * LceP.bv gen W p * (rep cur)⁻¹) * (rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹) := by
    rw [LceP.bv_succ]
    group
  have hmul := hM.2.1
  rcases hX with ⟨hp', hA, hE⟩ | ⟨hp', B, hB, C, hC, hA, hE⟩
  · obtain ⟨h1, h2⟩ := hmul A hA l hl
    exact Or.inl ⟨by omega, h1, by rw [e, hE, he, h2]⟩
  · obtain ⟨h1, h2⟩ := hmul C hC l hl
    have hBr := (model_range ψ I d hM hB).2
    refine Or.inr ⟨by omega, B, hB, McL.pmul d C l, h1, ?_, ?_⟩
    · rw [hA, pmul_assoc' (fun i hi => by rw [pget_pmul d B L hi]; exact hLr _ (hBr i hi))]
    · rw [e, ← hE, he, h2]
      group

private theorem WB_ref {FB : ℕ → ℕ} {rw INV INV8 L nC i : ℕ} (hd : d ≤ 64) (hM : ModelI ψ I d)
    (hinv : LceS.invOK INV INV8 L = true) {rep : ℕ → G} {s W ft : ℕ} {u : G} {Lb p st A : ℕ}
    (hLr : ∀ i < d, McL.pget Lb i < d)
    (e : ℕ) (k : ℕ → ℕ → ℕ) (hrefs : BRefs gen ψ I d lw lm FB rw INV nC rep i) (hp : p ≠ ft)
    (hI : WB gen ψ I d rep s W ft u Lb p st A) :
    ∃ st' A', McL.Lab.refStep FB rw d lw lm i e st A k = k st' A' ∧
      WB gen ψ I d rep s W ft u Lb (p + 1) st' A' := by
  unfold McL.Lab.refStep
  rw [LceP.brec_eq]
  split_ifs with hh
  · rw [Nat.blt_eq] at hh
    simp only [LceP.strictN_eq]
    obtain ⟨hrec, hlI, hel⟩ := hrefs _ hh
    set R := McL.Lab.fct FB rw (Nat.shiftRight e (nat_lit 1))
    obtain ⟨-, -, -, hpair⟩ := mrec_spec hrec
    obtain ⟨hliI, hliψ⟩ := model_inv ψ I d hd hM hlI hpair
    have hlv := mlv_ric gen hinv hrec
    rw [LceP.brec_eq]
    split_ifs with hdir
    · refine ⟨_, _, rfl, pmul_lt _ _ _, ?_⟩
      rcases hI with ⟨-, hdead | ⟨cur, hcur, hst, hX⟩⟩
      · left
        rcases msB_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := rx_lt R
          omega
      · rcases msB_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := mbwd hcur hst hm
          refine ⟨McL.Lab.rx R, rx_lt R, by rw [h1, hs], ?_⟩
          refine WB_ext gen ψ I d hM hLr hp hX hliI ?_
          rw [hw, hlv, hc, hliψ, ← hel]
          unfold elM
          group
    · refine ⟨_, _, rfl, pmul_lt _ _ _, ?_⟩
      rcases hI with ⟨-, hdead | ⟨cur, hcur, hst, hX⟩⟩
      · left
        rcases msF_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := ry_lt R
          omega
      · rcases msF_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := mfwd hcur hst hm
          refine ⟨McL.Lab.ry R, ry_lt R, by rw [h1, hs], ?_⟩
          refine WB_ext gen ψ I d hM hLr hp hX hlI ?_
          rw [hw, hc, ← hel]
          rfl
  · exact ⟨0, A, rfl, hI.1, Or.inl rfl⟩

private theorem WB_own {rep : ℕ → G} {s W ft Ri p st A : ℕ} (hd : d ≤ 64) (hM : ModelI ψ I d)
    (hp : p = ft) (hLr : ∀ y < d, McL.pget (McL.Lab.rlab lm Ri) y < d)
    (hI : WB gen ψ I d rep s W ft (elM gen rep Ri) (McL.Lab.rlab lm Ri) p st A) :
    WB gen ψ I d rep s W ft (elM gen rep Ri) (McL.Lab.rlab lm Ri) (p + 1) (McL.Lab.sF Ri st)
      (McL.pmul d A (McL.Lab.rlab lm Ri)) := by
  refine ⟨pmul_lt _ _ _, ?_⟩
  rcases hI with ⟨-, hdead | ⟨cur, hcur, hst, hX⟩⟩
  · left
    rcases msF_cases Ri st with h0 | ⟨hm, h1⟩
    · rw [h0]
    · rw [h1]
      have := ry_lt Ri
      omega
  · rcases msF_cases Ri st with h0 | ⟨hm, h1⟩
    · left
      rw [h0]
    · right
      obtain ⟨hc, hw, hs⟩ := mfwd hcur hst hm
      refine ⟨McL.Lab.ry Ri, ry_lt Ri, by rw [h1, hs], Or.inr ⟨by omega, ?_⟩⟩
      rcases hX with ⟨-, hA, hE⟩ | ⟨hlt, -⟩
      · obtain ⟨hAlt, hAr⟩ := model_range ψ I d hM hA
        refine ⟨A, hA, McL.pid d, hM.1.1, ?_, ?_⟩
        · rw [pmul_pid hd (pmul_lt _ _ _) fun i hi => by rw [pget_pmul d A _ hi]; exact hLr _ (hAr i hi)]
        · rw [hc] at hE
          rw [hM.1.2, mul_one, LceP.bv_succ, hw]
          have e : rep s * (LceP.bv gen W p * LceP.lv gen (McL.Lab.rc Ri)) *
              (rep (McL.Lab.ry Ri))⁻¹ = (rep s * LceP.bv gen W p * (rep (McL.Lab.rx Ri))⁻¹) *
              elM gen rep Ri := by
            unfold elM
            group
          rw [e, hE]
      · omega

private theorem walk_goB {FB : ℕ → ℕ} {rw INV INV8 L nC i : ℕ} (hd : d ≤ 64) (hM : ModelI ψ I d)
    (hinv : LceS.invOK INV INV8 L = true) {rep : ℕ → G} {s W Ri ft n : ℕ}
    (hrefs : BRefs gen ψ I d lw lm FB rw INV nC rep i)
    (hLr : ∀ y < d, McL.pget (McL.Lab.rlab lm Ri) y < d) :
    ∀ k ≤ n, ∀ J st A, WB gen ψ I d rep s W ft (elM gen rep Ri) (McL.Lab.rlab lm Ri) (n - k) st A →
      ∃ st' A', McL.Lab.walkGo FB rw d lw lm i Ri ft n k J st A =
          Nat.lor A' (Nat.shiftLeft st' lw) ∧
        WB gen ψ I d rep s W ft (elM gen rep Ri) (McL.Lab.rlab lm Ri) n st' A'
  | 0, _, J, st, A, hI => ⟨st, A, rfl, by rw [Nat.sub_zero] at hI; exact hI⟩
  | k + 1, hk, J, st, A, hI => by
    change ∃ st' A', Bool.rec (motive := fun _ => ℕ)
      (McL.Lab.refStep FB rw d lw lm i (Nat.land J 4294967295) st A
        (McL.Lab.walkGo FB rw d lw lm i Ri ft n k (Nat.shiftRight J 32)))
      (CFSG.KC.Loop.strictN (McL.Lab.sF Ri st) (fun st' => CFSG.KC.Loop.strictN
        (McL.pmul d A (McL.Lab.rlab lm Ri)) (McL.Lab.walkGo FB rw d lw lm i Ri ft n k J st')))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft) = _ ∧ _
    have e : n - k = n - (k + 1) + 1 := by omega
    cases hb : Nat.beq (Nat.sub n (Nat.succ k)) ft
    · dsimp only
      have hp : n - (k + 1) ≠ ft := by
        intro h
        have h2 : Nat.beq (Nat.sub n (Nat.succ k)) ft = true := by
          rw [Nat.beq_eq]
          exact h
        rw [hb] at h2
        exact Bool.false_ne_true h2
      obtain ⟨st1, A1, h1, hI1⟩ := WB_ref gen ψ I d lw lm hd hM hinv hLr (Nat.land J 4294967295)
        (McL.Lab.walkGo FB rw d lw lm i Ri ft n k (Nat.shiftRight J 32)) hrefs hp hI
      rw [h1]
      exact walk_goB hd hM hinv hrefs hLr k (by omega) _ _ _ (by rw [e]; exact hI1)
    · dsimp only
      rw [LceP.strictN_eq, LceP.strictN_eq]
      exact walk_goB hd hM hinv hrefs hLr k (by omega) _ _ _
        (by rw [e]; exact WB_own gen ψ I d lm hd hM (Nat.eq_of_beq_eq_true hb) hLr hI)

private theorem trace_goB {FB : ℕ → ℕ} {rw INV INV8 L nC i : ℕ} (hd : d ≤ 64) (hM : ModelI ψ I d)
    (hinv : LceS.invOK INV INV8 L = true) {rep : ℕ → G} {s W n : ℕ} {u : G}
    (hrefs : BRefs gen ψ I d lw lm FB rw INV nC rep i) :
    ∀ k ≤ n, ∀ J st A, WB gen ψ I d rep s W n u (McL.pid d) (n - k) st A →
      ∃ st' A', McL.Lab.traceGo FB rw d lw lm i k J st A = Nat.lor A' (Nat.shiftLeft st' lw) ∧
        WB gen ψ I d rep s W n u (McL.pid d) n st' A'
  | 0, _, J, st, A, hI => ⟨st, A, rfl, by rw [Nat.sub_zero] at hI; exact hI⟩
  | k + 1, hk, J, st, A, hI => by
    change ∃ st' A', McL.Lab.refStep FB rw d lw lm i (Nat.land J 4294967295) st A
      (McL.Lab.traceGo FB rw d lw lm i k (Nat.shiftRight J 32)) = _ ∧ _
    obtain ⟨st1, A1, h1, hI1⟩ := WB_ref gen ψ I d lw lm hd hM hinv
      (fun y hy => by rw [pget_pid hd hy]; exact hy) (Nat.land J 4294967295)
      (McL.Lab.traceGo FB rw d lw lm i k (Nat.shiftRight J 32)) hrefs (by omega) hI
    rw [h1]
    exact trace_goB hd hM hinv hrefs k (by omega) _ _ _
      (by rw [show n - k = n - (k + 1) + 1 by omega]; exact hI1)

private def BInv (FB : ℕ → ℕ) (rw INV nC i N : ℕ) : Prop :=
  ∃ rep : ℕ → G, rep 0 = 1 ∧ ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) →
    BRefs gen ψ I d lw lm FB rw INV nC rep' i

private def BGood (FB : ℕ → ℕ) (rw INV nC S : ℕ) : Prop :=
  S = 0 ∨ (1 ≤ McL.Lab.sN S ∧ BInv gen ψ I d lw lm FB rw INV nC (McL.Lab.sI S) (McL.Lab.sN S))

private theorem BGood_mkS {FB : ℕ → ℕ} {rw INV nC i N : ℕ} (hi : i ≤ 4294967296) (hN : 1 ≤ N)
    (hF : i < 4294967296 → BInv gen ψ I d lw lm FB rw INV nC i N) :
    BGood gen ψ I d lw lm FB rw INV nC (McL.Lab.mkS i N) := by
  right
  rcases Nat.lt_or_ge i 4294967296 with hlt | hge
  · rw [msN_eq, msI_eq, mmkS_eq N hlt]
    have e1 : (i + N * 4294967296) / 4294967296 = N := by omega
    have e2 : (i + N * 4294967296) % 4294967296 = i := by omega
    rw [e1, e2]
    exact ⟨hN, hF hlt⟩
  · have hi' : i = 4294967296 := by omega
    subst hi'
    have e : McL.Lab.mkS 4294967296 N = (1 ||| N) * 4294967296 := by
      change (1 <<< 32) ||| (N <<< 32) = _
      rw [← Nat.shiftLeft_or_distrib, Nat.shiftLeft_eq]
    rw [msN_eq, msI_eq, e, Nat.mul_div_cancel _ (by norm_num), Nat.mul_mod_left]
    exact ⟨le_trans (by norm_num) Nat.left_le_or,
      ⟨fun _ => 1, rfl, fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩⟩

private def BWords (SL WT : ℕ → ℕ) : Prop :=
  ∀ id < 65536, WT id = 0 ∨
    ((McL.Lab.wKind (WT id) = 2 →
        LceP.bv gen (McL.Lab.wWord (WT id)) (McL.Lab.wLen (WT id)) = 1) ∧
      (McL.Lab.wKind (WT id) = 3 → SL (McL.Lab.wHint (WT id)) ∈ I ∧
        LceP.bv gen (McL.Lab.wWord (WT id)) (McL.Lab.wLen (WT id)) = ψ (SL (McL.Lab.wHint (WT id)))))

private theorem bfactStep_good {FB WT SL : ℕ → ℕ} {INV INV8 rw nC L : ℕ} (hd : d ≤ 64)
    (hM : ModelI ψ I d) (hinv : LceS.invOK INV INV8 L = true) (hW : BWords gen ψ I SL WT)
    (hlw : lw = 6 * d) (hlm : lm = 2 ^ lw - 1) {S J w : ℕ}
    (hS : BGood gen ψ I d lw lm FB rw INV nC S)
    (hw : Nat.land J 1 = 1 → ∃ id < 65536, w = WT id) :
    BGood gen ψ I d lw lm FB rw INV nC (McL.Lab.factStep FB SL INV rw d lw lm nC L J S w) := by
  unfold McL.Lab.factStep
  dsimp only
  rcases hS with h0 | ⟨hN, rep, hrep0, hrefs⟩
  · left
    rw [h0]
    rfl
  set i := McL.Lab.sI S with hidef
  set N := McL.Lab.sN S with hNdef
  have hS0 : Nat.blt (nat_lit 0) S = true := by
    rw [Nat.blt_eq]
    change 0 < S
    have : S / 4294967296 ≥ 1 := by rw [← msN_eq]; exact hN
    omega
  rw [hS0]
  dsimp only
  set R := McL.Lab.fct FB rw i
  cases hJ : Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)
  ·
    dsimp only
    cases ht : McL.Lab.treeOK INV d lw lm nC L N R
    · left
      rfl
    dsimp only
    refine BGood_mkS gen ψ I d lw lm (Nat.succ_le_of_lt (msI_lt S)) (by omega) fun _ => ?_
    unfold McL.Lab.treeOK at ht
    simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at ht
    obtain ⟨hrR, hry, hrx, -, hl1, -⟩ := ht
    refine ⟨Function.update rep N (rep (McL.Lab.rx R) * LceP.lv gen (McL.Lab.rc R)), ?_,
      fun rep' hag h hh => ?_⟩
    · rw [Function.update_of_ne (show (0 : ℕ) ≠ N by omega)]
      exact hrep0
    have hag' : ∀ k < N, rep' k = rep k := by
      intro k hk
      rw [hag k (by omega), Function.update_of_ne (show k ≠ N by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag' h hh
    · refine ⟨hrR, by rw [hl1]; exact hM.1.1, ?_⟩
      unfold elM
      rw [hry, hag N (by omega), Function.update_self, hag' _ hrx, mul_inv_cancel, hl1, hM.1.2]
  ·
    dsimp only
    obtain ⟨id, hid, rfl⟩ := hw (Nat.eq_of_beq_eq_true hJ)
    set w := WT id
    set fs := Nat.land (Nat.shiftRight J (nat_lit 17)) McL.Lab.m20
    set ft := Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)
    cases hwk : McL.Lab.walkOK FB SL INV rw d lw lm nC i R w fs ft J
    · left
      rfl
    dsimp only
    refine BGood_mkS gen ψ I d lw lm (Nat.succ_le_of_lt (msI_lt S)) hN fun _ => ?_
    refine ⟨rep, hrep0, fun rep' hag h hh => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag h hh
    unfold McL.Lab.walkOK at hwk
    simp only [LceP.andB_iff, LceP.orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hwk
    obtain ⟨hrec, hft, hkind, hres1, hres2⟩ := hwk
    obtain ⟨-, -, -, hpair⟩ := mrec_spec hrec
    obtain ⟨hLlt, -, hLr, -, -⟩ := pairOK_full hpair
    have hfs : fs < 1048576 := by
      change Nat.land (Nat.shiftRight J 17) 1048575 < 1048576
      rw [LceP.land20]
      omega
    have hrefs' := hrefs rep' hag
    have hstart := WB_start gen ψ I d rep' (McL.Lab.wWord w) ft (elM gen rep' R)
      (McL.Lab.rlab lm R) hd hM hfs
    obtain ⟨st', A', heq, hA', hWB⟩ := walk_goB gen ψ I d lw lm hd hM hinv hrefs' hLr
      (McL.Lab.wLen w) le_rfl (Nat.shiftRight J 53) _ _ (by rw [Nat.sub_self]; exact hstart)
    have hlt : A' < 2 ^ lw := by rw [hlw, pow_mul]; norm_num; exact hA'
    obtain ⟨r1, r2⟩ := res_spec lw hlt (st := st')
    rw [heq, r1] at hres1
    rw [heq, hlm, r2] at hres2
    rcases hWB with hdead | ⟨cur, hcur, hst, hX⟩
    · exfalso
      omega
    have hc : cur = fs := by omega
    rcases hX with ⟨hle, -⟩ | ⟨-, B, hB, C, hC, hAe, hE⟩
    · exfalso
      omega
    rw [hc] at hE
    rcases hW id hid with hw0 | ⟨hk2, hk3⟩
    · exfalso
      have hw0' : w = 0 := hw0
      rw [hw0'] at hkind
      rcases hkind with h | ⟨h, -⟩ <;> exact absurd h (by decide)
    rcases hkind with hkd | ⟨hkd, hfs0⟩
    ·
      have htg : McL.Lab.wTarget SL d w = McL.pid d := by
        unfold McL.Lab.wTarget
        rw [show Nat.beq (McL.Lab.wKind w) (nat_lit 3) = false by rw [hkd]; rfl]
      rw [htg] at hres2
      obtain ⟨hLI, hLψ⟩ := model_solve ψ I d hd hM hB hC hM.1.1 hLlt hLr (by rw [← hres2, hAe])
      refine ⟨hrec, hLI, ?_⟩
      have hb := hk2 hkd
      rw [hb, mul_one, mul_inv_cancel] at hE
      rw [hLψ, hM.1.2, mul_one]
      calc elM gen rep' R = (ψ B)⁻¹ * (ψ B * elM gen rep' R * ψ C) * (ψ C)⁻¹ := by group
        _ = (ψ B)⁻¹ * (ψ C)⁻¹ := by rw [hE]; group
    ·
      obtain ⟨hSLI, hb⟩ := hk3 hkd
      have htg : McL.Lab.wTarget SL d w = SL (McL.Lab.wHint w) := by
        unfold McL.Lab.wTarget
        rw [show Nat.beq (McL.Lab.wKind w) (nat_lit 3) = true by rw [hkd]; rfl]
      rw [htg] at hres2
      obtain ⟨hLI, hLψ⟩ := model_solve ψ I d hd hM hB hC hSLI hLlt hLr (by rw [← hres2, hAe])
      refine ⟨hrec, hLI, ?_⟩
      have h0 : rep' 0 = 1 := by rw [hag 0 (by omega), hrep0]
      rw [hfs0, h0, one_mul, inv_one, mul_one, hb] at hE
      rw [hLψ]
      calc elM gen rep' R = (ψ B)⁻¹ * (ψ B * elM gen rep' R * ψ C) * (ψ C)⁻¹ := by group
        _ = (ψ B)⁻¹ * ψ (SL (McL.Lab.wHint (WT id))) * (ψ C)⁻¹ := by rw [hE]

private theorem bchunk_good {FB WT SL : ℕ → ℕ} {INV INV8 rw nC L : ℕ} (hd : d ≤ 64)
    (hM : ModelI ψ I d) (hinv : LceS.invOK INV INV8 L = true) (hW : BWords gen ψ I SL WT)
    (hlw : lw = 6 * d) (hlm : lm = 2 ^ lw - 1) :
    ∀ k J S, BGood gen ψ I d lw lm FB rw INV nC S →
      BGood gen ψ I d lw lm FB rw INV nC (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
          (ih (Nat.shiftRight J (nat_lit 1)) (McL.Lab.factStep FB SL INV rw d lw lm nC L J S (nat_lit 0)))
          (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
            (nat_lit 65535)) WT) (fun w =>
            CFSG.KC.Loop.strictN (McL.Lab.factStep FB SL INV rw d lw lm nC L J S w)
              (ih (Nat.shiftRight J (McL.Lab.jLen J w)))))
          (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k J S)
  | 0, _, _, hS => hS
  | k + 1, J, S, hS => by
    dsimp only
    cases hJ : Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)
    · dsimp only
      apply bchunk_good hd hM hinv hW hlw hlm k
      refine bfactStep_good gen ψ I d lw lm hd hM hinv hW hlw hlm hS fun h1 => ?_
      rw [h1] at hJ
      exact absurd hJ (by decide)
    · dsimp only
      rw [LceP.strictN_eq, LceP.strictN_eq, LceP.strictN_eq]
      apply bchunk_good hd hM hinv hW hlw hlm k
      refine bfactStep_good gen ψ I d lw lm hd hM hinv hW hlw hlm hS fun _ => ?_
      refine ⟨_, ?_, rfl⟩
      change Nat.land (Nat.shiftRight J 1) 65535 < 65536
      rw [LceP.land_lit _ 16 65535 (by norm_num)]
      omega

private theorem bruns_good {FB WT SL : ℕ → ℕ} {INV INV8 rw nC L : ℕ} (hd : d ≤ 64)
    (hM : ModelI ψ I d) (hinv : LceS.invOK INV INV8 L = true) (hW : BWords gen ψ I SL WT)
    (hlw : lw = 6 * d) (hlm : lm = 2 ^ lw - 1) :
    ∀ (Cs : List ℕ) S, BGood gen ψ I d lw lm FB rw INV nC S →
      BGood gen ψ I d lw lm FB rw INV nC (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L Cs S)
  | [], _, hS => hS
  | C :: Cs, S, hS => by
    change BGood gen ψ I d lw lm FB rw INV nC (CFSG.KC.Loop.strictN
      (McL.Lab.runChunk FB WT SL INV rw d lw lm nC L C S)
      (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L Cs))
    rw [LceP.strictN_eq]
    exact bruns_good hd hM hinv hW hlw hlm Cs _
      (bchunk_good gen ψ I d lw lm hd hM hinv hW hlw hlm _ _ _ hS)

end ThmB

theorem targetsB_sound {G : Type*} [Group G] (gen ψ : ℕ → G) (I : Set ℕ)
    {FB WT SL RT ST TW TL : ℕ → ℕ}
    {INV INV8 rw d lw lm nC L R K m nF nT S0 S1 T0 T1 nF' : ℕ} {Cs Ts : List ℕ}
    (hid : McL.pid d ∈ I ∧ ψ (McL.pid d) = 1)
    (hmul : ∀ p ∈ I, ∀ q ∈ I, McL.pmul d p q ∈ I ∧ ψ (McL.pmul d p q) = ψ p * ψ q)
    (hinv' : ∀ p ∈ I, McL.Sub.pinv d p ∈ I ∧ ψ (McL.Sub.pinv d p) = (ψ p)⁻¹)
    (hval : ∀ p ∈ I, McL.pairOK d p (McL.Sub.pinv d p) = true)
    (hSL : ∀ j < K, SL j ∈ I ∧ ψ (SL j) = bval gen (LceS.wWord (ST j)) (LceS.wLen (ST j)))
    (hRT : ∀ r < R, LceS.wWord (RT r) < 2 ^ (8 * LceS.wLen (RT r)) ∧
      bval gen (LceS.wWord (RT r)) (LceS.wLen (RT r)) = 1)
    (hWT : ∀ k < 65536, WT k = 0 ∨ ∃ k' < m, WT k = WT k')
    (hwords : McL.Lab.wordsOK WT RT ST INV INV8 R K m = true)
    (hinv : LceS.invOK INV INV8 L = true)
    (hgeom : lw = 6 * d ∧ rw = 56 + 2 * lw ∧ lm = 2 ^ lw - 1) (hd : d ≤ 64) (hnC : nC ≤ 2 ^ 20)
    (hS0 : S0 = McL.Lab.mkS 0 1)
    (hfacts : Nat.beq (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L Cs S0) S1 = true)
    (hS1 : S1 = McL.Lab.mkS nF nC) (hnF : nF < 2 ^ 32)
    (htg : Nat.beq (McL.Lab.runTargets FB TW TL rw d lw lm nF' Ts T0) T1 = true)
    (hT0 : T0 = 1) (hT1 : T1 = nT + 1) (hnF' : nF' = nF) :
    ∀ k < nT, TL k ∈ I ∧ bval gen (LceS.wWord (TW k)) (LceS.wLen (TW k)) = ψ (TL k) := by
  have _hnC := hnC
  obtain ⟨hlw, -, hlm⟩ := hgeom
  subst nF'
  have hM : ModelI ψ I d := ⟨hid, hmul, hinv', hval⟩
  have hW : BWords gen ψ I SL WT := by
    intro id hid
    rcases hWT id hid with h0 | ⟨k', hk', hk⟩
    · exact Or.inl h0
    right
    rw [hk]
    have hw := (LceP.allRec_iff (fun w => McL.Lab.wordOK RT ST INV INV8 R K (WT w)) m).1 hwords k' hk'
    unfold McL.Lab.wordOK at hw
    refine ⟨fun h2 => ?_, fun h3 => ?_⟩
    · have hb : Nat.beq (McL.Lab.wKind (WT k')) (nat_lit 2) = true := by rw [h2]; rfl
      rw [hb] at hw
      obtain ⟨hh, hrel⟩ := (LceP.andB_iff _ _).1 hw
      have hr := hRT _ (LceP.blt_true hh)
      exact LceP.wRel_sound gen hinv hrel hr.1 hr.2
    · have hb2 : Nat.beq (McL.Lab.wKind (WT k')) (nat_lit 2) = false := by rw [h3]; rfl
      have hb3 : Nat.beq (McL.Lab.wKind (WT k')) (nat_lit 3) = true := by rw [h3]; rfl
      rw [hb2, hb3] at hw
      obtain ⟨hh, hsub⟩ := (LceP.andB_iff _ _).1 hw
      obtain ⟨hSI, hSψ⟩ := hSL _ (LceP.blt_true hh)
      refine ⟨hSI, ?_⟩
      rw [LceP.wSub_sound gen hsub, hSψ]
      rfl
  have hG0 : BGood gen ψ I d lw lm FB rw INV nC S0 := by
    rw [hS0]
    exact BGood_mkS gen ψ I d lw lm (by norm_num) le_rfl
      (fun _ => ⟨fun _ => 1, rfl, fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩)
  have hG1 := bruns_good gen ψ I d lw lm hd hM hinv hW hlw hlm Cs S0 hG0
  rw [Nat.eq_of_beq_eq_true hfacts, hS1] at hG1
  have hnF2 : nF < 4294967296 := by simpa using hnF
  have hL : ∃ rep : ℕ → G, rep 0 = 1 ∧ BRefs gen ψ I d lw lm FB rw INV nC rep nF := by
    rcases hG1 with h0 | ⟨-, rep, hrep0, hrefs⟩
    · rw [mmkS_eq nC hnF2] at h0
      have h0' : nF = 0 := by omega
      exact ⟨fun _ => 1, rfl, fun h hh => absurd hh (by omega)⟩
    · have e1 : McL.Lab.sI (McL.Lab.mkS nF nC) = nF := by
        rw [msI_eq, mmkS_eq nC hnF2]
        omega
      rw [e1] at hrefs
      exact ⟨rep, hrep0, hrefs rep fun _ _ => rfl⟩
  obtain ⟨rep, hrep0, hrefs⟩ := hL
  have hT := truns_good Ts T0 (Or.inr fun k hk => by rw [hT0] at hk; omega)
    (FB := FB) (TW := TW) (TL := TL) (rw := rw) (d := d) (lw := lw) (lm := lm) (nF := nF)
  rw [Nat.eq_of_beq_eq_true htg, hT1] at hT
  rcases hT with h0 | hT
  · omega
  intro k hk
  obtain ⟨J, hJ⟩ := hT k (by omega)
  unfold McL.Lab.targetOK at hJ
  simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at hJ
  obtain ⟨hn0, hres1, hres2⟩ := hJ
  set e := TW k
  set n' := LceS.wLen e
  set W' := Nat.lor (LceS.wWord e) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) n'))
  have hstart := WB_start gen ψ I d rep (s := 0) W' n' 1 (McL.pid d) hd hM (by norm_num)
  obtain ⟨st', A', heq, hA', hWB⟩ := trace_goB gen ψ I d lw lm hd hM hinv hrefs n' le_rfl J _ _
    (by rw [Nat.sub_self]; exact hstart)
  have hlt : A' < 2 ^ lw := by rw [hlw, pow_mul]; norm_num; exact hA'
  obtain ⟨r1, r2⟩ := res_spec lw hlt (st := st')
  rw [heq, r1] at hres1
  rw [heq, hlm, r2] at hres2
  rcases hWB with hdead | ⟨cur, hcur, hst, hX⟩
  · exfalso
    rw [hres1] at hdead
    omega
  have hc : cur = 0 := by omega
  rcases hX with ⟨-, hAI, hE⟩ | ⟨hlt', -⟩
  swap
  · exact absurd hlt' (lt_irrefl _)
  rw [hc, hrep0, one_mul, inv_one, mul_one] at hE
  rw [← hres2]
  refine ⟨hAI, ?_⟩
  have hbW : LceP.bv gen W' n' = bval gen (LceS.wWord e) n' := by
    rw [bv_mod gen W' n']
    change _ = LceP.bv gen (LceS.wWord e) n'
    rw [bv_mod gen (LceS.wWord e) n']
    congr 1
    change (LceS.wWord e ||| 1 <<< (8 * n')) % 256 ^ n' = _
    rw [← LceP.two_pow_eight_mul, Nat.or_mod_two_pow, Nat.one_shiftLeft, Nat.mod_self, Nat.or_zero]
  change bval gen (LceS.wWord e) n' = _
  rw [← hbW, hE]

end CFSG.Certificates.McLLab

end
