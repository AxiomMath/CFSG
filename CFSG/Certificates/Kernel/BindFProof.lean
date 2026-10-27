module

public import CFSG.Certificates.Kernel.BindByte
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Certificates.BindF

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates.LCE CFSG.Certificates.BindL

theorem xor1_lt {l : ℕ} (hl : l < 254) : l ^^^ 1 < 254 ∧ (l ^^^ 1) / 2 = l / 2 ∧
    (l ^^^ 1) % 2 = 1 - l % 2 := by
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · rw [Nat.xor_one_of_even (Nat.even_iff.2 h)]
    omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.2 h)]
    omega

theorem letV_xor1 {G : Type*} [Group G] (pg : ℕ → G) {l : ℕ} (hl : l < 254) :
    letV pg (l ^^^ 1) = (letV pg l)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := xor1_lt hl
  unfold letV
  rw [ite_eq_right (by omega : l ^^^ 1 ≠ 255), ite_eq_right (by omega : l ≠ 255), h2]
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · rw [h] at h3
    rw [ite_eq_right (by omega : ¬ (l ^^^ 1) % 2 = 0), ite_eq_left h]
  · rw [h] at h3
    rw [ite_eq_left (by omega : (l ^^^ 1) % 2 = 0), ite_eq_right (by omega : ¬ l % 2 = 0), inv_inv]

theorem kCnt_eqF (P : ℕ) : kCnt P = P % 65536 := by
  change P &&& (2 ^ 16 - 1) = P % 2 ^ 16
  exact Nat.and_two_pow_sub_one_eq_mod P 16

theorem kStk_eqF (P : ℕ) : kStk P = P / 65536 := by
  change P >>> 16 = P / 2 ^ 16
  exact Nat.shiftRight_eq_div_pow P 16

theorem mkK_eqF {c : ℕ} (s : ℕ) (hc : c < 65536) : mkK c s = s * 65536 + c := by
  change c ||| s <<< 16 = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by norm_num; exact hc), Nat.shiftLeft_eq]

theorem kCnt_mkKF {c : ℕ} (s : ℕ) (hc : c < 65536) : kCnt (mkK c s) = c := by
  rw [kCnt_eqF, mkK_eqF s hc]
  omega

theorem kStk_mkKF {c : ℕ} (s : ℕ) (hc : c < 65536) : kStk (mkK c s) = s := by
  rw [kStk_eqF, mkK_eqF s hc]
  omega

theorem byte_div256F (s i : ℕ) : s / 256 / 256 ^ i % 256 = s / 256 ^ (i + 1) % 256 := by
  rw [Nat.div_div_eq_div_mul, pow_succ']

theorem kByte_eqF (P i : ℕ) : kByte P i = kStk P / 256 ^ i % 256 := HO.wLet_eq (kStk P) i

section Stack

variable {G : Type*} [Group G] (pg : ℕ → G)

@[expose] def fval : ℕ → ℕ → G
  | _, 0 => 1
  | s, c + 1 => fval (s / 256) c * letV pg (s % 256 - 1)

theorem fval_succ (s c : ℕ) : fval pg s (c + 1) = fval pg (s / 256) c * letV pg (s % 256 - 1) := by
  rw [fval]

theorem fval_eq_prod : ∀ c s, fval pg s c =
    ((List.range c).map fun q => letV pg (s / 256 ^ (c - 1 - q) % 256 - 1)).prod
  | 0, s => rfl
  | c + 1, s => by
    rw [fval_succ, fval_eq_prod c (s / 256), List.range_succ, List.map_append, List.prod_append]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro q hq
      rw [List.mem_range] at hq
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      have e : c - 1 - q + 1 = c + 1 - 1 - q := by omega
      rw [e]
    · simp

@[expose] def SInvF (P : ℕ) : Prop :=
  kStk P < 256 ^ kCnt P ∧ ∀ i < kCnt P, 1 ≤ kStk P / 256 ^ i % 256 ∧ kStk P / 256 ^ i % 256 ≤ 254

theorem SInvF_zero : SInvF 0 := by
  refine ⟨?_, ?_⟩ <;> simp [kStk_eqF, kCnt_eqF]

@[expose] noncomputable def pvalF (P : ℕ) : G := fval pg (kStk P) (kCnt P)

theorem pushF_spec {P x : ℕ} (hI : SInvF P) (hx : x < 254) (hc : kCnt P + 1 < 65536) :
    SInvF (push 1 P x) ∧ kCnt (push 1 P x) ≤ kCnt P + 1 ∧
      pvalF pg (push 1 P x) = pvalF pg P * letV pg x := by
  obtain ⟨hs, hb⟩ := hI
  unfold push
  rw [brec_eq]
  split_ifs with hcond
  · simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at hcond
    obtain ⟨hpos, htop⟩ := hcond
    change kStk P &&& 255 = (x ^^^ 1) + 1 at htop
    have h255 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
    rw [h255, Nat.and_two_pow_sub_one_eq_mod] at htop
    have hsh : Nat.shiftRight (kStk P) 8 = kStk P / 256 := by
      change kStk P >>> 8 = _
      rw [Nat.shiftRight_eq_div_pow]
    rw [hsh]
    have hc' : kCnt P - 1 < 65536 := by omega
    unfold SInvF pvalF
    simp only [Nat.sub_eq]
    rw [kCnt_mkKF _ hc', kStk_mkKF _ hc']
    obtain ⟨c, hcP⟩ : ∃ c, kCnt P = c + 1 := ⟨kCnt P - 1, by omega⟩
    rw [hcP] at hs hb ⊢
    refine ⟨⟨?_, fun i hi => ?_⟩, by omega, ?_⟩
    · rw [Nat.add_sub_cancel]
      rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]
      exact hs
    · rw [Nat.add_sub_cancel] at hi
      rw [byte_div256F]
      exact hb (i + 1) (by omega)
    · rw [Nat.add_sub_cancel, fval_succ, htop, Nat.add_sub_cancel, mul_assoc, letV_xor1 pg hx,
        inv_mul_cancel, mul_one]
  · have hc' : Nat.succ (kCnt P) < 65536 := hc
    unfold SInvF pvalF
    rw [kCnt_mkKF _ hc', kStk_mkKF _ hc']
    have e : Nat.add (Nat.mul (kStk P) 256) (Nat.succ x) = kStk P * 256 + (x + 1) := rfl
    rw [e]
    refine ⟨⟨?_, fun i hi => ?_⟩, by omega, ?_⟩
    · rw [Nat.succ_eq_add_one, pow_succ]
      have : kStk P + 1 ≤ 256 ^ kCnt P := hs
      have h2 : (kStk P + 1) * 256 ≤ 256 ^ kCnt P * 256 := Nat.mul_le_mul_right _ this
      omega
    · rcases i with _ | i
      · simp
        omega
      · rw [← byte_div256F]
        have e1 : (kStk P * 256 + (x + 1)) / 256 = kStk P := by omega
        rw [e1]
        exact hb i (by omega)
    · change fval pg (kStk P * 256 + (x + 1)) (kCnt P + 1) = _
      rw [fval_succ]
      have e1 : (kStk P * 256 + (x + 1)) / 256 = kStk P := by omega
      have e2 : (kStk P * 256 + (x + 1)) % 256 - 1 = x := by omega
      rw [e1, e2]

@[expose] noncomputable def ptF (W n : ℕ) (inv : Bool) (k P : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun P => P) (fun k ih P =>
    ih (Bool.rec (motive := fun _ => Nat)
      (push (nat_lit 1) P (wLet W (Nat.sub n (Nat.succ k))))
      (push (nat_lit 1) P (Nat.xor (wLet W (Nat.succ k)) (nat_lit 1))) inv)) k P

theorem pushTailF_eq (W n : ℕ) (inv : Bool) (P : ℕ) : pushTailF W n inv P = ptF W n inv (n - 1) P :=
  rfl

theorem ptF_false (W n : ℕ) (hW : ∀ i < n, wLet W i < 254) :
    ∀ k, k + 1 ≤ n → ∀ P, SInvF P → kCnt P + k < 65536 →
      SInvF (ptF W n false k P) ∧ kCnt (ptF W n false k P) ≤ kCnt P + k ∧
      pvalF pg (ptF W n false k P) =
        pvalF pg P * ((List.range k).map fun j => letV pg (wLet W (n - k + j))).prod
  | 0, _, P, hI, _ => ⟨hI, by simp [ptF], by simp [ptF]⟩
  | k + 1, hk, P, hI, hc => by
    have hl := hW (n - (k + 1)) (by omega)
    obtain ⟨h1, h2, h3⟩ := pushF_spec pg hI (x := wLet W (n - (k + 1))) hl (by omega)
    obtain ⟨i1, i2, i3⟩ := ptF_false W n hW k (by omega) _ h1 (by omega)
    have es : ptF W n false (k + 1) P = ptF W n false k (push 1 P (wLet W (n - (k + 1)))) := rfl
    rw [es]
    refine ⟨i1, by omega, ?_⟩
    have hl2 : ((List.range (k + 1)).map fun j => letV pg (wLet W (n - (k + 1) + j))).prod =
        letV pg (wLet W (n - (k + 1))) *
          ((List.range k).map fun j => letV pg (wLet W (n - k + j))).prod := by
      rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, Nat.add_zero]
      congr 2
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have e : n - (k + 1) + (j + 1) = n - k + j := by omega
      simp only [Function.comp_apply, e]
    rw [i3, h3, hl2, mul_assoc]

theorem ptF_true (W n : ℕ) (hW : ∀ i < n, wLet W i < 254) :
    ∀ k, k + 1 ≤ n → ∀ P, SInvF P → kCnt P + k < 65536 →
      SInvF (ptF W n true k P) ∧ kCnt (ptF W n true k P) ≤ kCnt P + k ∧
      pvalF pg (ptF W n true k P) =
        pvalF pg P * (((List.range k).map fun j => letV pg (wLet W (j + 1))).prod)⁻¹
  | 0, _, P, hI, _ => ⟨hI, by simp [ptF], by simp [ptF]⟩
  | k + 1, hk, P, hI, hc => by
    have hl := hW (k + 1) (by omega)
    obtain ⟨h1, h2, h3⟩ := pushF_spec pg hI (x := wLet W (k + 1) ^^^ 1) (xor1_lt hl).1 (by omega)
    obtain ⟨i1, i2, i3⟩ := ptF_true W n hW k (by omega) _ h1 (by omega)
    have es : ptF W n true (k + 1) P = ptF W n true k (push 1 P (wLet W (k + 1) ^^^ 1)) := rfl
    rw [es]
    refine ⟨i1, by omega, ?_⟩
    rw [i3, h3, letV_xor1 pg hl, List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev,
      mul_assoc]

@[expose] noncomputable def stepF (PRT : ℕ → ℕ) (SB ns W q P : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => Nat) (push 1 P (wLet W q))
    (pushTailF (wWord (PRT (findSub SB ns (wLet W q / 2) - 1)))
      (wLen (PRT (findSub SB ns (wLet W q / 2) - 1)))
      (Nat.beq (Nat.land (Nat.xor (wLet (wWord (PRT (findSub SB ns (wLet W q / 2) - 1))) 0)
        (wLet W q)) 1) 0) P)
    (Nat.blt 0 (findSub SB ns (wLet W q / 2)))

theorem stackF_eq (PRT : ℕ → ℕ) (SB ns W n : ℕ) :
    stackF PRT SB ns W n = Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepF PRT SB ns W q P) n := by
  unfold stackF stepF
  simp only [shr1]
  rfl

theorem subsOK_specF {PRT : ℕ → ℕ} {SB ns : ℕ} (h : subsOK PRT SB ns false = true) :
    ∀ s < ns, 0 < wLen (PRT (Nat.shiftRight (sbE SB s) 8)) ∧
      wLet (wWord (PRT (Nat.shiftRight (sbE SB s) 8))) 0 / 2 = Nat.land (sbE SB s) 255 := by
  intro s hs
  have h1 := (allRec_iff _ ns).1 h s hs
  simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at h1
  obtain ⟨a, b⟩ := h1
  refine ⟨a, ?_⟩
  change Nat.shiftRight _ 1 = _ at b
  rw [shr1] at b
  exact b

theorem findSub_relF {PRT : ℕ → ℕ} {SB ns PR g : ℕ} (hsub : subsOK PRT SB ns false = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (h0 : 0 < findSub SB ns g) :
    findSub SB ns g - 1 < PR ∧ 0 < wLen (PRT (findSub SB ns g - 1)) ∧
      wLet (wWord (PRT (findSub SB ns g - 1))) 0 / 2 = g := by
  rcases findSub_spec SB g ns with h | ⟨s, hs, h1, h2⟩
  · omega
  · rw [h2, Nat.add_sub_cancel]
    obtain ⟨a, b⟩ := subsOK_specF hsub s hs
    exact ⟨hSB s hs, a, by rw [b, h1]⟩

theorem stackF_spec {PRT : ℕ → ℕ} {SB ns PR W n : ℕ}
    (hsub : subsOK PRT SB ns false = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, wLen (PRT r) < 256 ∧ ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254)
    (hn : n < 256) (hW : ∀ i < n, wLet W i < 254) :
    ∀ q ≤ n, SInvF (Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepF PRT SB ns W q P) q) ∧
      kCnt (Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepF PRT SB ns W q P) q) ≤ 255 * q ∧
      pvalF pg (Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepF PRT SB ns W q P) q) =
        ((List.range q).map fun i => letV pg (wLet W i)).prod
  | 0, _ => ⟨SInvF_zero, by simp [kCnt_eqF], by simp [pvalF, kCnt_eqF, fval]⟩
  | q + 1, hq => by
    obtain ⟨hI, hc, hv⟩ := stackF_spec hsub hSB hP hPL hn hW q (by omega)
    change SInvF (stepF PRT SB ns W q _) ∧ kCnt (stepF PRT SB ns W q _) ≤ 255 * (q + 1) ∧
      pvalF pg (stepF PRT SB ns W q _) = _
    generalize Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepF PRT SB ns W q P) q = P at hI hc hv
    have hl := hW q (by omega)
    rw [List.range_succ, List.map_append, List.prod_append, ← hv]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold stepF
    rw [brec_eq]
    split_ifs with hs
    · rw [Nat.blt_eq] at hs
      obtain ⟨hk, hlen, hfirst⟩ := findSub_relF hsub hSB hs
      generalize findSub SB ns (wLet W q / 2) - 1 = k at hk hlen hfirst ⊢
      obtain ⟨hkl, hkW⟩ := hPL k hk
      have hPk := hP k hk
      obtain ⟨m, hm⟩ : ∃ m, wLen (PRT k) = m + 1 := ⟨wLen (PRT k) - 1, by omega⟩
      rw [hm, bval_cons] at hPk
      have hx0 := hkW 0 (by omega)
      have hrest : ((List.range m).map fun j => letV pg (wLet (wWord (PRT k)) (j + 1))).prod =
          (letV pg (wLet (wWord (PRT k)) 0))⁻¹ := (inv_eq_of_mul_eq_one_right hPk).symm
      rw [pushTailF_eq, hm, Nat.add_sub_cancel]
      by_cases hpar : wLet (wWord (PRT k)) 0 = wLet W q
      ·
        have hb : Nat.beq (Nat.land (Nat.xor (wLet (wWord (PRT k)) 0) (wLet W q)) 1) 0 = true := by
          rw [hpar, Nat.beq_eq]
          change (wLet W q ^^^ wLet W q) &&& 1 = 0
          rw [Nat.xor_self]
          rfl
        rw [hb]
        obtain ⟨a, b, c⟩ := ptF_true pg (wWord (PRT k)) (m + 1) (by rw [← hm]; exact hkW) m
          (by omega) P hI (by omega)
        refine ⟨a, by omega, ?_⟩
        rw [c, hrest, inv_inv, hpar]
      ·
        have hx1 : wLet (wWord (PRT k)) 0 = wLet W q ^^^ 1 := by
          obtain ⟨-, h2, h3⟩ := xor1_lt hl
          omega
        have hb : Nat.beq (Nat.land (Nat.xor (wLet (wWord (PRT k)) 0) (wLet W q)) 1) 0 = false := by
          rw [hx1]
          apply Bool.eq_false_iff.2
          intro h
          rw [Nat.beq_eq] at h
          change (wLet W q ^^^ 1 ^^^ wLet W q) &&& 1 = 0 at h
          rw [Nat.xor_comm (wLet W q) 1, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h
          exact absurd h (by decide)
        rw [hb]
        obtain ⟨a, b, c⟩ := ptF_false pg (wWord (PRT k)) (m + 1) (by rw [← hm]; exact hkW) m
          (by omega) P hI (by omega)
        refine ⟨a, by omega, ?_⟩
        rw [c]
        congr 1
        have hlq : letV pg (wLet W q) = (letV pg (wLet (wWord (PRT k)) 0))⁻¹ := by
          rw [hx1, letV_xor1 pg hl, inv_inv]
        rw [hlq, ← hrest]
        congr 1
        apply List.map_congr_left
        intro j hj
        have e : m + 1 - m + j = j + 1 := by omega
        rw [e]
    · obtain ⟨a, b, c⟩ := pushF_spec pg hI (x := wLet W q) hl (by omega)
      exact ⟨a, by omega, c⟩

end Stack

theorem outWF_eq (M K : ℕ) : outW M 2 true K =
    HO.byteFold (fun q => 2 * mget M ((kByte K (kCnt K - (q + 1)) - 1) / 2) +
      (kByte K (kCnt K - (q + 1)) - 1) % 2) (kCnt K) := by
  unfold outW HO.byteFold
  congr 1
  funext q acc
  simp only [shr1, land1]
  rfl

theorem relsF_sound' {G : Type*} [Group G] (pg cg : ℕ → G) {CRT PRT : ℕ → ℕ} {SB ns M R PR Hs : ℕ}
    (h : relsF CRT PRT SB ns M R PR Hs = true) (hsub : subsOK PRT SB ns false = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (hM : ∀ g < 128, mget M g < 255 → mget M g < 127 ∧ cg (mget M g) = pg g)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, wLen (PRT r) < 256 ∧ ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254) :
    ∀ r < R, bval cg (wWord (CRT r)) (wLen (CRT r)) = 1 := by
  intro r hr
  have hall := (allRec_iff _ R).1 h r hr
  simp only [andB_iff, Nat.blt_eq] at hall
  obtain ⟨hlt, hbr⟩ := hall
  have hPk := hP _ hlt
  obtain ⟨hPn, hPW⟩ := hPL _ hlt
  generalize hget Hs r = k at hlt hPk hPn hPW hbr
  generalize PRT k = P at hPk hPn hPW hbr
  generalize CRT r = C at hbr
  unfold derivF at hbr
  rw [letB_eq] at hbr
  simp only [andB_iff, Nat.beq_eq] at hbr
  obtain ⟨hok, hcnt, hw⟩ := hbr
  obtain ⟨hI, hc, hv⟩ := stackF_spec pg hsub hSB hP hPL hPn hPW (wLen P) le_rfl
  rw [← stackF_eq] at hI hc hv
  set K := stackF PRT SB ns (wWord P) (wLen P) with hK
  have hv1 : pvalF pg K = 1 := by
    rw [hv, ← hPk]
    rfl
  have hok' := (allRec_iff _ _).1 hok
  rw [← hcnt, ← hw, outWF_eq]
  obtain ⟨hs, hb⟩ := hI
  have hx : ∀ q < kCnt K, kByte K (kCnt K - (q + 1)) - 1 < 254 ∧
      mget M ((kByte K (kCnt K - (q + 1)) - 1) / 2) < 255 := by
    intro q hq
    have h1 := hb (kCnt K - (q + 1)) (by omega)
    have h2 : Nat.blt (mget M (Nat.shiftRight (kByte K (kCnt K - (q + 1)) - 1) 1)) 255 = true :=
      hok' (kCnt K - (q + 1)) (by omega)
    rw [Nat.blt_eq, shr1] at h2
    rw [kByte_eqF]
    exact ⟨by omega, by rw [← kByte_eqF]; exact h2⟩
  have hM' : ∀ q < kCnt K, mget M ((kByte K (kCnt K - (q + 1)) - 1) / 2) < 127 ∧
      cg (mget M ((kByte K (kCnt K - (q + 1)) - 1) / 2)) =
        pg ((kByte K (kCnt K - (q + 1)) - 1) / 2) :=
    fun q hq => hM _ (by have := (hx q hq).1; omega) (hx q hq).2
  have hf : ∀ q < kCnt K, (fun q => 2 * mget M ((kByte K (kCnt K - (q + 1)) - 1) / 2) +
      (kByte K (kCnt K - (q + 1)) - 1) % 2) q < 256 := by
    intro q hq
    have := (hM' q hq).1
    simp only
    omega
  unfold pvalF at hv1
  rw [← hv1, fval_eq_prod]
  unfold bval
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range] at hq
  rw [fold_byte _ hf hq, letV_ren pg cg (hx q hq).1 (hM' q hq).1 (hM' q hq).2, kByte_eqF]
  have e : kCnt K - 1 - q = kCnt K - (q + 1) := by omega
  rw [e]

end CFSG.Certificates.BindF

end
