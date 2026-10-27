module

public import CFSG.Certificates.Kernel.BindByte
public import CFSG.Certificates.Kernel.BindSound
import Mathlib.Tactic.Group
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Certificates.BindL

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates.LCE

theorem invMap_inv (Q : ℕ) : ∀ n, invMap Q n ≠ 0 → ∀ x < 256, mget (invMap Q n) x < 255 →
    mget (invMap Q n) x < n ∧ mget Q (mget (invMap Q n) x) = x
  | 0, _, x, hx, h => by
    change mget allFF x < 255 at h
    rw [BindS.allFF_byte x hx] at h
    omega
  | n + 1, h, x, hx, hlt => by
    have e : invMap Q (n + 1) = mset (invMap Q n) (mget Q n) n := rfl
    rw [e] at h hlt ⊢
    obtain ⟨hpos, -, -, -, hset⟩ := BindS.mset_spec h
    rw [hset x] at hlt ⊢
    split_ifs with hxe
    · exact ⟨by omega, hxe.symm⟩
    · rw [ite_eq_right hxe] at hlt
      obtain ⟨a, b⟩ := invMap_inv Q n (by omega) x hx hlt
      exact ⟨by omega, b⟩

theorem stMap_ok (ST : ℕ → ℕ) : ∀ K, stMap ST K ≠ 0 → ∀ j < K,
    wLen (ST j) = 1 ∧ wWord (ST j) % 2 = 0 ∧ wWord (ST j) < 256
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | K + 1, h, j, hj => by
    have e : stMap ST (K + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (mset (stMap ST K) (Nat.shiftRight (wWord (ST K)) 1) K)
        (andB (Nat.beq (wLen (ST K)) 1) (andB (Nat.beq (Nat.land (wWord (ST K)) 1) 0)
          (Nat.blt (wWord (ST K)) 256))) := rfl
    rw [e, brec_eq] at h
    split_ifs at h with hc
    · obtain ⟨hpos, -⟩ := BindS.mset_spec h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact stMap_ok ST K (by omega) j hj'
      · simp only [andB_iff, Nat.beq_eq, Nat.blt_eq] at hc
        obtain ⟨h1, h2, h3⟩ := hc
        change wWord (ST j) &&& 1 = 0 at h2
        rw [Nat.and_one_is_mod] at h2
        exact ⟨h1, h2, h3⟩
    · exact absurd rfl h

theorem mget_lt (M g : ℕ) : mget M g < 256 := by
  rw [BindS.mget_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem letV_mem {G : Type*} [Group G] (pg : ℕ → G) {H : Subgroup G} {l : ℕ}
    (h : pg (l / 2) ∈ H) : letV pg l ∈ H := by
  unfold letV
  split_ifs
  · exact H.one_mem
  · exact h
  · exact H.inv_mem h

theorem list_prod_mem' {G : Type*} [Group G] {H : Subgroup G} (f : ℕ → G) (m : ℕ)
    (h : ∀ j < m, f j ∈ H) : ((List.range m).map f).prod ∈ H := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact h j (List.mem_range.mp hj)

theorem levelOK_sound' {G : Type*} [Group G] (pg : ℕ → G) {ST PRT : ℕ → ℕ} {S Q n K SB ns PR : ℕ}
    (h : levelOK ST PRT S Q n K SB ns = true) (hS : S = stMap ST K) (h0 : S ≠ 0)
    (hIQ : invMap Q n ≠ 0)
    (hsub : subsOK PRT SB ns true = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254) :
    Subgroup.closure ((fun j => bval pg (wWord (ST j)) (wLen (ST j))) '' {j | j < K}) =
      Subgroup.closure ((fun c => pg (mget Q c)) '' {c | c < n}) := by
  unfold levelOK at h
  simp only [letB_eq, andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := (allRec_iff _ n).1 h1
  have h2' := (allRec_iff _ K).1 h2
  have hok := stMap_ok ST K (hS ▸ h0)
  have hval : ∀ j < K, bval pg (wWord (ST j)) (wLen (ST j)) = pg (wWord (ST j) / 2) := by
    intro j hj
    obtain ⟨hl, he, hlt⟩ := hok j hj
    rw [hl, HO.bval_one pg hlt]
    have : wWord (ST j) = 2 * (wWord (ST j) / 2) := by omega
    rw [this, letV_even pg (by omega)]
    congr 1
    omega
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    change j < K at hj
    change bval pg (wWord (ST j)) (wLen (ST j)) ∈
      Subgroup.closure ((fun c => pg (mget Q c)) '' {c | c < n})
    rw [hval j hj]
    set g := wWord (ST j) / 2 with hg
    have hg128 : g < 128 := by have := (hok j hj).2.2; omega
    have hj2 := h2' j hj
    simp only [orB_iff, andB_iff, Nat.blt_eq, shr1] at hj2
    have hmemQ : ∀ x < 256, mget (invMap Q n) x < 255 →
        pg x ∈ Subgroup.closure ((fun c => pg (mget Q c)) '' {c | c < n}) := by
      intro x hx hlt
      obtain ⟨a, b⟩ := invMap_inv Q n hIQ x hx hlt
      apply Subgroup.subset_closure
      exact ⟨mget (invMap Q n) x, a, by simp only [b]⟩
    rcases hj2 with hq | ⟨hs0, hR⟩
    · exact hmemQ g (by omega) hq
    · rw [← hg] at hs0 hR
      obtain ⟨hk, hlen, hfirst⟩ := findSub_rel hsub hSB hs0
      set k := findSub SB ns g - 1
      have hR' := (allRec_iff _ _).1 hR
      simp only [Nat.blt_eq] at hR'
      have hPk := hP k hk
      obtain ⟨m, hm⟩ : ∃ m, wLen (PRT k) = m + 1 := ⟨wLen (PRT k) - 1, by omega⟩
      rw [hm, bval_cons, hfirst, letV_odd pg (by have := hPL k hk 0 (by omega); omega)] at hPk
      have e : pg g = ((List.range m).map fun j => letV pg (wLet (wWord (PRT k)) (j + 1))).prod :=
        (inv_mul_eq_one.mp hPk)
      rw [e]
      apply list_prod_mem'
      intro q hq
      apply letV_mem
      have hq' := hR' q (by change q < wLen (PRT k) - 1; omega)
      exact hmemQ _ (by have := hPL k hk (q + 1) (by omega); omega) hq'
  · rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    change c < n at hc
    have hS1 := h1' c hc
    simp only [Nat.blt_eq] at hS1
    subst hS
    obtain ⟨hlt, hl, hw⟩ := (BindS.stMap_inv ST K h0 (mget Q c) (mget_lt Q c)).resolve_left
      (by omega)
    apply Subgroup.subset_closure
    refine ⟨mget (stMap ST K) (mget Q c), hlt, ?_⟩
    change bval pg (wWord (ST _)) (wLen (ST _)) = pg (mget Q c)
    rw [hval _ hlt, hw]
    congr 1
    omega

section Stack

variable {G : Type*} [Group G] (pg : ℕ → G)

@[expose] def sval : ℕ → ℕ → G
  | _, 0 => 1
  | s, c + 1 => sval (s / 256) c * pg (s % 256 - 1)

theorem sval_succ (s c : ℕ) : sval pg s (c + 1) = sval pg (s / 256) c * pg (s % 256 - 1) := by
  rw [sval]

theorem sval_top : ∀ c s, sval pg s (c + 1) = pg (s / 256 ^ c % 256 - 1) * sval pg (s % 256 ^ c) c
  | 0, s => by simp [sval]
  | c + 1, s => by
    rw [sval_succ, sval_top c (s / 256), sval_succ, mul_assoc]
    have e1 : s / 256 / 256 ^ c = s / 256 ^ (c + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    have e2 : s % 256 ^ (c + 1) / 256 = s / 256 % 256 ^ c := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    have e3 : s % 256 ^ (c + 1) % 256 = s % 256 :=
      Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (Nat.succ_ne_zero c))
    rw [e1, e2, e3]

theorem sval_eq_prod : ∀ c s, sval pg s c =
    ((List.range c).map fun q => pg (s / 256 ^ (c - 1 - q) % 256 - 1)).prod
  | 0, s => rfl
  | c + 1, s => by
    rw [sval_succ, sval_eq_prod c (s / 256), List.range_succ, List.map_append, List.prod_append]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro q hq
      rw [List.mem_range] at hq
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      have e : c - 1 - q + 1 = c + 1 - 1 - q := by omega
      rw [e]
    · simp

@[expose] def SInv (P : ℕ) : Prop :=
  kStk P < 256 ^ kCnt P ∧ ∀ i < kCnt P, 1 ≤ kStk P / 256 ^ i % 256 ∧ kStk P / 256 ^ i % 256 ≤ 127

theorem kCnt_eq (P : ℕ) : kCnt P = P % 65536 := by
  change P &&& (2 ^ 16 - 1) = P % 2 ^ 16
  exact Nat.and_two_pow_sub_one_eq_mod P 16

theorem kStk_eq (P : ℕ) : kStk P = P / 65536 := by
  change P >>> 16 = P / 2 ^ 16
  exact Nat.shiftRight_eq_div_pow P 16

theorem mkK_eq {c : ℕ} (s : ℕ) (hc : c < 65536) : mkK c s = s * 65536 + c := by
  change c ||| s <<< 16 = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by norm_num; exact hc), Nat.shiftLeft_eq]

theorem kCnt_mkK {c : ℕ} (s : ℕ) (hc : c < 65536) : kCnt (mkK c s) = c := by
  rw [kCnt_eq, mkK_eq s hc]
  omega

theorem kStk_mkK {c : ℕ} (s : ℕ) (hc : c < 65536) : kStk (mkK c s) = s := by
  rw [kStk_eq, mkK_eq s hc]
  omega

theorem SInv_zero : SInv 0 := by
  refine ⟨?_, ?_⟩ <;> simp [kStk_eq, kCnt_eq]

@[expose] noncomputable def pval (P : ℕ) : G := sval pg (kStk P) (kCnt P)

theorem byte_div256 (s i : ℕ) : s / 256 / 256 ^ i % 256 = s / 256 ^ (i + 1) % 256 := by
  rw [Nat.div_div_eq_div_mul, pow_succ']

theorem push_spec (hinv : ∀ g, pg g * pg g = 1) {P x : ℕ} (hI : SInv P) (hx : x < 127)
    (hc : kCnt P + 1 < 65536) :
    SInv (push 0 P x) ∧ kCnt (push 0 P x) ≤ kCnt P + 1 ∧
      pval pg (push 0 P x) = pval pg P * pg x := by
  obtain ⟨hs, hb⟩ := hI
  unfold push
  rw [brec_eq]
  have hx0 : Nat.xor x 0 = x := Nat.xor_zero x
  rw [hx0]
  split_ifs with hcond
  · simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at hcond
    obtain ⟨hpos, htop⟩ := hcond
    change kStk P &&& 255 = x + 1 at htop
    rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at htop
    have hsh : Nat.shiftRight (kStk P) 8 = kStk P / 256 := by
      change kStk P >>> 8 = _
      rw [Nat.shiftRight_eq_div_pow]
    rw [hsh]
    have hc' : kCnt P - 1 < 65536 := by omega
    unfold SInv pval
    simp only [Nat.sub_eq]
    rw [kCnt_mkK _ hc', kStk_mkK _ hc']
    obtain ⟨c, hcP⟩ : ∃ c, kCnt P = c + 1 := ⟨kCnt P - 1, by omega⟩
    rw [hcP] at hs hb ⊢
    refine ⟨⟨?_, fun i hi => ?_⟩, by omega, ?_⟩
    · rw [Nat.add_sub_cancel]
      rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]
      exact hs
    · rw [Nat.add_sub_cancel] at hi
      rw [byte_div256]
      exact hb (i + 1) (by omega)
    · rw [Nat.add_sub_cancel, sval_succ, htop, Nat.add_sub_cancel, mul_assoc, hinv, mul_one]
  · have hc' : Nat.succ (kCnt P) < 65536 := hc
    unfold SInv pval
    rw [kCnt_mkK _ hc', kStk_mkK _ hc']
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
      · rw [← byte_div256]
        have e1 : (kStk P * 256 + (x + 1)) / 256 = kStk P := by omega
        rw [e1]
        exact hb i (by omega)
    · change sval pg (kStk P * 256 + (x + 1)) (kCnt P + 1) = _
      rw [sval_succ]
      have e1 : (kStk P * 256 + (x + 1)) / 256 = kStk P := by omega
      have e2 : (kStk P * 256 + (x + 1)) % 256 - 1 = x := by omega
      rw [e1, e2]

@[expose] noncomputable def ptA (W n k P : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun P => P) (fun k ih P =>
    ih (push (nat_lit 0) P (Nat.shiftRight (wLet W (Nat.sub n (Nat.succ k))) (nat_lit 1)))) k P

theorem ptA_succ (W n k P : ℕ) : ptA W n (k + 1) P = ptA W n k (push 0 P (wLet W (n - (k + 1)) / 2)) := by
  rw [← shr1]
  rfl

theorem pushTailA_eq (W n P : ℕ) : pushTailA W n P = ptA W n (n - 1) P := rfl

theorem ptA_spec (hinv : ∀ g, pg g * pg g = 1) (W n : ℕ) (hW : ∀ i < n, wLet W i < 254) :
    ∀ k, k + 1 ≤ n → ∀ P, SInv P → kCnt P + k < 65536 →
      SInv (ptA W n k P) ∧ kCnt (ptA W n k P) ≤ kCnt P + k ∧
      pval pg (ptA W n k P) =
        pval pg P * ((List.range k).map fun j => pg (wLet W (n - k + j) / 2)).prod
  | 0, _, P, hI, _ => ⟨hI, by simp [ptA], by simp [ptA]⟩
  | k + 1, hk, P, hI, hc => by
    have hl := hW (n - (k + 1)) (by omega)
    obtain ⟨h1, h2, h3⟩ := push_spec pg hinv hI (x := wLet W (n - (k + 1)) / 2) (by omega)
      (by omega)
    obtain ⟨i1, i2, i3⟩ := ptA_spec hinv W n hW k (by omega) _ h1 (by omega)
    rw [ptA_succ]
    refine ⟨i1, by omega, ?_⟩
    have hl2 : ((List.range (k + 1)).map fun j => pg (wLet W (n - (k + 1) + j) / 2)).prod =
        pg (wLet W (n - (k + 1)) / 2) *
          ((List.range k).map fun j => pg (wLet W (n - k + j) / 2)).prod := by
      rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, Nat.add_zero]
      congr 2
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have e : n - (k + 1) + (j + 1) = n - k + j := by omega
      simp only [Function.comp_apply, e]
    rw [i3, h3, hl2, mul_assoc]

theorem pushTailA_spec (hinv : ∀ g, pg g * pg g = 1) {W n P : ℕ} (hn : 0 < n)
    (hW : ∀ i < n, wLet W i < 254) (hI : SInv P) (hc : kCnt P + (n - 1) < 65536) :
    SInv (pushTailA W n P) ∧ kCnt (pushTailA W n P) ≤ kCnt P + (n - 1) ∧
      pval pg (pushTailA W n P) =
        pval pg P * ((List.range (n - 1)).map fun j => pg (wLet W (j + 1) / 2)).prod := by
  rw [pushTailA_eq]
  obtain ⟨a, b, c⟩ := ptA_spec pg hinv W n hW (n - 1) (by omega) P hI hc
  refine ⟨a, b, ?_⟩
  rw [c]
  have e : n - (n - 1) = 1 := by omega
  simp only [e, Nat.add_comm 1]

@[expose] noncomputable def stepA (PRT : ℕ → ℕ) (SB ns W q P : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => Nat) (push 0 P (wLet W q / 2))
    (pushTailA (wWord (PRT (findSub SB ns (wLet W q / 2) - 1)))
      (wLen (PRT (findSub SB ns (wLet W q / 2) - 1))) P)
    (Nat.blt 0 (findSub SB ns (wLet W q / 2)))

theorem stackA_eq (PRT : ℕ → ℕ) (SB ns W n : ℕ) :
    stackA PRT SB ns W n = Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepA PRT SB ns W q P) n := by
  unfold stackA stepA
  simp only [shr1]
  rfl

theorem stackA_spec (hinv : ∀ g, pg g * pg g = 1) {PRT : ℕ → ℕ} {SB ns PR W n : ℕ}
    (hsub : subsOK PRT SB ns true = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, wLen (PRT r) < 256 ∧ ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254)
    (hn : n < 256) (hW : ∀ i < n, wLet W i < 254) :
    ∀ q ≤ n, SInv (Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepA PRT SB ns W q P) q) ∧
      kCnt (Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepA PRT SB ns W q P) q) ≤ 255 * q ∧
      pval pg (Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepA PRT SB ns W q P) q) =
        ((List.range q).map fun i => pg (wLet W i / 2)).prod
  | 0, _ => ⟨SInv_zero, by simp [kCnt_eq], by simp [pval, kCnt_eq, sval]⟩
  | q + 1, hq => by
    obtain ⟨hI, hc, hv⟩ := stackA_spec hinv hsub hSB hP hPL hn hW q (by omega)
    change SInv (stepA PRT SB ns W q _) ∧ kCnt (stepA PRT SB ns W q _) ≤ 255 * (q + 1) ∧
      pval pg (stepA PRT SB ns W q _) = _
    generalize Nat.rec (motive := fun _ => ℕ) 0 (fun q P => stepA PRT SB ns W q P) q = P at hI hc hv
    have hl := hW q (by omega)
    rw [List.range_succ, List.map_append, List.prod_append, ← hv]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold stepA
    rw [brec_eq]
    split_ifs with hs
    · rw [Nat.blt_eq] at hs
      obtain ⟨hk, hlen, hfirst⟩ := findSub_rel hsub hSB hs
      generalize findSub SB ns (wLet W q / 2) - 1 = k at hk hlen hfirst ⊢
      obtain ⟨hkl, hkW⟩ := hPL k hk
      obtain ⟨a, b, c⟩ := pushTailA_spec pg hinv hlen hkW hI (by omega)
      refine ⟨a, by omega, ?_⟩
      rw [c]
      congr 1
      have hPk := hP k hk
      obtain ⟨m, hm⟩ : ∃ m, wLen (PRT k) = m + 1 := ⟨wLen (PRT k) - 1, by omega⟩
      have hkW' := hkW
      rw [hm] at hPk hkW'
      rw [bval_cons, hfirst, letV_odd pg (by have := hkW 0 (by omega); omega)] at hPk
      have e := inv_mul_eq_one.mp hPk
      rw [hm, Nat.add_sub_cancel, e]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      exact (letV_inv pg hinv (by have := hkW' (j + 1) (by omega); omega)).symm
    · obtain ⟨a, b, c⟩ := push_spec pg hinv hI (x := wLet W q / 2) (by omega) (by omega)
      exact ⟨a, by omega, c⟩

@[expose] noncomputable def cstep (P : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => Nat) P
      (mkK (Nat.sub (kCnt P) (nat_lit 2))
        (Nat.shiftRight (Nat.land (kStk P) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (Nat.sub (kCnt P) (nat_lit 1)))) (nat_lit 1))) (nat_lit 8)))
      (andB (Nat.ble (nat_lit 2) (kCnt P)) (Nat.beq (kByte P (Nat.sub (kCnt P) (nat_lit 1))) (kByte P (nat_lit 0))))

theorem kByte_eq (P i : ℕ) : kByte P i = kStk P / 256 ^ i % 256 := HO.wLet_eq (kStk P) i

theorem byte_mod {s k j : ℕ} (hj : j < k) : s % 256 ^ k / 256 ^ j % 256 = s / 256 ^ j % 256 := by
  conv_rhs => rw [← Nat.mod_add_div s (256 ^ k), Nat.add_comm, Nat.mul_comm]
  rw [Nat.add_comm, HO.byte_add_high hj]

theorem cstep_spec (hinv : ∀ g, pg g * pg g = 1) {P : ℕ} (hI : SInv P) (hv : pval pg P = 1)
    (hc : kCnt P < 65536) :
    SInv (cstep P) ∧ pval pg (cstep P) = 1 ∧ kCnt (cstep P) < 65536 := by
  unfold cstep
  rw [brec_eq]
  split_ifs with hcond
  · simp only [andB_iff, Nat.ble_eq, Nat.beq_eq, kByte_eq] at hcond
    obtain ⟨h2, hbyte⟩ := hcond
    obtain ⟨hs, hb⟩ := hI
    obtain ⟨c, hcP⟩ : ∃ c, kCnt P = c + 2 := ⟨kCnt P - 2, by omega⟩
    have hmask : Nat.shiftRight (Nat.land (kStk P) (Nat.sub (Nat.shiftLeft 1 (Nat.mul 8
        (Nat.sub (kCnt P) 1))) 1)) 8 = kStk P % 256 ^ (c + 1) / 256 := by
      change (kStk P &&& ((1 <<< (8 * (kCnt P - 1))) - 1)) >>> 8 = _
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
        HO.two_pow_eight_mul, hcP]
      norm_num
    rw [hmask]
    simp only [Nat.sub_eq]
    have hc2 : kCnt P - 2 < 65536 := by omega
    unfold pval at hv
    unfold SInv pval
    rw [kCnt_mkK _ hc2, kStk_mkK _ hc2]
    have hbyte' : kStk P / 256 ^ (c + 1) % 256 = kStk P % 256 := by
      have := hbyte
      simp only [Nat.sub_eq, hcP] at this
      simpa using this
    rw [hcP] at hs hb hv ⊢
    simp only [Nat.add_sub_cancel]
    refine ⟨⟨?_, fun i hi => ?_⟩, ?_, by omega⟩
    · rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]
      exact Nat.mod_lt _ (by positivity)
    · rw [byte_div256, byte_mod (by omega)]
      exact hb (i + 1) (by omega)
    · rw [sval_top, sval_succ] at hv
      have e3 : kStk P % 256 ^ (c + 1) % 256 = kStk P % 256 :=
        Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (Nat.succ_ne_zero c))
      rw [e3, hbyte'] at hv
      set X := pg (kStk P % 256 - 1)
      set Mv := sval pg (kStk P % 256 ^ (c + 1) / 256) c
      have hX : X * X = 1 := hinv _
      calc Mv = X⁻¹ * (X * (Mv * X)) * X⁻¹ := by group
        _ = X⁻¹ * X⁻¹ := by rw [hv]; group
        _ = X * X := by rw [inv_eq_of_mul_eq_one_right hX]
        _ = 1 := hX
  · exact ⟨hI, hv, hc⟩

theorem cycRed_spec (hinv : ∀ g, pg g * pg g = 1) {P : ℕ} (hI : SInv P) (hv : pval pg P = 1)
    (hc : kCnt P < 65536) : ∀ m, SInv (Nat.rec (motive := fun _ => ℕ) P (fun _ P => cstep P) m) ∧
      pval pg (Nat.rec (motive := fun _ => ℕ) P (fun _ P => cstep P) m) = 1 ∧
      kCnt (Nat.rec (motive := fun _ => ℕ) P (fun _ P => cstep P) m) < 65536
  | 0 => ⟨hI, hv, hc⟩
  | m + 1 => by
    obtain ⟨a, b, c⟩ := cycRed_spec hinv hI hv hc m
    exact cstep_spec pg hinv a b c

end Stack

theorem outW_eq (M mul K : ℕ) : outW M mul false K =
    HO.byteFold (fun q => mul * mget M (kByte K (kCnt K - (q + 1)) - 1)) (kCnt K) := rfl

theorem relsA_sound' {G : Type*} [Group G] (pg cval : ℕ → G) {cn cw PRT : ℕ → ℕ}
    {SB ns M mul R PR Hs : ℕ}
    (h : relsA cn cw PRT SB ns M mul R PR Hs = true)
    (hsub : subsOK PRT SB ns true = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (hinv : ∀ g, pg g * pg g = 1)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, wLen (PRT r) < 256 ∧ ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254)
    (hM : ∀ g < 127, mget M g < 255 → mul * mget M g < 256 ∧ cval (mul * mget M g) = pg g) :
    ∀ r < R, ((List.range (cn r)).map fun q => cval (wLet (cw r) q)).prod = 1 := by
  intro r hr
  have hall := (allRec_iff _ R).1 h r hr
  simp only [andB_iff, Nat.blt_eq] at hall
  obtain ⟨hlt, hbr⟩ := hall
  have hPk := hP _ hlt
  obtain ⟨hPn, hPW⟩ := hPL _ hlt
  generalize Nat.land (hget Hs r) 32767 = k at hlt hPk hPn hPW hbr
  generalize PRT k = P at hPk hPn hPW hbr
  rw [brec_eq] at hbr
  split_ifs at hbr with hbit
  ·
    unfold derivA at hbr
    rw [letB_eq] at hbr
    simp only [andB_iff, Nat.beq_eq] at hbr
    obtain ⟨hok, hcnt, hw⟩ := hbr
    obtain ⟨hI, hc, hv⟩ := stackA_spec pg hinv hsub hSB hP hPL hPn hPW (wLen P) le_rfl
    rw [← stackA_eq] at hI hc hv
    have hv1 : pval pg (stackA PRT SB ns (wWord P) (wLen P)) = 1 := by
      rw [hv, ← hPk]
      unfold bval
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (letV_inv pg hinv (by have := hPW i (List.mem_range.mp hi); omega)).symm
    have hc' : kCnt (stackA PRT SB ns (wWord P) (wLen P)) < 65536 := by
      have : 255 * wLen P ≤ 255 * 255 := Nat.mul_le_mul_left _ (by omega)
      omega
    obtain ⟨hI2, hv2, -⟩ := cycRed_spec pg hinv hI hv1 hc' (kCnt (stackA PRT SB ns (wWord P) (wLen P)))
    set K := cycRed (stackA PRT SB ns (wWord P) (wLen P)) with hK
    have eK : K = Nat.rec (motive := fun _ => ℕ) (stackA PRT SB ns (wWord P) (wLen P))
        (fun _ P => cstep P) (kCnt (stackA PRT SB ns (wWord P) (wLen P))) := rfl
    rw [← eK] at hI2 hv2
    have hok' := (allRec_iff _ _).1 hok
    rw [← hcnt, ← hw, outW_eq]
    obtain ⟨hs, hb⟩ := hI2
    have hx : ∀ q < kCnt K, kByte K (kCnt K - (q + 1)) - 1 < 127 ∧
        mget M (kByte K (kCnt K - (q + 1)) - 1) < 255 := by
      intro q hq
      have h1 := hb (kCnt K - (q + 1)) (by omega)
      have h2 : Nat.blt (mget M (kByte K (kCnt K - (q + 1)) - 1)) 255 = true :=
        hok' (kCnt K - (q + 1)) (by omega)
      rw [Nat.blt_eq] at h2
      rw [kByte_eq]
      exact ⟨by omega, by rw [← kByte_eq]; exact h2⟩
    have hf : ∀ q < kCnt K, (fun q => mul * mget M (kByte K (kCnt K - (q + 1)) - 1)) q < 256 :=
      fun q hq => (hM _ (hx q hq).1 (hx q hq).2).1
    unfold pval at hv2
    rw [← hv2, sval_eq_prod]
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [List.mem_range] at hq
    rw [fold_byte _ hf hq, (hM _ (hx q hq).1 (hx q hq).2).2, kByte_eq]
    have e : kCnt K - 1 - q = kCnt K - (q + 1) := by omega
    rw [e]
  ·
    unfold subU at hbr
    simp only [andB_iff, Nat.beq_eq] at hbr
    obtain ⟨hcn, hcw, hev⟩ := hbr
    have hev' := (allRec_iff _ _).1 hev
    simp only [andB_iff, Nat.beq_eq, Nat.blt_eq, shr1] at hev'
    have hx : ∀ q < wLen P, wLet (wWord P) q / 2 < 127 ∧ mget M (wLet (wWord P) q / 2) < 255 ∧
        wLet (wWord P) q % 2 = 0 := by
      intro q hq
      have h1 := hPW q hq
      obtain ⟨h2, h3⟩ := hev' q hq
      change wLet (wWord P) q &&& 1 = 0 at h2
      rw [Nat.and_one_is_mod] at h2
      exact ⟨by omega, h3, h2⟩
    have e : Nat.rec (motive := fun _ => ℕ) 0 (fun q acc => Nat.lor acc
        (Nat.shiftLeft (Nat.mul mul (mget M (Nat.shiftRight (wLet (wWord P) q) 1))) (Nat.mul 8 q)))
        (wLen P) = HO.byteFold (fun q => mul * mget M (wLet (wWord P) q / 2)) (wLen P) := by
      change HO.byteFold (fun q => mul * mget M (Nat.shiftRight (wLet (wWord P) q) 1)) (wLen P) = _
      simp only [shr1]
    rw [e] at hcw
    have hf : ∀ q < wLen P, (fun q => mul * mget M (wLet (wWord P) q / 2)) q < 256 :=
      fun q hq => (hM _ (hx q hq).1 (hx q hq).2.1).1
    rw [hcn, hcw, ← hPk]
    unfold bval
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [List.mem_range] at hq
    rw [fold_byte _ hf hq, (hM _ (hx q hq).1 (hx q hq).2.1).2]
    have h1 := hPW q hq
    have h3 := (hx q hq).2.2
    have : wLet (wWord P) q = 2 * (wLet (wWord P) q / 2) := by omega
    conv_rhs => rw [this]
    rw [letV_even pg (by omega)]

end CFSG.Certificates.BindL

end
