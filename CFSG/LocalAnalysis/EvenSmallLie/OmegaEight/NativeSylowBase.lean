
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylowDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

@[expose] public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem foldr_ite_xor (L : List ℕ) (f : ℕ → ℕ) (b : ℕ → Bool) :
    L.foldr (fun c acc => if b c then f c ^^^ acc else acc) 0 =
      L.foldr (fun c acc => (if b c then f c else 0) ^^^ acc) 0 := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    simp only [List.foldr_cons, ih]
    cases b c <;> simp

theorem foldr_xor_split (L : List ℕ) (f g : ℕ → ℕ) :
    L.foldr (fun c acc => (f c ^^^ g c) ^^^ acc) 0 =
      L.foldr (fun c acc => f c ^^^ acc) 0 ^^^ L.foldr (fun c acc => g c ^^^ acc) 0 := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.foldr_cons, ih]
    ac_rfl

theorem matApp_eq (M v : ℕ) : matApp M v =
    (List.range 8).foldr (fun c acc => (if v.testBit c then M / 256 ^ c % 256 else 0) ^^^ acc)
      0 := by
  rw [matApp, foldr_ite_xor]

theorem matApp_xor (M x y : ℕ) : matApp M (x ^^^ y) = matApp M x ^^^ matApp M y := by
  rw [matApp_eq, matApp_eq, matApp_eq, ← foldr_xor_split]
  congr 1
  funext c acc
  rw [Nat.testBit_xor]
  cases x.testBit c <;> cases y.testBit c <;> simp

theorem matApp_zero (M : ℕ) : matApp M 0 = 0 := by
  simp [matApp]

theorem foldr_xor_lt (L : List ℕ) (f : ℕ → ℕ) (hf : ∀ c, f c < 256) :
    L.foldr (fun c acc => f c ^^^ acc) 0 < 256 := by
  induction L with
  | nil => simp
  | cons c L ih =>
    rw [List.foldr_cons]
    exact Nat.xor_lt_two_pow (n := 8) (hf c) ih

theorem matApp_lt (M v : ℕ) : matApp M v < 256 := by
  rw [matApp_eq]
  refine foldr_xor_lt _ _ fun c => ?_
  split
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

theorem foldr_xor_zero {g : ℕ → ℕ} :
    ∀ {L : List ℕ}, (∀ c ∈ L, g c = 0) → L.foldr (fun c acc => g c ^^^ acc) 0 = 0
  | [], _ => rfl
  | a :: L, h => by
    rw [List.foldr_cons, h a List.mem_cons_self,
      foldr_xor_zero fun c hc => h c (List.mem_cons_of_mem _ hc), Nat.zero_xor]

theorem foldr_xor_single {c : ℕ} {g : ℕ → ℕ} (hg : ∀ c', c' ≠ c → g c' = 0) :
    ∀ {L : List ℕ}, L.Nodup → c ∈ L → L.foldr (fun c' acc => g c' ^^^ acc) 0 = g c
  | [], _, h => absurd h List.not_mem_nil
  | a :: L, hn, h => by
    rw [List.foldr_cons]
    obtain ⟨ha, hn⟩ := List.nodup_cons.1 hn
    rcases List.mem_cons.1 h with rfl | h
    · rw [foldr_xor_zero fun c' hc' => hg c' fun e => ha (e ▸ hc'), Nat.xor_zero]
    · rw [hg a fun e => ha (e ▸ h), Nat.zero_xor, foldr_xor_single hg hn h]

theorem matApp_pow (M : ℕ) {c : ℕ} (hc : c < 8) : matApp M (2 ^ c) = M / 256 ^ c % 256 := by
  rw [matApp_eq]
  refine (foldr_xor_single (g := fun c' => if (2 ^ c).testBit c' then M / 256 ^ c' % 256 else 0)
    (fun c' hc' => ?_) (List.nodup_range) (List.mem_range.2 hc)).trans ?_
  · simp [Ne.symm hc']
  · simp

theorem horner_byte (f : ℕ → ℕ) (hf : ∀ c, f c < 256) :
    ∀ (n s k : ℕ), k < n →
      (List.range' s n).foldr (fun c acc => f c + 256 * acc) 0 / 256 ^ k % 256 = f (s + k)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, 0, _ => by
    rw [List.range'_succ, List.foldr_cons, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf s), Nat.add_zero]
  | n + 1, s, k + 1, h => by
    rw [List.range'_succ, List.foldr_cons, pow_succ', ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (hf s), Nat.zero_add,
      horner_byte f hf n (s + 1) k (by omega)]
    congr 1
    omega

theorem horner_lt (f : ℕ → ℕ) (hf : ∀ c, f c < 256) :
    ∀ (n s : ℕ), (List.range' s n).foldr (fun c acc => f c + 256 * acc) 0 < 256 ^ n
  | 0, _ => by simp
  | n + 1, s => by
    rw [List.range'_succ, List.foldr_cons, pow_succ']
    have := horner_lt f hf n (s + 1)
    have := hf s
    omega

theorem range8 : List.range 8 = List.range' 0 8 := List.range_eq_range'

theorem matMulM_col (A B : ℕ) {k : ℕ} (hk : k < 8) :
    matMulM A B / 256 ^ k % 256 = matApp A (B / 256 ^ k % 256) := by
  rw [matMulM, range8, horner_byte _ (fun c => matApp_lt _ _) 8 0 k hk, Nat.zero_add]

theorem matMulM_lt (A B : ℕ) : matMulM A B < 2 ^ 64 := by
  rw [matMulM, range8, show (2 : ℕ) ^ 64 = 256 ^ 8 by norm_num]
  exact horner_lt _ (fun c => matApp_lt _ _) 8 0

theorem eq_of_bytes : ∀ (n : ℕ) {M M' : ℕ}, M < 256 ^ n → M' < 256 ^ n →
    (∀ k < n, M / 256 ^ k % 256 = M' / 256 ^ k % 256) → M = M'
  | 0, M, M', hM, hM', _ => by simp at hM hM'; omega
  | n + 1, M, M', hM, hM', h => by
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have ih := eq_of_bytes n (M := M / 256) (M' := M' / 256)
      (by rw [pow_succ'] at hM; omega) (by rw [pow_succ'] at hM'; omega) fun k hk => by
        have := h (k + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    rw [← Nat.mod_add_div M 256, ← Nat.mod_add_div M' 256, h0, ih]

theorem eq_of_cols {M M' : ℕ} (hM : M < 2 ^ 64) (hM' : M' < 2 ^ 64)
    (h : ∀ c < 8, M / 256 ^ c % 256 = M' / 256 ^ c % 256) : M = M' :=
  eq_of_bytes 8 (by rw [show (256 : ℕ) ^ 8 = 2 ^ 64 by norm_num]; exact hM)
    (by rw [show (256 : ℕ) ^ 8 = 2 ^ 64 by norm_num]; exact hM') h

theorem matApp_foldr (A : ℕ) (L : List ℕ) (b : ℕ → Bool) (x : ℕ → ℕ) :
    matApp A (L.foldr (fun c acc => (if b c then x c else 0) ^^^ acc) 0) =
      L.foldr (fun c acc => (if b c then matApp A (x c) else 0) ^^^ acc) 0 := by
  induction L with
  | nil => exact matApp_zero A
  | cons c L ih =>
    simp only [List.foldr_cons]
    rw [matApp_xor, ih]
    cases b c <;> simp [matApp_zero]

theorem foldr_congr_mem {L : List ℕ} (f g : ℕ → ℕ) (h : ∀ c ∈ L, f c = g c) :
    L.foldr (fun c acc => f c ^^^ acc) 0 = L.foldr (fun c acc => g c ^^^ acc) 0 := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.foldr_cons, List.foldr_cons, h c List.mem_cons_self,
      ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]

theorem matApp_matMulM (A B v : ℕ) : matApp (matMulM A B) v = matApp A (matApp B v) := by
  rw [matApp_eq (matMulM A B), matApp_eq B, matApp_foldr]
  exact foldr_congr_mem _ _ fun c hc => by rw [matMulM_col A B (List.mem_range.1 hc)]

theorem eq_of_span {M M' : ℕ} (hM : M < 2 ^ 64) (hM' : M' < 2 ^ 64)
    (hs : ∀ c < 8, spanA.getD c 0 ^^^ spanB.getD c 0 = 2 ^ c)
    (h : ∀ c < 8, matApp M (spanA.getD c 0) = matApp M' (spanA.getD c 0) ∧
      matApp M (spanB.getD c 0) = matApp M' (spanB.getD c 0)) : M = M' := by
  refine eq_of_cols hM hM' fun c hc => ?_
  rw [← matApp_pow M hc, ← matApp_pow M' hc, ← hs c hc, matApp_xor, matApp_xor, (h c hc).1,
    (h c hc).2]

theorem matApp_idCode : ∀ v < 256, matApp idCode v = v := by decide +kernel

theorem idCode_lt : idCode < 2 ^ 64 := by decide +kernel

theorem saMat_lt (i : ℕ) : saMat i < 2 ^ 64 := Nat.mod_lt _ (by positivity)

def Acts (g : Equiv.Perm (Fin 360)) (M : ℕ) : Prop :=
  ∀ p (hp : p < 120), ((g ⟨p, by omega⟩ : Fin 360) : ℕ) < 120 ∧
    ((g ⟨p, by omega⟩ : Fin 360) : ℕ) = nsIdx[matApp M nsArr[p]!]!

theorem acts_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin 360)} {M : ℕ} (ht : Rep 360 t g)
    (h : ActsOn0 t M) : Acts g M := fun p hp => by
  rw [← ht.apply (by omega)]
  exact h p hp

def saElt (i : ℕ) : Equiv.Perm (Fin 360) :=
  if _h : 0 < i ∧ saPar i < i then gen (sylowIdx.getD (saLab i) 0) * saElt (saPar i) else 1
termination_by i
decreasing_by exact _h.2

theorem gen_mem_sylowT {l : ℕ} (hl : l < 5) : gen (sylowIdx.getD l 0) ∈ sylowT := by
  rw [sylowT_eq]
  exact Subgroup.subset_closure ⟨l, hl, rfl⟩

theorem sylowIdx_lt {l : ℕ} (hl : l < 5) : sylowIdx.getD l 0 < 10 := by
  interval_cases l <;> decide

end CFSG.EvenSmallLie.OmegaEight

end
