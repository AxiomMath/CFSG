module

public import Certificates.Data.Kernel.LocalComp.TitsBfs
public import CFSG.Certificates.Kernel.LocalCompTits.Defs
public import CFSG.Certificates.Kernel.Spor.PChainSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CFSG.KC.LocalComp.TitsSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KS.PEnum CFSG.KS.TBfs
  CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th.Native CFSG.KC.LocalComp.Tits
  CFSG.KC.LocalComp.TitsChain
open CFSG.KS.PC (walkF walkInvF siftF mapK listEqK lvK lvAt termK invK walkF_succ walkInvF_succ
  siftF_succ mapK_eq listEqK_iff ChainHyp pchainK_sound)

namespace Chain

@[expose] noncomputable def rowT (g : Nat → Nat) : Nat → Nat :=
  fun r => pmk 32 32 fun j => g (32 * r + j)

private theorem fld_pmk32 {f : Nat → Nat} (hf : ∀ x < 32, f x < 2 ^ 32) :
    Fld 32 (pmk 32 32 f) (fun i => if i < 32 then f i else 0) := by
  have hc := clog_spec (n := 32) (by decide)
  have h := fld_pmkT 32 32 f hf (clog 32) 0
  have e : pmk 32 32 f = pmkT 32 32 f (clog 32) 0 := by
    unfold pmk
    rw [strictN_eqP]
  rw [e]
  refine fld_congr h fun i => ?_
  by_cases hi : i < 32
  · have h2 : i < 2 ^ clog 32 := by omega
    simp [hi, h2]
  · simp [hi]

theorem r32_rowT {g : Nat → Nat} (hg : ∀ k, g k < 2 ^ 32) (k : Nat) : r32 (rowT g) k = g k := by
  have h1 : r32 (rowT g) k = pg 32 (mask 32) (rowT g (k >>> 5)) (k &&& 31) := by
    unfold r32 CFSG.KS.Row.rg
    have e : Nat.add 0 (k.shiftRight 5) = k >>> 5 := Nat.zero_add _
    rw [e]
    rfl
  rw [h1]
  have h2 : k &&& 31 < 32 := by
    have := Nat.and_le_right (n := k) (m := 31)
    omega
  unfold rowT
  rw [pg_of_fld (fld_pmk32 (fun x _ => hg _)) (by simpa [h2] using hg _)]
  simp only [h2, ↓reduceIte]
  congr 1
  have : k = 32 * (k >>> 5) + (k &&& 31) := by
    rw [Nat.shiftRight_eq_div_pow]
    have := Nat.and_two_pow_sub_one_eq_mod k 5
    have e : (2:Nat) ^ 5 - 1 = 31 := by decide
    rw [e] at this
    omega
  omega

theorem m11_eq : m11 = mask 11 := rfl

theorem apL_eq (TL : Nat → Nat) (l x : Nat) : apL TL l x = pg 11 (mask 11) (TL l) x := rfl

theorem apL_lt (TL : Nat → Nat) (l x : Nat) : apL TL l x < 2048 := by
  have := pg_lt 11 (TL l) x
  rw [apL_eq]
  simpa using this

theorem getD_lt {q : List Nat} {j : Nat} (h : j < q.length) : q.getD j 0 = q[j] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ge {q : List Nat} {j : Nat} (h : q.length ≤ j) : q.getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem f16_lt (R k : Nat) : f16 R k < 65536 := by
  have := pg_lt 16 R k
  exact this

private theorem fld_orN (g : Nat → Nat) (hg : ∀ i, g i < 2 ^ 11) : ∀ c,
    Fld 11 (CFSG.KLie.CT.orN c fun j => Nat.shiftLeft (g j) (Nat.mul 11 j))
      (fun i => if i < c then g i else 0)
  | 0 => fld_congr (fld_zero 11) (fun i => by simp)
  | c + 1 => by
    have e : (CFSG.KLie.CT.orN (c + 1) fun j => Nat.shiftLeft (g j) (Nat.mul 11 j)) =
        Nat.lor (Nat.shiftLeft (g c) (Nat.mul 11 c))
          (CFSG.KLie.CT.orN c fun j => Nat.shiftLeft (g j) (Nat.mul 11 j)) := rfl
    rw [e]
    refine fld_congr (fld_or (fld_shl c (fld_one (hg c))) (fld_orN g hg c)) ?_
    intro i
    by_cases h1 : i < c
    · have h2 : ¬ c ≤ i := by omega
      have h3 : i < c + 1 := by omega
      simp only [h1, h2, h3, ↓reduceIte, Nat.zero_or]
    · by_cases h3 : i = c
      · subst h3
        simp
      · have h4 : ¬ i < c + 1 := by omega
        have h5 : c ≤ i := by omega
        have h6 : ¬ i - c = 0 := by omega
        simp only [h1, h4, h5, h6, ↓reduceIte, Nat.or_zero]

@[expose] def TupR (t : Nat) (q : List Nat) : Prop :=
  q.length = 56 ∧ ∀ j < 56, pg 11 (mask 11) t j = q.getD j 0

private theorem fld_tupOf : ∀ q : List Nat, (∀ x ∈ q, x < 2048) →
    Fld 11 (tupOf q) (fun i => q.getD i 0)
  | [], _ => fld_congr (fld_zero 11) (fun i => by simp)
  | p :: q, h => by
    have hp : p < 2 ^ 11 := h p List.mem_cons_self
    have e : tupOf (p :: q) = Nat.lor p (Nat.shiftLeft (tupOf q) 11) := rfl
    rw [e]
    refine fld_congr (fld_or (fld_one hp) (fld_shl 1 (fld_tupOf q
      fun x hx => h x (List.mem_cons_of_mem _ hx)))) ?_
    intro i
    rcases i with _ | i
    · simp
    · simp

theorem TupR_tupOf {q : List Nat} (hl : q.length = 56) (hq : ∀ x ∈ q, x < 2048) :
    TupR (tupOf q) q := by
  refine ⟨hl, fun j _ => ?_⟩
  rw [pg_of_fld (fld_tupOf q hq) ?_]
  by_cases hj : j < q.length
  · rw [getD_lt hj]
    exact hq _ (List.getElem_mem hj)
  · rw [getD_ge (by omega)]
    decide

theorem TupR_map {t : Nat} {q : List Nat} (h : TupR t q) (f : Nat → Nat) (hf : ∀ x, f x < 2048) :
    TupR (tupK 56 f t) (q.map f) := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  unfold tupK
  rw [m11_eq, pg_of_fld (fld_orN (fun j => f (pg 11 (mask 11) t j)) (fun i => hf _) 56)
    (by simp only [hj, ↓reduceIte]; exact hf _)]
  simp only [hj, ↓reduceIte]
  have hl := h.1
  rw [h.2 j hj, getD_lt (by omega), getD_lt (by simp; omega)]
  simp

theorem TupR_inj {t : Nat} {q q' : List Nat} (h : TupR t q) (h' : TupR t q') : q = q' := by
  apply List.ext_getElem (by rw [h.1, h'.1])
  intro j hj hj'
  have := (h.2 j (by have := h.1; omega)).symm.trans (h'.2 j (by have := h'.1; omega))
  rwa [getD_lt hj, getD_lt hj'] at this

open CFSG.KS.Raw.Orb in
theorem mem_levLetters {TL : Nat → Nat} {CP : List Nat} {i l : Nat} :
    l ∈ levLetters TL CP i ↔ l < 28 ∧ ∀ t < i, apL TL l (CP.getD t 0) = CP.getD t 0 := by
  unfold levLetters
  rw [List.mem_filter, List.mem_range, List.all_eq_true]
  simp only [List.mem_range, Nat.beq_eq]

open CFSG.KS.Raw.Orb in
theorem levLetters_eq_lvK (TL : Nat → Nat) (CP : List Nat) (i : Nat) :
    levLetters TL CP i = lvK (apL TL) (fun j => CP.getD j 0) 28 i := by
  unfold levLetters lvK
  apply List.filter_congr
  intro l _
  rw [Bool.eq_iff_iff, List.all_eq_true, allN_iff]
  simp only [List.mem_range, Nat.beq_eq]

theorem levLetters_length (TL : Nat → Nat) (CP : List Nat) (i : Nat) :
    (levLetters TL CP i).length ≤ 28 := by
  unfold levLetters
  calc _ ≤ (List.range 28).length := List.length_filter_le _ _
    _ = 28 := List.length_range

structure LevP (TL : Nat → Nat) (TT TS TW : Nat → Nat → Nat) (sz : Nat → Nat) (CP : List Nat)
    (i : Nat) : Prop where
  pos : 0 < sz i
  le : sz i ≤ 1755
  root : f16 (TT i 0) 0 = CP.getD i 0
  tw0 : TW i 0 = tupOf CP
  tsOf : ∀ p < 1755, if f16 (TS i p) 0 < sz i then f16 (TT i (f16 (TS i p) 0)) 0 = p
    else f16 (TS i p) 0 = 65535
  pt : ∀ k < sz i, f16 (TT i k) 0 < 1755 ∧ f16 (TS i (f16 (TT i k) 0)) 0 = k ∧
    (∀ l ∈ levLetters TL CP i, f16 (TS i (apL TL l (f16 (TT i k) 0))) 0 < sz i) ∧
    (0 < k → f16 (TT i k) 1 < k ∧ f16 (TT i k) 2 ∈ levLetters TL CP i ∧
      apL TL (f16 (TT i k) 2) (f16 (TT i (f16 (TT i k) 1)) 0) = f16 (TT i k) 0 ∧
      TW i k = tupK 56 (apL TL (f16 (TT i k) 2)) (TW i (f16 (TT i k) 1)))

open CFSG.KS.Raw.Orb in
theorem levP_of {TL : Nat → Nat} {TT TS TW : Nat → Nat → Nat} {sz : Nat → Nat} {CP : List Nat}
    {i : Nat} (h : levelOK 56 TL TT TS TW sz CP i = true) : LevP TL TT TS TW sz CP i := by
  unfold levelOK at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun p hp => ?_, fun k hk => ?_⟩
  · have := allN_iff.1 h5 p hp
    simp only [strictB_eq, bIf_eq] at this
    by_cases hc : f16 (TS i p) 0 < sz i
    · simpa [hc, Nat.beq_eq] using this
    · simpa [hc, Nat.beq_eq] using this
  · have := allN_iff.1 h6 k hk
    simp only [strictB_eq, bIf_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
      List.all_eq_true, List.contains_iff_mem] at this
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a, b, c, fun hk0 => ?_⟩
    rw [if_neg (by omega)] at d
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.contains_iff_mem] at d
    exact d

open CFSG.KS.Raw.Orb in
structure BfsP (TL : Nat → Nat) (TT TS : Nat → Nat → Nat) (sz : Nat → Nat) (CP : List Nat)
    (i : Nat) : Prop where
  inc : ∀ k, 0 < k → k + 1 < sz i →
    keyK TT (levLetters TL CP i) i k < keyK TT (levLetters TL CP i) i (k + 1)
  close : ∀ h < sz i, ∀ u < (levLetters TL CP i).length,
    f16 (TS i (apL TL ((levLetters TL CP i).getD u 0) (f16 (TT i h) 0))) 0 = 0 ∨
      keyK TT (levLetters TL CP i) i
        (f16 (TS i (apL TL ((levLetters TL CP i).getD u 0) (f16 (TT i h) 0))) 0) ≤ 32 * h + u

open CFSG.KS.Raw.Orb in
theorem bfsP_of {TL : Nat → Nat} {TT TS : Nat → Nat → Nat} {sz : Nat → Nat} {CP : List Nat}
    {i : Nat} (h : bfsOK TL TT TS sz CP i = true) : BfsP TL TT TS sz CP i := by
  unfold bfsOK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun k hk hk1 => ?_, fun h' hh u hu => ?_⟩
  · have := allN_iff.1 h1 (k - 1) (by show k - 1 < sz i - 2; omega)
    simp only [Nat.blt_eq] at this
    have e1 : Nat.succ (k - 1) = k := by omega
    rw [e1] at this
    exact this
  · have := allN_iff.1 (allN_iff.1 h2 h' hh) u hu
    simp only [strictB_eq, bIf_eq] at this
    by_cases hz : f16 (TS i (apL TL ((levLetters TL CP i).getD u 0) (f16 (TT i h') 0))) 0 = 0
    · exact Or.inl hz
    · right
      simp only [hz, Nat.beq_eq, ite_false, Bool.false_eq_true] at this
      simpa [Nat.ble_eq] using this

@[expose] noncomputable def gPts (TT : Nat → Nat → Nat) (i k : Nat) : Nat := f16 (TT i k) 0

@[expose] noncomputable def gPar (TT : Nat → Nat → Nat) (i k : Nat) : Nat := if k = 0 then 0 else f16 (TT i k) 1

@[expose] noncomputable def gLab (TT : Nat → Nat → Nat) (i k : Nat) : Nat := if k = 0 then 0 else f16 (TT i k) 2

@[expose] noncomputable def gPos (TS : Nat → Nat → Nat) (sz : Nat → Nat) (i z : Nat) : Nat :=
  if f16 (TS i z) 0 < sz i then f16 (TS i z) 0 else 4294967295

@[expose] noncomputable def gTi (TL : Nat → Nat) (TT : Nat → Nat → Nat) (CP : List Nat) (i k : Nat) : Nat :=
  (levLetters TL CP i).idxOf (gLab TT i k)

@[expose] noncomputable def tPts (TT : Nat → Nat → Nat) : Nat → Nat → Nat := fun i => rowT (gPts TT i)
@[expose] noncomputable def tPar (TT : Nat → Nat → Nat) : Nat → Nat → Nat := fun i => rowT (gPar TT i)
@[expose] noncomputable def tLab (TT : Nat → Nat → Nat) : Nat → Nat → Nat := fun i => rowT (gLab TT i)
@[expose] noncomputable def tPos (TS : Nat → Nat → Nat) (sz : Nat → Nat) : Nat → Nat → Nat :=
  fun i => rowT (gPos TS sz i)
@[expose] noncomputable def tTi (TL : Nat → Nat) (TT : Nat → Nat → Nat) (CP : List Nat) :
    Nat → Nat → Nat := fun i => rowT (gTi TL TT CP i)

theorem r32_tPts (TT : Nat → Nat → Nat) (i k : Nat) : r32 (tPts TT i) k = f16 (TT i k) 0 :=
  r32_rowT (fun k => by have := f16_lt (TT i k) 0; unfold gPts; omega) k

theorem r32_tPar (TT : Nat → Nat → Nat) (i k : Nat) : r32 (tPar TT i) k = gPar TT i k :=
  r32_rowT (fun k => by
    have := f16_lt (TT i k) 1
    unfold gPar; split_ifs <;> omega) k

theorem r32_tLab (TT : Nat → Nat → Nat) (i k : Nat) : r32 (tLab TT i) k = gLab TT i k :=
  r32_rowT (fun k => by
    have := f16_lt (TT i k) 2
    unfold gLab; split_ifs <;> omega) k

theorem r32_tPos (TS : Nat → Nat → Nat) (sz : Nat → Nat) (i z : Nat) :
    r32 (tPos TS sz i) z = gPos TS sz i z :=
  r32_rowT (fun k => by
    have := f16_lt (TS i k) 0
    unfold gPos; split_ifs <;> omega) z

theorem r32_tTi (TL : Nat → Nat) (TT : Nat → Nat → Nat) (CP : List Nat) (i k : Nat) :
    r32 (tTi TL TT CP i) k = gTi TL TT CP i k :=
  r32_rowT (fun k => by
    have h1 := levLetters_length TL CP i
    have h2 := List.idxOf_le_length (a := gLab TT i k) (l := levLetters TL CP i)
    unfold gTi; omega) k

theorem invLK_eq (l : Nat) : invLK l = Nat.xor l 1 := by
  rw [CFSG.KS.PC.xor_one]
  unfold invLK CFSG.Perm.Native.invL
  rw [CFSG.KS.Raw.Orb.nIf_eq]
  simp only [Nat.beq_eq, Nat.and_one_is_mod]
  by_cases h : l % 2 = 0
  · simp [h]
  · simp [h]

theorem walkInvF_zero (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (F : Nat) (q : List Nat) :
    walkInvF L PAR LAB F 0 q = q := by
  cases F with
  | zero => rfl
  | succ F => rw [walkInvF_succ, if_neg (by simp)]

section Walk

variable {TL : Nat → Nat} {TT TS TW : Nat → Nat → Nat} {sz : Nat → Nat} {CP : List Nat} {i : Nat}

theorem walkF_tw (hL : LevP TL TT TS TW sz CP i) (hCP : TupR (tupOf CP) CP) :
    ∀ F k, k < sz i → k ≤ F →
      TupR (TW i k) (walkF (apL TL) (tPar TT i) (tLab TT i) F k CP) := by
  intro F
  induction F with
  | zero =>
    intro k hk hkF
    obtain rfl : k = 0 := by omega
    rw [hL.tw0]
    exact hCP
  | succ F ih =>
    intro k hk hkF
    rw [walkF_succ, r32_tPar, r32_tLab]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_neg (by simp [gPar]), hL.tw0]
      exact hCP
    · obtain ⟨-, -, -, hpt⟩ := hL.pt k hk
      obtain ⟨hlt, -, -, htw⟩ := hpt (by omega)
      have hc : 0 < k ∧ gPar TT i k < k := ⟨by omega, by simpa [gPar, hk0] using hlt⟩
      rw [if_pos hc, mapK_eq]
      have h1 := ih (f16 (TT i k) 1) (by omega) (by omega)
      rw [htw]
      simpa [gLab, gPar, hk0] using TupR_map h1 (apL TL (f16 (TT i k) 2)) (apL_lt _ _)

theorem walkInv_cmp (hL : LevP TL TT TS TW sz CP i) :
    ∀ f k, k < sz i → depthK TT i f k = true → ∀ F, k ≤ F → ∀ t q, TupR t q →
      TupR (walkInvK 56 TL TT i f k t)
        (walkInvF (apL TL) (tPar TT i) (tLab TT i) F k q) := by
  intro f
  induction f with
  | zero =>
    intro k hk hd F hkF t q htq
    have hk0 : k = 0 := by simpa [depthK, Nat.beq_eq] using hd
    subst hk0
    rw [walkInvF_zero]
    exact htq
  | succ f ih =>
    intro k hk hd F hkF t q htq
    by_cases hk0 : k = 0
    · subst hk0
      rw [walkInvF_zero]
      simpa [walkInvK, CFSG.KS.Raw.Orb.nIf_eq, Nat.beq_eq] using htq
    · have hd' : depthK TT i f (f16 (TT i k) 1) = true := by
        simpa [depthK, CFSG.KS.Raw.Orb.bIf_eq, Nat.beq_eq, hk0] using hd
      obtain ⟨-, -, -, hpt⟩ := hL.pt k hk
      obtain ⟨hlt, hlab, -, -⟩ := hpt (by omega)
      obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hc : 0 < k ∧ gPar TT i k < k := ⟨by omega, by simpa [gPar, hk0] using hlt⟩
      rw [walkInvF_succ, r32_tPar, r32_tLab, if_pos hc, mapK_eq]
      have e : walkInvK 56 TL TT i (f + 1) k t =
          walkInvK 56 TL TT i f (f16 (TT i k) 1)
            (tupK 56 (apL TL (invLK (f16 (TT i k) 2))) t) := by
        simp only [walkInvK, CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.strictN_eq, Nat.beq_eq, hk0,
          if_false]
      rw [e]
      have h1 := ih (f16 (TT i k) 1) (by omega) hd' F (by simp [gPar, hk0] at hc ⊢; omega) _ _
        (TupR_map htq (apL TL (invLK (f16 (TT i k) 2))) (apL_lt _ _))
      simp only [gPar, gLab, hk0, if_false, invLK_eq] at h1 ⊢
      exact h1

theorem sift_cmp (hLv : ∀ j < 4, LevP TL TT TS TW sz CP j)
    (hdp : ∀ j < 4, ∀ k < sz j, depthK TT j 64 k = true) (hCP : TupR (tupOf CP) CP) :
    ∀ f j, j + f ≤ 4 → ∀ t q, TupR t q →
      siftK 56 TL TT TS sz (tupOf CP) f j t = true →
      siftF (apL TL) (tPos TS sz) (tPar TT) (tLab TT) sz (fun j => j) CP f j q = true := by
  intro f
  induction f with
  | zero =>
    intro j _ t q htq h
    have h1 : t = tupOf CP := by simpa [siftK, Nat.beq_eq] using h
    subst h1
    exact (listEqK_iff _ _).2 (TupR_inj hCP htq).symm
  | succ f ih =>
    intro j hj t q htq h
    have hj4 : j < 4 := by omega
    have hy : pg 11 m11 t j = q.getD j 0 := by
      rw [m11_eq]
      exact htq.2 j (by omega)
    simp only [siftK, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
      Nat.blt_eq, hy] at h
    obtain ⟨hky, h2⟩ := h
    rw [siftF_succ, r32_tPos, Bool.and_eq_true]
    have hpos : gPos TS sz j (q.getD j 0) = f16 (TS j (q.getD j 0)) 0 := by
      unfold gPos
      rw [if_pos hky]
    rw [hpos]
    refine ⟨by simpa using hky, ?_⟩
    refine ih (j + 1) (by omega) _ _ ?_ h2
    exact walkInv_cmp (hLv j hj4) 64 _ hky (hdp j hj4 _ hky) _ (Nat.le_refl _) t q htq

theorem sch_cmp (hLv : ∀ j < 4, LevP TL TT TS TW sz CP j)
    (hdp : ∀ j < 4, ∀ k < sz j, depthK TT j 64 k = true) (hCP : TupR (tupOf CP) CP)
    (hi : i < 4) {k : Nat} (hk : k < sz i) {l : Nat}
    (h : schK 56 TL TT TS TW sz (tupOf CP) i l k = true) :
    CFSG.KS.PC.schK (apL TL) (tPts TT) (tPos TS sz) (tPar TT) (tLab TT) sz (fun j => j) CP 4 i l
      k = true := by
  simp only [schK, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
    Nat.blt_eq] at h
  obtain ⟨hky, h2⟩ := h
  unfold CFSG.KS.PC.schK
  rw [r32_tPts, r32_tPos, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true]
  have hpos : gPos TS sz i (apL TL l (f16 (TT i k) 0)) =
      f16 (TS i (apL TL l (f16 (TT i k) 0))) 0 := by
    unfold gPos
    rw [if_pos hky]
  rw [hpos]
  refine ⟨by simpa using hky, ?_⟩
  have h3 : TupR (tupK 56 (apL TL l) (TW i k))
      (mapK (apL TL l) (CFSG.KS.PC.walkK (apL TL) (tPar TT i) (tLab TT i) k CP)) := by
    rw [mapK_eq]
    exact TupR_map (walkF_tw (hLv i hi) hCP k k hk (Nat.le_refl _)) (apL TL l) (apL_lt _ _)
  have h4 := walkInv_cmp (hLv i hi) 64 _ hky (hdp i hi _ hky) _ (Nat.le_refl _) _ _ h3
  unfold CFSG.KS.PC.siftK
  have e : Nat.sub 4 (Nat.succ i) = Nat.sub 3 i := by
    show 4 - (i + 1) = 3 - i
    omega
  rw [e]
  exact sift_cmp hLv hdp hCP (3 - i) (i + 1) (by omega) _ _ h4 h2

theorem term_cmp (hCP : TupR (tupOf CP) CP) (h : terminalOK 56 TL CP = true) :
    termK (apL TL) (fun j => CP.getD j 0) 28 4 CP = true := by
  unfold termK
  rw [← levLetters_eq_lvK, List.all_eq_true]
  intro l hl
  unfold terminalOK at h
  rw [List.all_eq_true] at h
  have h1 := h l hl
  rw [Nat.beq_eq] at h1
  have h2 := TupR_map hCP (apL TL l) (apL_lt _ _)
  rw [h1] at h2
  rw [listEqK_iff, mapK_eq]
  exact TupR_inj hCP h2 |>.symm

end Walk

open CFSG.KS.Raw.Orb in
theorem hdK_of {n root cnt : Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : Hd n root cnt PTS POS PAR LAB) : tbfsHdK n root cnt PTS POS PAR LAB = true := by
  unfold tbfsHdK none32K
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq]
  refine ⟨h.cnt_pos, h.cnt_le, h.n_lt, h.root, h.par0, h.lab0, allN_iff.2 fun z hz => ?_⟩
  rw [strictB_eq, bIf_eq]
  rcases h.pos z hz with h1 | ⟨h1, h2⟩
  · simp [h1]
  · have := h.cnt_le
    have := h.n_lt
    have : r32 POS z ≠ 4294967295 := by omega
    simp [this, bAnd_eq, Nat.blt_eq, Nat.beq_eq, h1, h2]

open CFSG.KS.Raw.Orb in
theorem ptK_of {n cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {k : Nat}
    (h : Pt n cnt r L LV PTS POS PAR LAB TI k) :
    tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  unfold tbfsPtK
  rw [strictB_eq]
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  refine ⟨h.lt, h.pos, ?_, allN_iff.2 fun t ht => ?_⟩
  · by_cases hk : k = 0
    · subst hk
      simp [bIf_eq]
    · obtain ⟨a1, a2, a3, a4, a5⟩ := h.tree (Nat.pos_of_ne_zero hk)
      rw [bIf_eq, if_neg (by simpa [Nat.beq_eq] using hk), strictB_eq, strictB_eq]
      simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, bIf_eq]
      refine ⟨a1, a2, a3, a4, ?_⟩
      by_cases hc : k + 1 < cnt
      · have hc' : Nat.succ k < cnt := hc
        simp only [Nat.blt_eq, hc', ite_true]
        exact lexLtK_iff.2 (a5 hc)
      · have hc' : ¬ Nat.succ k < cnt := hc
        simp [hc']
  · obtain ⟨c1, c2, c3⟩ := h.close t ht
    rw [strictB_eq]
    simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, strictB_eq, bIf_eq, Nat.beq_eq]
    refine ⟨c1, c2, ?_⟩
    rcases c3 with c3 | c3
    · simp [c3]
    · by_cases h0 : r32 POS (L (LV t) (r32 PTS k)) = 0
      · simp [h0]
      · have : ¬ Raw.lexLtK k t (r32 PAR (r32 POS (L (LV t) (r32 PTS k))))
            (r32 TI (r32 POS (L (LV t) (r32 PTS k)))) = true := fun e => c3 (lexLtK_iff.1 e)
        simp [h0, this]

section Tables

variable {TL : Nat → Nat} {TT TS TW : Nat → Nat → Nat} {sz : Nat → Nat} {CP : List Nat} {i : Nat}

theorem hd_tables (hL : LevP TL TT TS TW sz CP i) :
    Hd 1755 (CP.getD i 0) (sz i) (tPts TT i) (tPos TS sz i) (tPar TT i) (tLab TT i) where
  cnt_pos := hL.pos
  cnt_le := hL.le
  n_lt := by omega
  root := by rw [r32_tPts]; exact hL.root
  par0 := by rw [r32_tPar]; simp [gPar]
  lab0 := by rw [r32_tLab]; simp [gLab]
  pos := fun z hz => by
    rw [r32_tPos]
    have h1 := hL.tsOf z hz
    have h2 := hL.le
    unfold gPos
    by_cases hc : f16 (TS i z) 0 < sz i
    · right
      rw [if_pos hc, r32_tPts]
      rw [if_pos hc] at h1
      exact ⟨hc, h1⟩
    · left
      rw [if_neg hc]

theorem pt_tables (hL : LevP TL TT TS TW sz CP i) (hB : BfsP TL TT TS sz CP i)
    (hmap : ∀ l < 28, ∀ x < 1755, apL TL l x < 1755) {k : Nat} (hk : k < sz i) :
    Pt 1755 (sz i) (lvK (apL TL) (fun j => CP.getD j 0) 28 i).length (apL TL)
      (lvAt (apL TL) (fun j => CP.getD j 0) 28 i) (tPts TT i) (tPos TS sz i) (tPar TT i)
      (tLab TT i) (tTi TL TT CP i) k := by
  have hLV : lvAt (apL TL) (fun j => CP.getD j 0) 28 i =
      fun t => (levLetters TL CP i).getD t 0 := by
    funext t
    unfold lvAt
    rw [← levLetters_eq_lvK]
  rw [hLV, ← levLetters_eq_lvK]
  have hlen := levLetters_length TL CP i
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hL.pt k hk
  have hmem : ∀ t < (levLetters TL CP i).length, (levLetters TL CP i).getD t 0 ∈
      levLetters TL CP i := fun t ht => by
    rw [getD_lt ht]
    exact List.getElem_mem ht
  refine ⟨?_, ?_, fun hk0 => ?_, fun t ht => ?_⟩
  · rw [r32_tPts]; exact hp1
  · rw [r32_tPts, r32_tPos]
    unfold gPos
    rw [hp2, if_pos hk]
  · obtain ⟨q1, q2, q3, q4⟩ := hp4 hk0
    have hk0' : k ≠ 0 := by omega
    have hq2 : (levLetters TL CP i).idxOf (f16 (TT i k) 2) < (levLetters TL CP i).length :=
      List.idxOf_lt_length_of_mem q2
    have hgl : (levLetters TL CP i).getD ((levLetters TL CP i).idxOf (f16 (TT i k) 2)) 0 =
        f16 (TT i k) 2 := by
      rw [getD_lt hq2, List.getElem_idxOf]
    simp only [r32_tPar, r32_tLab, r32_tTi, r32_tPts, gPar, gLab, gTi, hk0', if_false, hgl]
    refine ⟨q1, hq2, trivial, q3, fun hk1 => ?_⟩
    · have h1 := hB.inc k hk0 (by omega)
      have hk1' : k + 1 ≠ 0 := by omega
      unfold TitsChain.keyK at h1
      simp only [Nat.add_eq, Nat.mul_eq] at h1
      have h2 := List.idxOf_le_length (a := f16 (TT i k) 2) (l := levLetters TL CP i)
      have h3 := List.idxOf_le_length (a := f16 (TT i (k + 1)) 2) (l := levLetters TL CP i)
      simp only [hk1', if_false]
      unfold LexLt
      omega
  · have htm := hmem t ht
    have hl28 := (mem_levLetters.1 htm).1
    have hlt : apL TL ((levLetters TL CP i).getD t 0) (f16 (TT i k) 0) < 1755 :=
      hmap _ hl28 _ hp1
    have hpos := hp3 _ htm
    have hg : gPos TS sz i (apL TL ((levLetters TL CP i).getD t 0) (f16 (TT i k) 0)) =
        f16 (TS i (apL TL ((levLetters TL CP i).getD t 0) (f16 (TT i k) 0))) 0 := by
      unfold gPos
      rw [if_pos hpos]
    simp only [r32_tPts, r32_tPos, hg]
    refine ⟨hlt, hpos, ?_⟩
    rcases hB.close k hk t ht with h0 | h0
    · exact Or.inl h0
    · by_cases hz : f16 (TS i (apL TL ((levLetters TL CP i).getD t 0) (f16 (TT i k) 0))) 0 = 0
      · exact Or.inl hz
      · right
        rw [r32_tPar, r32_tTi]
        simp only [gPar, gTi, gLab, hz, if_false]
        unfold TitsChain.keyK at h0
        simp only [Nat.add_eq, Nat.mul_eq] at h0
        have h2 := List.idxOf_le_length (a := f16 (TT i
          (f16 (TS i (apL TL ((levLetters TL CP i).getD t 0) (f16 (TT i k) 0))) 0)) 2)
          (l := levLetters TL CP i)
        unfold LexLt
        omega

end Tables

theorem tabP_get {N P i : Nat} (hi : i < N) :
    (tabP N P)[i]! = UInt32.ofNat (pg 11 (mask 11) P i) := by
  unfold tabP
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ap_tabP_lt {N P i : Nat} (hi : i < N) : ap (tabP N P) i = pg 11 (mask 11) P i := by
  unfold ap
  rw [tabP_get hi, UInt32.toNat_ofNat']
  have := pg_lt 11 P i
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by simpa using this) (by decide))

theorem perm_facts {p q : Nat} (h : permOK 1755 11 (mask 11) (1755 * 11) p q = true) :
    (∀ x < 1755, pg 11 (mask 11) p x < 1755) ∧ (∀ x < 1755, pg 11 (mask 11) q x < 1755) ∧
      ∀ x < 1755, pg 11 (mask 11) q (pg 11 (mask 11) p x) = x := by
  obtain ⟨-, -, h3⟩ := CFSG.KS.PK.permOK_iff.1 h
  have hpg : ∀ p x, pg 11 (mask 11) p x = CFSG.KS.PK.fd 11 p x := fun p x => by
    rw [CFSG.KS.PK.pg_eq]
    rfl
  simp only [hpg]
  refine ⟨fun x hx => (h3 x hx).1, fun y hy => ?_, fun x hx => (h3 x hx).2⟩
  obtain ⟨x, hx, rfl⟩ := CFSG.KS.PK.surj_of_inj (f := CFSG.KS.PK.fd 11 p)
    (fun x hx => (h3 x hx).1)
    (fun i hi j hj e => by
      have := (h3 i hi).2
      rw [e, (h3 j hj).2] at this
      exact this.symm) y hy
  rw [(h3 x hx).2]
  exact hx

theorem letters_map {TL : Nat → Nat}
    (hp : ∀ j < 14, permOK 1755 11 (mask 11) (1755 * 11) (TL (2 * j)) (TL (2 * j + 1)) = true) :
    ∀ l < 28, ∀ x < 1755, apL TL l x < 1755 := by
  intro l hl x hx
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · exact (perm_facts (hp j (by omega))).1 x hx
  · exact (perm_facts (hp j (by omega))).2.1 x hx

open CFSG.KS.Raw.Orb in
theorem invK_of {TL : Nat → Nat}
    (hp : ∀ j < 14, permOK 1755 11 (mask 11) (1755 * 11) (TL (2 * j)) (TL (2 * j + 1)) = true) :
    invK (apL TL) 1755 28 = true := by
  unfold invK
  rw [allN_iff]
  intro j hj
  have e : Nat.div 28 2 = 14 := rfl
  rw [e] at hj
  rw [allN_iff]
  intro x hx
  obtain ⟨hp1, hq1, hpq⟩ := perm_facts (hp j hj)
  rw [strictB_eq]
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.mul_eq, Nat.succ_eq_add_one]
  exact ⟨hp1 x hx, hq1 x hx, hpq x hx⟩

end Chain

open Chain

open CFSG.KC.LocalComp.TitsChain CFSG.Perm.Native in
theorem chain_sound {TL : Nat → Nat} {TT TS TW : Nat → Nat → Nat} {sz : Nat → Nat}
    {CP : List Nat} {letters : Array Table} {base Q qb : Array Nat}
    (hL : letters = Array.ofFn (n := 28) fun l => tabP 1755 (TL l.val))
    (hp : ∀ j < 14, permOK 1755 11 (mask 11) (1755 * 11) (TL (2 * j)) (TL (2 * j + 1)) = true)
    (hcp : CP.length = 56) (hcpN : ∀ t < 56, CP.getD t 0 < 1755)
    (hbase : base = (CP.take 4).toArray) (hQ : Q = CP.toArray) (hqb : qb = Array.range 4)
    (hv : ∀ i < 4, levelOK 56 TL TT TS TW sz CP i = true)
    (hb : ∀ i < 4, bfsOK TL TT TS sz CP i = true) (hd : ∀ i < 4, depthOK TT sz i = true)
    (hs : ∀ i < 4, ∀ c < 28,
      schRange 56 TL TT TS TW sz (tupOf CP) i (levLetters TL CP i) (64 * c) 64 = true)
    (ht : terminalOK 56 TL CP = true) :
    chainOK 1755 letters base Q qb (chainTrees 1755 letters base) 3 = true ∧
      orbitSizes (chainTrees 1755 letters base) = (List.range 4).map sz := by
  subst hL hbase hQ hqb
  have hmap := letters_map hp
  have hlt2048 : ∀ x ∈ CP, x < 2048 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    have := hcpN t (by omega)
    rw [getD_lt ht] at this
    omega
  have hCP : TupR (tupOf CP) CP := TupR_tupOf hcp hlt2048
  have hLv : ∀ j < 4, LevP TL TT TS TW sz CP j := fun j hj => levP_of (hv j hj)
  have hBf : ∀ j < 4, BfsP TL TT TS sz CP j := fun j hj => bfsP_of (hb j hj)
  have hdp : ∀ j < 4, ∀ k < sz j, depthK TT j 64 k = true := fun j hj k hk =>
    CFSG.KS.Raw.Orb.allN_iff.1 (hd j hj) k hk
  have H : ChainHyp 1755 28 4 (Array.ofFn (n := 28) fun l => tabP 1755 (TL l.val))
      (CP.take 4).toArray CP.toArray (Array.range 4) (apL TL) (fun j => CP.getD j 0) CP
      (fun i => i) sz (tPts TT) (tPos TS sz) (tPar TT) (tLab TT) (tTi TL TT CP) := by
    refine ⟨⟨by simp, fun l hl x hx => ?_⟩, ⟨by decide, invK_of hp⟩, ⟨?_, fun i hi => ?_⟩,
      ⟨by simp, fun t ht => ?_, by simp, fun i hi => ?_⟩, fun i hi => ?_⟩
    · rw [ofFn_get (c := 28) (f := fun l => tabP 1755 (TL l)) hl, ap_tabP_lt hx]
      rfl
    · simp [hcp]
    · refine ⟨?_, hcpN i (by omega)⟩
      have hi' : i < (CP.take 4).length := by simp [hcp]; omega
      rw [getElem!_pos _ i (by simpa using hi'), getD_lt (show i < CP.length by omega)]
      simp
    · exact hcpN t (by omega)
    · refine ⟨?_, by omega, rfl⟩
      rw [getElem!_pos _ i (by simpa using hi)]
      simp
    · exact ⟨hdK_of (hd_tables (hLv i hi)), fun k hk =>
        ptK_of (pt_tables (hLv i hi) (hBf i hi) hmap hk)⟩
  have hsch : ∀ i < 4, ∀ k < sz i, ∀ t < (lvK (apL TL) (fun j => CP.getD j 0) 28 i).length,
      CFSG.KS.PC.schK (apL TL) (tPts TT) (tPos TS sz) (tPar TT) (tLab TT) sz (fun j => j) CP 4 i
        (lvAt (apL TL) (fun j => CP.getD j 0) 28 i t) k = true := by
    intro i hi k hk t ht
    have hmem : lvAt (apL TL) (fun j => CP.getD j 0) 28 i t ∈ levLetters TL CP i := by
      rw [levLetters_eq_lvK]
      exact CFSG.KS.PC.lvAt_mem ht
    have hc : k / 64 < 28 := by
      have := (hLv i hi).le
      omega
    have h1 := hs i hi (k / 64) hc
    unfold schRange at h1
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 (k % 64) (Nat.mod_lt _ (by decide))
    have e : Nat.add (64 * (k / 64)) (k % 64) = k := by
      show 64 * (k / 64) + k % 64 = k
      omega
    simp only [CFSG.KS.Raw.Orb.bIf_eq, e, Nat.blt_eq, if_pos hk, List.all_eq_true] at h2
    exact sch_cmp hLv hdp hCP hi hk (h2 _ hmem)
  obtain ⟨h1, h2⟩ := CFSG.KS.PC.pchainK_sound H hsch (term_cmp hCP ht)
  refine ⟨h2 3, ?_⟩
  rw [h1]
  unfold orbitSizes tbfsRec
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_map, Array.getElem_ofFn]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at h2; omega
    rcases this with rfl | rfl | rfl | rfl <;> rfl

end CFSG.KC.LocalComp.TitsSound

end
