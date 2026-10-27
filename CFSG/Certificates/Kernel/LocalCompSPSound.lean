module

public import CFSG.Certificates.Kernel.LocalCompSPCode
public import Certificates.Data.Kernel.WeylE8.U
public import CFSG.Certificates.Kernel.LocalCompFrameSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def listPermArrL (L : List (List ℤ)) (l : List ℕ) : Array ℕ :=
  Array.ofFn (n := 240) fun i => L.idxOf (listPermVec l (L.getD i.val []))

@[expose] def spArrL (L : List (List ℤ)) (m : ℕ) (l : List ℕ) : Array ℕ :=
  compA 240 (signArrsL L)[m]! (listPermArrL L l)

@[expose] noncomputable def spArrC (L : List (List ℤ)) (c : ℕ) : Array ℕ :=
  spArrL L (spMask c) (codeL c)

structure SPBind (L : List (List ℤ)) (K : List ℕ) (RK RT ST FT PT : Nat → Nat)
    (SO NEG FR DP KP : Nat) : Prop where
  bind : bindRoots RK L = true
  sorted : sortedOK RK SO = true
  refl : ∀ r < 240, reflRowOK RK r (RT r) = true
  neg : negTabOK RK NEG = true
  sign : ∀ m < 256, signRowOK RK m (ST m) = true
  froots : frameRootsOK RK FR = true
  frame0 : frameRowOK RK FR 0 (FT 0) = true
  frame : ∀ k < 8, frameRowOK RK FR (1 <<< k) (FT (1 <<< k)) = true
  homF : homF FT = true
  pairs : bindPairs DP dPairs = true
  swaps : d5K RK RT PT DP = true
  keys : bindList K 8 KP = true
  links : linksOK RT ST FT PT NEG KP = true
  rootsD : rootsDK RK DP = true

theorem spArr_eq (m : ℕ) (l : List ℕ) : spArr m l = spArrL rootList m l := rfl

end CFSG.KLC.E8

end

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

noncomputable def spFlip (m : ℕ) (x : List ℤ) : List ℤ :=
  (List.finRange 8).map fun k => if frameDecode m k = 1 then -x.getD k 0 else x.getD k 0

noncomputable def spVec (c : ℕ) (x : List ℤ) : List ℤ := spFlip (spMask c) (listPermVec (codeL c) x)

theorem spFin_getD (f : Fin 8 → ℤ) {j : ℕ} (hj : j < 8) :
    ((List.finRange 8).map f).getD j 0 = f ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem spOfFn_getD (f : Fin 8 → ℤ) {j : ℕ} (hj : j < 8) : (List.ofFn f).getD j 0 = f ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

theorem spRange_getD (f : ℕ → ℤ) {j : ℕ} (hj : j < 8) : ((List.range 8).map f).getD j 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem spExt8 {x y : List ℤ} (hx : x.length = 8) (hy : y.length = 8)
    (h : ∀ j < 8, x.getD j 0 = y.getD j 0) : x = y := by
  apply List.ext_getElem (by omega)
  intro j h1 h2
  have := h j (by omega)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem spNeg_getD (x : List ℤ) (j : ℕ) : (x.map (-·)).getD j 0 = -x.getD j 0 := by
  by_cases hj : j < x.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega), neg_zero]

theorem spDecode_one (m : ℕ) (k : Fin 8) : (frameDecode m k = 1) = (m.testBit k = true) := by
  by_cases h : m.testBit k = true <;> simp [frameDecode, h]

theorem spFlip_length (m : ℕ) (x : List ℤ) : (spFlip m x).length = 8 := by simp [spFlip]

theorem spVec_length (c : ℕ) (x : List ℤ) : (spVec c x).length = 8 := spFlip_length _ _

theorem spFlip_getD (m : ℕ) (x : List ℤ) {j : ℕ} (hj : j < 8) :
    (spFlip m x).getD j 0 = if m.testBit j then -x.getD j 0 else x.getD j 0 := by
  rw [spFlip, spFin_getD _ hj]
  simp only [spDecode_one]

theorem spPerm_getD (l : List ℕ) (x : List ℤ) {j : ℕ} (hj : j < 8) :
    (listPermVec l x).getD j 0 = x.getD (l.idxOf j) 0 := by
  rw [listPermVec, spRange_getD _ hj]

theorem spVec_getD (c : ℕ) (x : List ℤ) {j : ℕ} (hj : j < 8) :
    (spVec c x).getD j 0 = if (spMask c).testBit j then -x.getD ((codeL c).idxOf j) 0
      else x.getD ((codeL c).idxOf j) 0 := by
  rw [spVec, spFlip_getD _ _ hj, spPerm_getD _ _ hj]

theorem spVec_neg (c : ℕ) (x : List ℤ) : spVec c (x.map (-·)) = (spVec c x).map (-·) := by
  apply spExt8 (spVec_length _ _) (by simp [spVec_length])
  intro j hj
  rw [spNeg_getD, spVec_getD _ _ hj, spVec_getD _ _ hj, spNeg_getD]
  split_ifs <;> rfl

theorem spNeg_neg (x : List ℤ) : (x.map (-·)).map (-·) = x := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id x]
  congr 1
  funext y
  simp

theorem spIdx_lt {c : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) {j : ℕ} (hj : j < 8) : (codeL c).idxOf j < 8 := by
  have := List.idxOf_lt_length_of_mem (h2 j hj)
  rwa [codeL_length] at this

theorem spAt_idx {c : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) {j : ℕ} (hj : j < 8) :
    spAt c ((codeL c).idxOf j) = j := by
  have hl := spIdx_lt h2 hj
  rw [← codeL_getD c hl, List.getD_eq_getElem _ _ (by rw [codeL_length]; exact hl)]
  exact List.getElem_idxOf _

theorem spNodup {c : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) : (codeL c).Nodup := by
  obtain ⟨e, he⟩ := codeL_perm h2
  unfold codeL
  refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
  have hx' := List.mem_range.1 hx
  have hy' := List.mem_range.1 hy
  have : e ⟨x, hx'⟩ = e ⟨y, hy'⟩ := Fin.ext (by rw [he, he]; exact hxy)
  exact congrArg Fin.val (e.injective this)

theorem spIdx_at {c : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) {k : ℕ} (hk : k < 8) :
    (codeL c).idxOf (spAt c k) = k := by
  have e : spAt c k = (codeL c)[k]'(by rw [codeL_length]; exact hk) := by
    rw [← codeL_getD c hk, List.getD_eq_getElem _ _ (by rw [codeL_length]; exact hk)]
  rw [e]
  exact (spNodup h2).idxOf_getElem k _

theorem spIdx_e {c : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) {e : Equiv.Perm (Fin 8)}
    (he : ∀ j : Fin 8, (e j : ℕ) = spAt c j) (j : ℕ) (hj : j < 8) :
    (codeL c).idxOf j = (e.symm ⟨j, hj⟩ : ℕ) := by
  have h := he (e.symm ⟨j, hj⟩)
  rw [Equiv.apply_symm_apply] at h
  calc (codeL c).idxOf j = (codeL c).idxOf (spAt c (e.symm ⟨j, hj⟩)) := by rw [← h]
    _ = _ := spIdx_at h2 (e.symm _).isLt

theorem spBitsum_bit : ∀ f : Fin 8 → Bool, ∀ j : Fin 8, (bitsum f).testBit j = f j := by
  decide +kernel

theorem spBitsum_self : ∀ m < 256, bitsum (fun k => m.testBit k) = m := by
  decide +kernel

theorem spImg_bit {c : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) (m : ℕ) {j : ℕ} (hj : j < 8) :
    (imgMaskC (codeL c) m).testBit j = m.testBit ((codeL c).idxOf j) := by
  obtain ⟨e, he⟩ := codeL_perm h2
  have hI : imgMaskC (codeL c) m = bitsum fun i => m.testBit (e.symm i) := by
    rw [imgMaskC, bitsum, Finset.sum_range (fun j => if m.testBit j then 2 ^ (codeL c).getD j 0
      else 0), ← Equiv.sum_comp e (fun i => if m.testBit (e.symm i) then 2 ^ (i : ℕ) else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.symm_apply_apply, codeL_getD c j.2, he j]
  rw [hI, spIdx_e h2 he j hj]
  exact spBitsum_bit _ ⟨j, hj⟩

theorem spMul_idx {a b : ℕ} (ha : okC a = true) (hb : okC b = true) {j : ℕ} (hj : j < 8) :
    (codeL (spMul a b)).idxOf j = (codeL b).idxOf ((codeL a).idxOf j) := by
  obtain ⟨-, ha2, -, -⟩ := okC_spec ha
  obtain ⟨-, hb2, -, -⟩ := okC_spec hb
  obtain ⟨-, hab2, -, -⟩ := okC_spec (okC_mul ha hb)
  have h1 := spIdx_lt ha2 hj
  have h2 := spIdx_lt hb2 h1
  have e : spAt (spMul a b) ((codeL b).idxOf ((codeL a).idxOf j)) = j := by
    rw [spAt_mul a b h2, spAt_idx hb2 h1, spAt_idx ha2 hj]
  calc (codeL (spMul a b)).idxOf j
      = (codeL (spMul a b)).idxOf (spAt (spMul a b) ((codeL b).idxOf ((codeL a).idxOf j))) := by
        rw [e]
    _ = _ := spIdx_at hab2 h2

theorem spMul_bit {a b : ℕ} (ha : okC a = true) {j : ℕ} (hj : j < 8) :
    (spMask (spMul a b)).testBit j =
      xor ((spMask a).testBit j) ((spMask b).testBit ((codeL a).idxOf j)) := by
  obtain ⟨-, ha2, -, -⟩ := okC_spec ha
  rw [spMask_mul, show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    spImg_bit ha2 _ hj]
  simp [hj]

theorem spVec_mul {a b : ℕ} (ha : okC a = true) (hb : okC b = true) (x : List ℤ) :
    spVec a (spVec b x) = spVec (spMul a b) x := by
  obtain ⟨-, ha2, -, -⟩ := okC_spec ha
  apply spExt8 (spVec_length _ _) (spVec_length _ _)
  intro j hj
  rw [spVec_getD a (spVec b x) hj, spVec_getD b x (spIdx_lt ha2 hj), spVec_getD (spMul a b) x hj,
    spMul_idx ha hb hj, spMul_bit ha hj]
  cases (spMask a).testBit j <;> cases (spMask b).testBit ((codeL a).idxOf j) <;> simp

theorem spVec_inj {c : ℕ} (hc : okC c = true) {x y : List ℤ} (hx : x.length = 8) (hy : y.length = 8)
    (h : spVec c x = spVec c y) : x = y := by
  obtain ⟨-, h2, -, -⟩ := okC_spec hc
  apply spExt8 hx hy
  intro k hk
  have e := congrArg (fun z => z.getD (spAt c k) 0) h
  rw [spVec_getD _ _ (spAt_lt c k), spVec_getD _ _ (spAt_lt c k), spIdx_at h2 hk] at e
  by_cases ht : (spMask c).testBit (spAt c k) = true
  · simpa [ht] using e
  · simpa [ht] using e

theorem spId_sum : spId = sumN 8 (fun j => j % 8 * 8 ^ j) := by decide +kernel

theorem spAt_diag (m : ℕ) {k : ℕ} (hk : k < 8) : spAt (m * 2 ^ 24 + spId) k = k := by
  rw [spAt_eq, spId_sum, Nat.add_comm, digit8 (fun j => j % 8) (fun j => Nat.mod_lt _ (by norm_num))
    m hk]
  exact Nat.mod_eq_of_lt hk

theorem spMask_diag {m : ℕ} (hm : m < 256) : spMask (m * 2 ^ 24 + spId) = m := by
  rw [spMask_eq, spId_sum, Nat.add_comm, high8 (fun j => j % 8) (fun j => Nat.mod_lt _ (by norm_num))]
  exact Nat.mod_eq_of_lt hm

theorem codeL_diag (m : ℕ) : codeL (m * 2 ^ 24 + spId) = List.range 8 := by
  unfold codeL
  conv_rhs => rw [← List.map_id (List.range 8)]
  exact List.map_congr_left fun k hk => spAt_diag m (List.mem_range.1 hk)

theorem spRange_idx : ∀ j < 8, (List.range 8).idxOf j = j := by decide

theorem spPermId {x : List ℤ} (hx : x.length = 8) : listPermVec (List.range 8) x = x := by
  apply spExt8 (by simp [listPermVec]) hx
  intro j hj
  rw [spPerm_getD _ _ hj, spRange_idx j hj]

theorem spFlip_zero {x : List ℤ} (hx : x.length = 8) : spFlip 0 x = x := by
  apply spExt8 (spFlip_length _ _) hx
  intro j hj
  rw [spFlip_getD _ _ hj, Nat.zero_testBit]
  rfl

theorem spFlip_255 {x : List ℤ} (hx : x.length = 8) : spFlip 255 x = x.map (-·) := by
  apply spExt8 (spFlip_length _ _) (by simpa using hx)
  intro j hj
  have : (255 : ℕ).testBit j = true := by interval_cases j <;> decide
  rw [spFlip_getD _ _ hj, spNeg_getD, this]
  rfl

section

variable {L : List (List ℤ)} {K : List ℕ} {RK RT ST FT PT : Nat → Nat} {SO NEG FR DP KP : Nat}

theorem spIn (hb : bindRoots RK L = true) {y : List ℤ} (h : L.idxOf y < 240) :
    L.getD (L.idxOf y) [] = y := by
  obtain ⟨hl, -⟩ := bind_facts hb
  rw [getD_eq (by omega)]
  exact List.getElem_idxOf (by omega)

theorem spIn_of (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true) {j : ℕ} (hj : j < 240)
    {y : List ℤ} (h : L.getD j [] = y) : L.idxOf y < 240 := by
  rw [← h, idxOf_root hb hs hj]
  exact hj

theorem spIdx_inj (hb : bindRoots RK L = true) {y z : List ℤ} (hy : L.idxOf y < 240)
    (hz : L.idxOf z < 240) (h : L.idxOf y = L.idxOf z) : y = z :=
  calc y = L.getD (L.idxOf y) [] := (spIn hb hy).symm
    _ = L.getD (L.idxOf z) [] := by rw [h]
    _ = z := spIn hb hz

theorem spLen (hb : bindRoots RK L = true) {j : ℕ} (hj : j < 240) : (L.getD j []).length = 8 := by
  rw [((bind_facts hb).2 j hj).2.2]
  simp [vecOf]

theorem spFlip_in (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hst : ∀ m < 256, signRowOK RK m (ST m) = true) {m : ℕ} (hm : m < 256)
    (he : framePop m % 2 = 0) {i : ℕ} (hi : i < 240) : L.idxOf (spFlip m (L.getD i [])) < 240 := by
  obtain ⟨-, hf⟩ := bind_facts hb
  have hrow := hst m hm
  have hp : Nat.beq (Nat.land (pop8 m) (nat_lit 1)) (nat_lit 0) = true := by
    rw [Nat.beq_eq]
    change pop8 m &&& 1 = 0
    rw [Nat.and_one_is_mod, pop8_eq, he]
  unfold signRowOK at hrow
  rw [hp] at hrow
  change allN 240 _ = true at hrow
  rw [Orb.allN_iff] at hrow
  have h1 := hrow i hi
  simp only [Orb.strictB_eq] at h1
  obtain ⟨he1, he2⟩ := band_true h1
  obtain ⟨-, he3⟩ := band_true he2
  have he240 : pg 8 (mask 8) (ST m) i < 240 := blt_true he1
  obtain ⟨xi, si, vi⟩ := hf i hi
  obtain ⟨-, -, ve⟩ := hf _ he240
  refine spIn_of hb hs he240 ?_
  rw [ve, vi]
  exact (flip_vec xi si (Nat.eq_of_beq_eq_true he3)).symm

theorem spPairs_aux (DP : ℕ) : ∀ (P : List (ℕ × ℕ)) (p : ℕ),
    List.rec (motive := fun _ => Nat → Bool) (fun p => Nat.beq p (nat_lit 28))
      (fun ab _ ih p => bAnd(Nat.blt ab.1 (nat_lit 8), bAnd(Nat.blt ab.2 (nat_lit 8),
        bAnd(Nat.beq ab.1 (pa DP p), bAnd(Nat.beq ab.2 (pb DP p), ih (Nat.succ p)))))) P p = true →
    p + P.length = 28 ∧ ∀ j (hj : j < P.length), P[j] = (pa DP (p + j), pb DP (p + j))
  | [], p, h => by
    have : p = 28 := Nat.eq_of_beq_eq_true h
    simp [this]
  | ab :: P, p, h => by
    obtain ⟨-, h2⟩ := band_true h
    obtain ⟨-, h3⟩ := band_true h2
    obtain ⟨h3, h4⟩ := band_true h3
    obtain ⟨h4, h5⟩ := band_true h4
    obtain ⟨ih1, ih2⟩ := spPairs_aux DP P (Nat.succ p) h5
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    intro j hj
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero]
      exact Prod.ext (Nat.eq_of_beq_eq_true h3) (Nat.eq_of_beq_eq_true h4)
    | succ j =>
      have e : p + (j + 1) = Nat.succ p + j := by omega
      simpa [e] using ih2 j (by simpa using hj)

theorem spPairs (hp : bindPairs DP dPairs = true) {q : ℕ} (hq : q < 28) :
    (pa DP q, pb DP q) = dPairs.getD q (0, 0) := by
  obtain ⟨-, h2⟩ := band_true hp
  obtain ⟨l1, l2⟩ := spPairs_aux DP dPairs 0 h2
  have hq' : q < dPairs.length := by omega
  rw [List.getD_eq_getElem _ _ hq', l2 q hq', Nat.zero_add]

theorem spDP_lt : ∀ q < 28, (dPairs.getD q (0, 0)).1 < (dPairs.getD q (0, 0)).2 ∧
    (dPairs.getD q (0, 0)).2 < 8 := by
  decide +kernel

theorem spDP_all : ∀ a < 8, ∀ b < 8, a < b → ∃ q < 28, dPairs.getD q (0, 0) = (a, b) := by
  decide +kernel

theorem spPab (hp : bindPairs DP dPairs = true) {q : ℕ} (hq : q < 28) :
    pa DP q < pb DP q ∧ pb DP q < 8 := by
  have e := spPairs hp hq
  have h1 : pa DP q = (dPairs.getD q (0, 0)).1 := by rw [← e]
  have h2 : pb DP q = (dPairs.getD q (0, 0)).2 := by rw [← e]
  rw [h1, h2]
  exact spDP_lt q hq

theorem spPermVecL_one {x : List ℤ} (hx : x.length = 8) : permVecL 1 x = x := by
  apply spExt8 (by simp [permVecL]) hx
  intro j hj
  rw [permVecL, spFin_getD _ hj]
  rfl

theorem spPermVecL_mul (σ τ : Equiv.Perm (Fin 8)) (x : List ℤ) :
    permVecL σ (permVecL τ x) = permVecL (σ * τ) x := by
  apply spExt8 (by simp [permVecL]) (by simp [permVecL])
  intro j hj
  simp only [permVecL]
  rw [spFin_getD _ hj, spFin_getD _ hj, spFin_getD _ (σ.symm ⟨j, hj⟩).isLt]
  simp [Equiv.Perm.mul_def]

theorem spSwap_in (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hp : bindPairs DP dPairs = true) (h5 : d5K RK RT PT DP = true) {x y : Fin 8} (hxy : x ≠ y)
    {i : ℕ} (hi : i < 240) : L.idxOf (permVecL (Equiv.swap x y) (L.getD i [])) < 240 := by
  wlog hlt : x < y generalizing x y
  · rw [Equiv.swap_comm]
    exact this hxy.symm (lt_of_le_of_ne (not_lt.1 hlt) hxy.symm)
  obtain ⟨q, hq, hd⟩ := spDP_all x x.isLt y y.isLt hlt
  have e := spPairs hp hq
  rw [hd] at e
  have ha : (x : ℕ) = pa DP q := (congrArg Prod.fst e).symm
  have hb' : (y : ℕ) = pb DP q := (congrArg Prod.snd e).symm
  unfold d5K at h5
  rw [Orb.allN_iff] at h5
  obtain ⟨hw, -⟩ := band_true (h5 q hq)
  obtain ⟨e1, e2⟩ := swap_tab hb hs hw x y ha hb'
  have h := congrArg (fun A : Array ℕ => A[i]!) e1
  simp only [permArrL, getElem!_ofFn_nat _ hi, Orb.unpack_get hi] at h
  unfold permVecL
  rw [h]
  exact e2 i hi

theorem spPerm_in (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hp : bindPairs DP dPairs = true) (h5 : d5K RK RT PT DP = true) (σ : Equiv.Perm (Fin 8)) :
    ∀ i < 240, L.idxOf (permVecL σ (L.getD i [])) < 240 := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    intro i hi
    rw [spPermVecL_one (spLen hb hi)]
    exact spIn_of hb hs hi rfl
  | swap_mul f x y hxy ih =>
    intro i hi
    rw [← spPermVecL_mul]
    have h1 := ih i hi
    rw [← spIn hb h1]
    exact spSwap_in hb hs hp h5 hxy h1

theorem spList_eq {c : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) {e : Equiv.Perm (Fin 8)}
    (he : ∀ j : Fin 8, (e j : ℕ) = spAt c j) (x : List ℤ) :
    listPermVec (codeL c) x = permVecL e x := by
  apply spExt8 (by simp [listPermVec]) (by simp [permVecL])
  intro j hj
  rw [spPerm_getD _ _ hj, permVecL, spFin_getD _ hj, spIdx_e h2 he j hj]

theorem spListPerm_in (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {c : ℕ} (hc : okC c = true)
    {i : ℕ} (hi : i < 240) : L.idxOf (listPermVec (codeL c) (L.getD i [])) < 240 := by
  obtain ⟨-, h2, -, -⟩ := okC_spec hc
  obtain ⟨e, he⟩ := codeL_perm h2
  rw [spList_eq h2 he]
  exact spPerm_in h.bind h.sorted h.pairs h.swaps e i hi

theorem spVec_in (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {c : ℕ} (hc : okC c = true)
    {i : ℕ} (hi : i < 240) : L.idxOf (spVec c (L.getD i [])) < 240 := by
  obtain ⟨-, -, h3, h4⟩ := okC_spec hc
  have h1 := spListPerm_in h hc hi
  unfold spVec
  rw [← spIn h.bind h1]
  exact spFlip_in h.bind h.sorted h.sign h3 h4 h1

theorem spArrC_size (L : List (List ℤ)) (c : ℕ) : (spArrC L c).size = 240 := by
  simp [spArrC, spArrL, compA]

theorem spArrC_get (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {c : ℕ} (hc : okC c = true)
    {i : ℕ} (hi : i < 240) : (spArrC L c)[i]! = L.idxOf (spVec c (L.getD i [])) := by
  obtain ⟨-, -, h3, -⟩ := okC_spec hc
  have hP := spListPerm_in h hc hi
  unfold spArrC spArrL
  rw [compA_get hi, signArrs_get h3]
  unfold listPermArrL
  rw [getElem!_ofFn_nat _ hi]
  dsimp only
  unfold signArrL
  rw [getElem!_ofFn_nat _ hP]
  dsimp only
  rw [spIn h.bind hP]
  rfl

theorem spDiag_get (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {m : ℕ} (hm : m < 256) {i : ℕ}
    (hi : i < 240) : (spArrC L (m * 2 ^ 24 + spId))[i]! = L.idxOf (spFlip m (L.getD i [])) := by
  unfold spArrC spArrL
  rw [spMask_diag hm, codeL_diag, compA_get hi, signArrs_get hm]
  unfold listPermArrL
  rw [getElem!_ofFn_nat _ hi]
  dsimp only
  rw [spPermId (spLen h.bind hi), idxOf_root h.bind h.sorted hi]
  unfold signArrL
  rw [getElem!_ofFn_nat _ hi]
  rfl

noncomputable def keyAB (a b s : Nat) : Nat :=
  Nat.sub (Nat.add (Nat.add (Nat.mul (nat_lit 2) REP)
      (nIf(Nat.blt s (nat_lit 2), Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) a), nat_lit 0)))
      (nIf(bIf(Nat.beq s (nat_lit 0), true, Nat.beq s (nat_lit 2)),
        Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) b), nat_lit 0)))
    (Nat.add (nIf(Nat.blt s (nat_lit 2), nat_lit 0, Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) a)))
      (nIf(bIf(Nat.beq s (nat_lit 0), true, Nat.beq s (nat_lit 2)), nat_lit 0,
        Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) b))))

noncomputable def reflCodeAB (a b s : Nat) : Nat :=
  Nat.add (Nat.add (Nat.sub spId (Nat.add (Nat.shiftLeft a (Nat.mul (nat_lit 3) a))
      (Nat.shiftLeft b (Nat.mul (nat_lit 3) b))))
    (Nat.add (Nat.shiftLeft b (Nat.mul (nat_lit 3) a)) (Nat.shiftLeft a (Nat.mul (nat_lit 3) b))))
    (nIf(bIf(Nat.beq s (nat_lit 0), true, Nat.beq s (nat_lit 3)),
      Nat.shiftLeft (Nat.add (Nat.shiftLeft (nat_lit 1) a) (Nat.shiftLeft (nat_lit 1) b)) (nat_lit 24),
      nat_lit 0))

def rvAB (a b s : ℕ) : Fin 8 → ℤ := fun k =>
  if (k : ℕ) = a then (if s < 2 then 2 else -2) else if (k : ℕ) = b then
    (if s = 0 ∨ s = 2 then 2 else -2) else 0

def swapF (a b k : ℕ) : ℕ := if k = a then b else if k = b then a else k

theorem keyAB_vec : ∀ a < 8, ∀ b < 8, ∀ s < 4, a < b →
    vecOf (keyAB a b s) = List.ofFn (rvAB a b s) := by
  decide +kernel

theorem reflCodeAB_ok : ∀ a < 8, ∀ b < 8, ∀ s < 4, a < b → okC (reflCodeAB a b s) = true := by
  decide +kernel

theorem reflCodeAB_bit : ∀ a < 8, ∀ b < 8, ∀ s < 4, a < b →
    ∀ j < 8, (spMask (reflCodeAB a b s)).testBit j = ((s == 0 || s == 3) && (j == a || j == b)) := by
  decide +kernel

theorem reflCodeAB_idx : ∀ a < 8, ∀ b < 8, ∀ s < 4, a < b →
    ∀ j < 8, (codeL (reflCodeAB a b s)).idxOf j = swapF a b j := by
  decide +kernel

theorem spDP_sum : ∀ k < 8, ∃ p < 28, ∃ s < 4, ∃ s' < 4, ∀ j : Fin 8,
    rvAB (dPairs.getD p (0, 0)).1 (dPairs.getD p (0, 0)).2 s j +
      rvAB (dPairs.getD p (0, 0)).1 (dPairs.getD p (0, 0)).2 s' j = if (j : ℕ) = k then 4 else 0 := by
  decide +kernel

theorem spShr2 (r : ℕ) : Nat.shiftRight r (nat_lit 2) = r / 4 := by
  change r >>> 2 = r / 2 ^ 2
  exact Nat.shiftRight_eq_div_pow r 2

theorem spLand3 (r : ℕ) : Nat.land r (nat_lit 3) = r % 4 := by
  change r &&& (2 ^ 2 - 1) = r % 2 ^ 2
  exact Nat.and_two_pow_sub_one_eq_mod r 2

theorem rootDKey_eq (DP r : ℕ) : rootDKey DP r = keyAB (pa DP (r / 4)) (pb DP (r / 4)) (r % 4) := by
  unfold rootDKey
  simp only [Orb.strictN_eq]
  rw [spShr2, spLand3]
  rfl

theorem reflCodeK_eq (DP r : ℕ) :
    reflCodeK DP r = reflCodeAB (pa DP (r / 4)) (pb DP (r / 4)) (r % 4) := by
  unfold reflCodeK
  simp only [Orb.strictN_eq]
  rw [spShr2, spLand3]
  rfl

theorem spRoot (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {r : ℕ} (hr : r < 112) :
    L.getD r [] = List.ofFn (rvAB (pa DP (r / 4)) (pb DP (r / 4)) (r % 4)) ∧
      pa DP (r / 4) < pb DP (r / 4) ∧ pb DP (r / 4) < 8 := by
  obtain ⟨-, hf⟩ := bind_facts h.bind
  have hd := h.rootsD
  unfold rootsDK at hd
  rw [Orb.allN_iff] at hd
  have e : RK r = rootDKey DP r := Nat.eq_of_beq_eq_true (hd r hr)
  obtain ⟨h1, h2⟩ := spPab h.pairs (q := r / 4) (by omega)
  refine ⟨?_, h1, h2⟩
  rw [(hf r (by omega)).2.2, e, rootDKey_eq, keyAB_vec _ (by omega) _ h2 _ (Nat.mod_lt _ (by norm_num)) h1]

theorem spCode_eq (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {a b : ℕ} (ha : okC a = true)
    (hb : okC b = true) (hv : ∀ i < 240, spVec a (L.getD i []) = spVec b (L.getD i [])) : a = b := by
  obtain ⟨ha1, ha2, ha3, -⟩ := okC_spec ha
  obtain ⟨hb1, hb2, hb3, -⟩ := okC_spec hb
  have key : ∀ k < 8, spAt a k = spAt b k ∧
      (spMask a).testBit (spAt a k) = (spMask b).testBit (spAt a k) := by
    intro k hk
    obtain ⟨p, hp, s, hs, s', hs', hsum⟩ := spDP_sum k hk
    have e := spPairs h.pairs hp
    rw [← e] at hsum
    obtain ⟨u1, -, -⟩ := spRoot h (r := 4 * p + s) (by omega)
    obtain ⟨u2, -, -⟩ := spRoot h (r := 4 * p + s') (by omega)
    have d1 : (4 * p + s) / 4 = p := by omega
    have d2 : (4 * p + s') / 4 = p := by omega
    have m1 : (4 * p + s) % 4 = s := by omega
    have m2 : (4 * p + s') % 4 = s' := by omega
    rw [d1, m1] at u1
    rw [d2, m2] at u2
    have j8 := spAt_lt a k
    have E1 := congrArg (fun z => z.getD (spAt a k) 0) (hv (4 * p + s) (by omega))
    have E2 := congrArg (fun z => z.getD (spAt a k) 0) (hv (4 * p + s') (by omega))
    rw [spVec_getD _ _ j8, spVec_getD _ _ j8, spIdx_at ha2 hk, u1] at E1
    rw [spVec_getD _ _ j8, spVec_getD _ _ j8, spIdx_at ha2 hk, u2] at E2
    have ib := spIdx_lt hb2 j8
    rw [spOfFn_getD _ hk, spOfFn_getD _ ib] at E1 E2
    have sk := hsum ⟨k, hk⟩
    have sb := hsum ⟨_, ib⟩
    simp only at sk sb
    by_cases hik : (codeL b).idxOf (spAt a k) = k
    · simp only [↓reduceIte] at sk
      rw [ite_eq_left hik] at sb
      refine ⟨?_, ?_⟩
      · have := spAt_idx hb2 j8
        rw [hik] at this
        exact this.symm
      · revert E1 E2
        cases (spMask a).testBit (spAt a k) <;> cases (spMask b).testBit (spAt a k) <;>
          simp <;> intro E1 E2 <;> omega
    · exfalso
      simp only [↓reduceIte] at sk
      rw [ite_eq_right hik] at sb
      revert E1 E2
      cases (spMask a).testBit (spAt a k) <;> cases (spMask b).testBit (spAt a k) <;>
        simp <;> intro E1 E2 <;> omega
  have hl : codeL a = codeL b := by
    unfold codeL
    exact List.map_congr_left fun k hk => (key k (List.mem_range.1 hk)).1
  have hm : spMask a = spMask b := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 8
    · have e := (key _ (spIdx_lt ha2 hj)).2
      rwa [spAt_idx ha2 hj] at e
    · have h256 : 256 ≤ 2 ^ j := by
        calc 256 = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]
  exact eq_of_spMask_codeL ha1 hb1 hm hl

theorem swapF_lt {a b k : ℕ} (ha : a < 8) (hb : b < 8) (hk : k < 8) : swapF a b k < 8 := by
  unfold swapF
  split_ifs <;> omega

theorem spReflAB {a b s : ℕ} (hab : a < b) (hb : b < 8) (hs : s < 4) (x : Fin 8 → ℤ)
    (hd : ∃ c : ℤ, ∑ j, x j * rvAB a b s j = 4 * c) :
    reflVec (List.ofFn (rvAB a b s)) (List.ofFn x) = spVec (reflCodeAB a b s) (List.ofFn x) := by
  obtain ⟨c, hc⟩ := hd
  have ha8 : a < 8 := by omega
  have hne : (⟨a, ha8⟩ : Fin 8) ≠ ⟨b, hb⟩ := fun e => by
    have := congrArg Fin.val e
    simp at this
    omega
  have hsum : ∑ j, x j * rvAB a b s j =
      x ⟨a, ha8⟩ * rvAB a b s ⟨a, ha8⟩ + x ⟨b, hb⟩ * rvAB a b s ⟨b, hb⟩ := by
    refine Finset.sum_eq_add _ _ hne (fun k _ hk => ?_) (by simp) (by simp)
    have h1 : (k : ℕ) ≠ a := fun e => hk.1 (Fin.ext e)
    have h2 : (k : ℕ) ≠ b := fun e => hk.2 (Fin.ext e)
    simp [rvAB, h1, h2]
  have hba : b ≠ a := by omega
  have ra : rvAB a b s ⟨a, ha8⟩ = if s < 2 then 2 else -2 := by simp [rvAB]
  have rb : rvAB a b s ⟨b, hb⟩ = if s = 0 ∨ s = 2 then 2 else -2 := by simp [rvAB, hba]
  rw [hsum, ra, rb] at hc
  rw [reflVec_ofFn, Finset.sum_congr rfl (fun j _ => rfl), hsum, ra, rb, hc,
    Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]
  apply spExt8 (by simp) (spVec_length _ _)
  intro j hj
  rw [spOfFn_getD _ hj, spVec_getD _ _ hj, reflCodeAB_bit a ha8 b hb s hs hab j hj,
    reflCodeAB_idx a ha8 b hb s hs hab j hj, spOfFn_getD _ (swapF_lt ha8 hb hj)]
  by_cases hja : j = a
  · subst hja
    have e1 : swapF j b j = b := by simp [swapF]
    simp only [e1, rvAB, beq_self_eq_true, Bool.true_or, Bool.and_true]
    interval_cases s <;> simp at hc ⊢ <;> omega
  · by_cases hjb : j = b
    · subst hjb
      have e1 : swapF a j j = a := by simp [swapF, hja]
      simp only [e1, rvAB, hja, ite_false, beq_self_eq_true, Bool.or_true, Bool.and_true]
      interval_cases s <;> simp at hc ⊢ <;> omega
    · have e1 : swapF a b j = j := by simp [swapF, hja, hjb]
      have hja' : (j == a) = false := by simpa using hja
      have hjb' : (j == b) = false := by simpa using hjb
      simp [e1, rvAB, hja, hjb, hja', hjb']

theorem spRefl_dvd {x r e : ℕ} (he : e < 4294967296) (hk : e = reflKey x r) :
    ∃ c : ℤ, dotZ (vecOf x) (vecOf r) = 4 * c := by
  have hdot := dot_eq x r
  have he2 := he
  unfold reflKey at hk
  beta_reduce at hk
  generalize hP : Nat.add (sumN (nat_lit 8) fun k => Nat.mul (cf x k) (cf r k)) (nat_lit 32) = P
    at hk
  generalize hN : Nat.mul (nat_lit 2) (Nat.add (sumN (nat_lit 8) fun k => cf x k)
    (sumN (nat_lit 8) fun k => cf r k)) = N at hk
  have hd : dotZ (vecOf x) (vecOf r) = (P : ℤ) - N := by
    rw [← hP, ← hN]
    exact hdot
  rw [hd]
  cases h1 : Nat.beq P N
  · simp only [h1] at hk
    cases h2 : Nat.beq P (Nat.add N (nat_lit 4))
    · simp only [h2] at hk
      cases h3 : Nat.beq N (Nat.add P (nat_lit 4))
      · simp only [h3] at hk
        cases h4 : Nat.beq P (Nat.add N (nat_lit 8))
        · simp only [h4] at hk
          cases h5 : Nat.beq N (Nat.add P (nat_lit 8))
          · simp only [h5] at hk
            rw [hk] at he2
            exact absurd he2 (lt_irrefl _)
          · have h5' : N = P + 8 := Nat.eq_of_beq_eq_true h5
            exact ⟨-2, by omega⟩
        · have h4' : P = N + 8 := Nat.eq_of_beq_eq_true h4
          exact ⟨2, by omega⟩
      · have h3' : N = P + 4 := Nat.eq_of_beq_eq_true h3
        exact ⟨-1, by omega⟩
    · have h2' : P = N + 4 := Nat.eq_of_beq_eq_true h2
      exact ⟨1, by omega⟩
  · have h1' : P = N := Nat.eq_of_beq_eq_true h1
    exact ⟨0, by omega⟩

noncomputable def spCv (RK : ℕ → ℕ) (i : ℕ) : Fin 8 → ℤ := fun k => (cf (RK i) k : ℤ) - 2

theorem spV (hb : bindRoots RK L = true) {i : ℕ} (hi : i < 240) :
    L.getD i [] = List.ofFn (spCv RK i) :=
  ((bind_facts hb).2 i hi).2.2

theorem spDvd (hb : bindRoots RK L = true) (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) {i j : ℕ}
    (hi : i < 240) (hj : j < 240) : ∃ c : ℤ, ∑ k, spCv RK i k * spCv RK j k = 4 * c := by
  obtain ⟨-, hf⟩ := bind_facts hb
  have h := hr j hj
  unfold reflRowOK at h
  rw [Orb.strictB_eq, Orb.allN_iff] at h
  have h1 := h i hi
  rw [Orb.strictB_eq] at h1
  obtain ⟨e1, e2⟩ := band_true h1
  obtain ⟨c, hc⟩ := spRefl_dvd (x := RK i) (r := RK j)
    (e := RK (pg (nat_lit 8) (nat_lit 255) (RT j) i)) (hf _ (blt_true e1)).1
    (Nat.eq_of_beq_eq_true e2)
  refine ⟨c, ?_⟩
  rw [← hc, vecOf, vecOf, dotZ_ofFn]
  rfl

theorem spReflL (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {r a b s : ℕ} (hr : r < 240)
    (hab : a < b) (hb : b < 8) (hs : s < 4) (hv : L.getD r [] = List.ofFn (rvAB a b s)) {i : ℕ}
    (hi : i < 240) : reflVec (L.getD r []) (L.getD i []) = spVec (reflCodeAB a b s) (L.getD i []) := by
  obtain ⟨c, hc⟩ := spDvd h.bind h.refl hi hr
  have hrv : spCv RK r = rvAB a b s := List.ofFn_inj.mp ((spV h.bind hr).symm.trans hv)
  rw [hrv] at hc
  rw [hv, spV h.bind hi]
  exact spReflAB hab hb hs _ ⟨c, hc⟩

theorem spReflK (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {r : ℕ} (hr : r < 112) :
    okC (reflCodeK DP r) = true ∧ ∀ i < 240,
      reflVec (L.getD r []) (L.getD i []) = spVec (reflCodeK DP r) (L.getD i []) := by
  obtain ⟨hv, h1, h2⟩ := spRoot h hr
  rw [reflCodeK_eq]
  exact ⟨reflCodeAB_ok _ (by omega) _ h2 _ (Nat.mod_lt _ (by norm_num)) h1,
    fun i hi => spReflL h (by omega) h1 h2 (Nat.mod_lt _ (by norm_num)) hv hi⟩

noncomputable def spStep (C : ℕ → ℕ) (v k A : ℕ) : ℕ :=
  nIf(Nat.beq (Nat.land (Nat.shiftRight v k) (nat_lit 1)) (nat_lit 1), spMul (C k) A, A)

noncomputable def spRec (C : ℕ → ℕ) (v n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) spId (fun k ih => strictN ih fun A => spStep C v k A) n

theorem spRec_succ (C : ℕ → ℕ) (v n : ℕ) : spRec C v (n + 1) = spStep C v n (spRec C v n) := by
  change strictN (spRec C v n) (fun A => spStep C v n A) = _
  rw [Orb.strictN_eq]

theorem spId_ok : okC spId = true := by decide +kernel

theorem spVec_one {x : List ℤ} (hx : x.length = 8) : spVec spId x = x := by
  have e : spId = 0 * 2 ^ 24 + spId := by norm_num
  unfold spVec
  rw [e, spMask_diag (by norm_num), codeL_diag, spPermId hx, spFlip_zero hx]

theorem spFold (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) (C : ℕ → ℕ)
    (hC : ∀ k : Fin 8, okC (C k) = true ∧ ∀ j < 240,
      reflVec (L.getD (frameRootL L k) []) (L.getD j []) = spVec (C k) (L.getD j []))
    (w : ℕ) {i : ℕ} (hi : i < 240) :
    (List.finRange 8).foldl (fun x k => if frameDecode w k = 1 then
      reflVec (L.getD (frameRootL L k) []) x else x) (L.getD i []) = spVec (spRec C w 8) (L.getD i []) ∧
    okC (spRec C w 8) = true := by
  have key : ∀ n ≤ 8, ((List.finRange 8).take n).foldl (fun x k => if frameDecode w k = 1 then
      reflVec (L.getD (frameRootL L k) []) x else x) (L.getD i []) = spVec (spRec C w n) (L.getD i []) ∧
      okC (spRec C w n) = true := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨(spVec_one (spLen h.bind hi)).symm, spId_ok⟩
    | succ n ih =>
      intro hn
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have ht : (List.finRange 8).take (n + 1) = (List.finRange 8).take n ++ [⟨n, by omega⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
        simp
      rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil, ih1, spRec_succ]
      have hin := spVec_in h ih2 hi
      unfold spStep
      rw [Orb.nIf_eq]
      simp only [spDecode_one]
      by_cases hbit : w.testBit n = true
      · have hb' : Nat.beq (Nat.land (Nat.shiftRight w n) 1) 1 = true := by
          rw [Nat.beq_eq]
          exact (bit_testBit w n).2 hbit
        rw [ite_eq_left hbit, ite_eq_left hb',← spIn h.bind hin, (hC ⟨n, by omega⟩).2 _ hin, spIn h.bind hin,
          spVec_mul (hC ⟨n, by omega⟩).1 ih2]
        exact ⟨rfl, okC_mul (hC ⟨n, by omega⟩).1 ih2⟩
      · have hb' : ¬ Nat.beq (Nat.land (Nat.shiftRight w n) 1) 1 = true := by
          rw [Nat.beq_eq]
          exact fun e => hbit ((bit_testBit w n).1 e)
        rw [ite_eq_right hbit, ite_eq_right hb']
        exact ⟨rfl, ih2⟩
  have := key 8 le_rfl
  rwa [List.take_of_length_le (by simp)] at this

theorem spFrameKey_vec : ∀ k : Fin 8, vecOf (frameKey k) =
    vecD (2 * (k / 2)) (2 * (k / 2) + 1) 2 (if (k : ℕ) % 2 = 0 then -2 else 2) := by
  decide +kernel

theorem spFrameRoot (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) (k : Fin 8) :
    pg 8 (mask 8) FR k < 240 ∧ L.getD (pg 8 (mask 8) FR k) [] = vecOf (frameKey k) ∧
      frameRootL L k = pg 8 (mask 8) FR k := by
  obtain ⟨-, hf⟩ := bind_facts h.bind
  have hfr := h.froots
  unfold frameRootsOK at hfr
  rw [Orb.allN_iff] at hfr
  have h1 := hfr k k.isLt
  rw [Orb.strictB_eq] at h1
  obtain ⟨e1, e2⟩ := band_true h1
  have he : pg 8 (mask 8) FR k < 240 := blt_true e1
  have hv : L.getD (pg 8 (mask 8) FR k) [] = vecOf (frameKey k) := by
    rw [(hf _ he).2.2]
    exact congrArg vecOf (Nat.eq_of_beq_eq_true e2)
  refine ⟨he, hv, ?_⟩
  unfold frameRootL
  rw [← spFrameKey_vec k, ← hv, idxOf_root h.bind h.sorted he]

noncomputable def FCk (k : ℕ) : ℕ :=
  reflCodeAB (2 * (k / 2)) (2 * (k / 2) + 1) (if k % 2 = 0 then 1 else 0)

noncomputable def fcK (v : ℕ) : ℕ := spRec FCk v 8

theorem spFrameKey_eq : ∀ k < 8,
    frameKey k = keyAB (2 * (k / 2)) (2 * (k / 2) + 1) (if k % 2 = 0 then 1 else 0) := by
  decide +kernel

theorem spFC (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) (k : Fin 8) :
    okC (FCk k) = true ∧ ∀ j < 240,
      reflVec (L.getD (frameRootL L k) []) (L.getD j []) = spVec (FCk k) (L.getD j []) := by
  obtain ⟨he, hv, hr⟩ := spFrameRoot h k
  have := k.isLt
  have hab : 2 * ((k : ℕ) / 2) < 2 * ((k : ℕ) / 2) + 1 := by omega
  have hb : 2 * ((k : ℕ) / 2) + 1 < 8 := by omega
  have hs : (if (k : ℕ) % 2 = 0 then 1 else 0) < 4 := by split_ifs <;> norm_num
  rw [spFrameKey_eq k k.isLt, keyAB_vec _ (by omega) _ hb _ hs hab] at hv
  rw [hr]
  exact ⟨reflCodeAB_ok _ (by omega) _ hb _ hs hab, fun j hj => spReflL h he hab hb hs hv hj⟩

theorem spFrame_get (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {w : ℕ} (hw : w < 256) {i : ℕ}
    (hi : i < 240) : ((frameArrsL L)[w]!)[i]! = L.idxOf (spVec (fcK w) (L.getD i [])) ∧
      okC (fcK w) = true := by
  rw [frameArrs_get hw]
  unfold frameArrL
  rw [getElem!_ofFn_nat _ hi]
  dsimp only
  obtain ⟨e1, e2⟩ := spFold h FCk (spFC h) w hi
  rw [e1]
  exact ⟨rfl, e2⟩

def spPd (t : Fin 4 → Bool) (k : Fin 8) : ℕ :=
  if t ⟨k / 2, by omega⟩ then (if (k : ℕ) % 2 = 0 then k + 1 else k - 1) else k

def codeTU (t u : Fin 4 → Bool) : ℕ :=
  (∑ k : Fin 8, spPd t k * 8 ^ (k : ℕ)) + bitsum (fun k => u ⟨k / 2, by omega⟩) * 2 ^ 24

def vtu (t u : Fin 4 → Bool) : ℕ :=
  bitsum fun k => if (k : ℕ) % 2 = 0 then xor (t ⟨k / 2, by omega⟩) (u ⟨k / 2, by omega⟩)
    else u ⟨k / 2, by omega⟩

theorem fcK_tu : ∀ t u : Fin 4 → Bool, fcK (vtu t u) = codeTU t u := by
  decide +kernel

theorem fcK_ok : ∀ v < 256, okC (fcK v) = true ∧ frameK' (fcK v) = true := by
  decide +kernel

theorem fcK_pow : ∀ i < 8, fcK (2 ^ i) = FCk i := by
  decide +kernel

theorem tu_vec : ∀ t u : Fin 4 → Bool, ∀ i : Fin 8, spVec (codeTU t u) (vecOf (frameKey i)) =
    if (vtu t u).testBit i then (vecOf (frameKey i)).map (-·) else vecOf (frameKey i) := by
  decide +kernel

theorem frame_neg : ∀ i : Fin 8, (vecOf (frameKey i)).map (-·) ≠ vecOf (frameKey i) := by
  decide +kernel

theorem frame_self : ∀ i : Fin 8,
    reflVec (vecOf (frameKey i)) (vecOf (frameKey i)) = (vecOf (frameKey i)).map (-·) := by
  decide +kernel

theorem frame_sq : ∀ i : Fin 8, ∑ k, spCv (fun _ => frameKey i) 0 k * spCv (fun _ => frameKey i) 0 k = 8 ∧
    spCv (fun _ => frameKey i) 0 ⟨2 * (i / 2), by omega⟩ = 2 := by
  decide +kernel

theorem spBits8 : ∀ v < 256, sumN 8 (fun i => if v.testBit i = true then 2 ^ i else 0) = v := by
  decide +kernel

theorem vtu_lt (t u : Fin 4 → Bool) : vtu t u < 256 := (bitsum_spec _).1

theorem sumN_congr'' {f g : ℕ → ℕ} : ∀ {n : ℕ}, (∀ i < n, f i = g i) → sumN n f = sumN n g
  | 0, _ => rfl
  | n + 1, h => by
    change f n + sumN n f = g n + sumN n g
    rw [h n (by omega), sumN_congr'' (fun i hi => h i (by omega))]

theorem foldl_pow_acc' (l : List ℕ) : ∀ acc, l.foldl (fun m i => m + 2 ^ i) acc =
    acc + l.foldl (fun m i => m + 2 ^ i) 0 := by
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (acc + 2 ^ a), ih (0 + 2 ^ a)]
    omega

theorem foldl_filter_pow' (c : ℕ → Bool) : ∀ n,
    ((List.range n).filter c).foldl (fun m i => m + 2 ^ i) 0 =
      sumN n (fun i => if c i = true then 2 ^ i else 0)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.foldl_append, foldl_pow_acc', foldl_filter_pow' c n]
    have hs : sumN (n + 1) (fun i => if c i = true then 2 ^ i else 0) =
        (if c n = true then 2 ^ n else 0) + sumN n (fun i => if c i = true then 2 ^ i else 0) := rfl
    rw [hs]
    cases h : c n
    · simp [h]
    · simp [h]
      omega

theorem sumN_pow_lt' (c : ℕ → Bool) : ∀ n, sumN n (fun i => if c i = true then 2 ^ i else 0) < 2 ^ n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    change (if c n = true then 2 ^ n else 0) + sumN n _ < 2 ^ (n + 1)
    have := sumN_pow_lt' c n
    rw [pow_succ]
    split_ifs <;> omega

theorem invCand_foldl' (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem invCand_get' {n : ℕ} {t : Array ℕ} (hlt : ∀ i < n, t[i]! < n)
    (hinj : ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j) : ∀ i < n, (invCand n t)[t[i]!]! = i := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt' | rfl
      · have hne : t[i]! ≠ t[k]! := fun e => by
          have := hinj i (by omega) k (by omega) e
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt'
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hlt i (by omega))]
  intro i hi
  rw [invCand_foldl']
  exact (key n le_rfl).2 i hi

theorem spKey_vec (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {i : ℕ} (hi : i < 8) :
    L.getD (pg 8 (mask 8) KP i) [] = vecOf (frameKey i) ∨
      L.getD (pg 8 (mask 8) KP i) [] = (vecOf (frameKey i)).map (-·) := by
  obtain ⟨-, hq⟩ := bindList_get h.keys hi
  set q := pg 8 (mask 8) KP i with hqdef
  obtain ⟨hFT, -, -⟩ := frame_tabs h.bind h.sorted h.froots h.frame0 h.frame h.homF
  have hl := h.links
  unfold linksOK at hl
  obtain ⟨hl1, -⟩ := band_true hl
  rw [Orb.allN_iff] at hl1
  have eF : FT (Nat.shiftLeft 1 i) = RT q := Nat.eq_of_beq_eq_true (hl1 i hi)
  have e2 : Nat.shiftLeft 1 i = 2 ^ i := by
    change 1 <<< i = 2 ^ i
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [e2] at eF
  have h2i : 2 ^ i < 256 := by
    calc 2 ^ i < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hi
      _ = 256 := by norm_num
  have hA : (frameArrsL L)[2 ^ i]! = reflArrL L q := by
    rw [hFT _ h2i, eF, refl_sound h.bind h.sorted h.refl q hq]
  obtain ⟨hfe, hfv, -⟩ := spFrameRoot h ⟨i, hi⟩
  set f := pg 8 (mask 8) FR i
  have hR : ((frameArrsL L)[2 ^ i]!)[f]! = (reflArrL L q)[f]! := by rw [hA]
  obtain ⟨g1, -⟩ := spFrame_get h h2i hfe
  rw [g1, fcK_pow i hi, ← (spFC h ⟨i, hi⟩).2 f hfe, (spFrameRoot h ⟨i, hi⟩).2.2, hfv,
    frame_self ⟨i, hi⟩] at hR
  have hRq : (reflArrL L q)[f]! = pg 8 (mask 8) (RT q) f := by
    rw [refl_sound h.bind h.sorted h.refl q hq, Orb.unpack_get hfe]
  have hRL : (reflArrL L q)[f]! = L.idxOf (reflVec (L.getD q []) (vecOf (frameKey i))) := by
    unfold reflArrL
    rw [getElem!_ofFn_nat _ hfe, hfv]
  have hlt1 : L.idxOf (reflVec (L.getD q []) (vecOf (frameKey i))) < 240 := by
    rw [← hRL, hRq]
    exact rt_lt8 h.refl hq hfe
  have hlt2 : L.idxOf ((vecOf (frameKey i)).map (-·)) < 240 := by
    rw [hR, hRq]
    exact rt_lt8 h.refl hq hfe
  rw [hRL] at hR
  have hE := spIdx_inj h.bind hlt1 hlt2 hR.symm
  obtain ⟨c, hc⟩ := spDvd h.bind h.refl hq hq
  obtain ⟨-, hf⟩ := bind_facts h.bind
  have sq := (hf q hq).2.1
  set r := spCv RK q
  set φ := spCv (fun _ => frameKey i) 0
  have hφ : vecOf (frameKey i) = List.ofFn φ := rfl
  rw [spV h.bind hq, hφ, reflVec_ofFn, List.map_ofFn] at hE
  have hk := fun k => congrFun (List.ofFn_inj.mp hE) k
  set T := (∑ j, φ j * r j) / 4
  have hT : ∀ k, T * r k = 2 * φ k := fun k => by
    have := hk k
    simp only [Function.comp_apply] at this
    linarith
  obtain ⟨s8, sa⟩ := frame_sq ⟨i, hi⟩
  have hra : -2 ≤ r ⟨2 * (i / 2), by omega⟩ ∧ r ⟨2 * (i / 2), by omega⟩ ≤ 2 := by
    have := sq (2 * (i / 2)) (by omega)
    simp only [r, spCv]
    omega
  have hTa := hT ⟨2 * (i / 2), by omega⟩
  change spCv (fun _ => frameKey i) 0 ⟨2 * (i / 2), by omega⟩ = 2 at sa
  rw [show φ ⟨2 * (i / 2), by omega⟩ = 2 from sa] at hTa
  have hT2 : T ^ 2 * (4 * c) = 32 := by
    have e1 : ∑ k, (T * r k) * (T * r k) = ∑ k, (2 * φ k) * (2 * φ k) := by
      simp only [hT]
    have e2 : ∑ k, (T * r k) * (T * r k) = T ^ 2 * ∑ k, r k * r k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e3 : ∑ k, (2 * φ k) * (2 * φ k) = 4 * ∑ k, φ k * φ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [← hc, ← e2, e1, e3, s8]
    norm_num
  have hT' : T = 2 ∨ T = -2 := by
    obtain ⟨l1, l2⟩ := hra
    generalize r ⟨2 * (i / 2), by omega⟩ = ra at l1 l2 hTa
    have : ra = -2 ∨ ra = -1 ∨ ra = 0 ∨ ra = 1 ∨ ra = 2 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · right; linarith
    · exfalso
      have : T = -4 := by linarith
      rw [this] at hT2
      omega
    · norm_num at hTa
    · exfalso
      have : T = 4 := by linarith
      rw [this] at hT2
      omega
    · left; linarith
  rw [spV h.bind hq, hφ]
  rcases hT' with hT2' | hT2'
  · left
    refine List.ofFn_inj.mpr (funext fun k => ?_)
    have := hT k
    rw [hT2'] at this
    linarith
  · right
    rw [List.map_ofFn]
    refine List.ofFn_inj.mpr (funext fun k => ?_)
    have := hT k
    rw [hT2'] at this
    simp only [Function.comp_apply]
    linarith

theorem spFrameK' {c : ℕ} (hc : okC c = true) (hf : frameK' c = true) :
    ∃ t u : Fin 4 → Bool, c = codeTU t u := by
  obtain ⟨hc1, -, hc3, -⟩ := okC_spec hc
  unfold frameK' at hf
  rw [Orb.allN_iff] at hf
  have q : ∀ k, (spMask c).testBit k = decide (Nat.land (Nat.shiftRight (spMask c) k) 1 = 1) :=
    fun k => by rw [Bool.eq_iff_iff, decide_eq_true_iff, bit_testBit]
  have P : ∀ j < 4, ((spAt c (2 * j) = 2 * j ∧ spAt c (2 * j + 1) = 2 * j + 1) ∨
      (spAt c (2 * j) = 2 * j + 1 ∧ spAt c (2 * j + 1) = 2 * j)) ∧
      (spMask c).testBit (2 * j) = (spMask c).testBit (2 * j + 1) := by
    intro j hj
    have h1 := hf j hj
    rw [Orb.strictB_eq] at h1
    obtain ⟨h2, h3⟩ := band_true h1
    rw [Orb.bIf_eq] at h2
    refine ⟨?_, ?_⟩
    · split_ifs at h2 with hh
      · left
        exact ⟨Nat.eq_of_beq_eq_true hh, Nat.eq_of_beq_eq_true h2⟩
      · right
        obtain ⟨h4, h5⟩ := band_true h2
        exact ⟨Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩
    · have e3 := Nat.eq_of_beq_eq_true h3
      change Nat.land (Nat.shiftRight (spMask c) (2 * j)) 1 =
        Nat.land (Nat.shiftRight (spMask c) (2 * j + 1)) 1 at e3
      rw [q, q, e3]
  obtain ⟨tt, htt⟩ : ∃ tt : Fin 4 → Bool, ∀ j : Fin 4, tt j = !(spAt c (2 * j) == 2 * j) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨uu, huu⟩ : ∃ uu : Fin 4 → Bool, ∀ j : Fin 4, uu j = (spMask c).testBit (2 * j) :=
    ⟨_, fun _ => rfl⟩
  refine ⟨tt, uu, ?_⟩
  have hd : ∀ k : Fin 8, spAt c k = spPd tt k := by
    intro k
    obtain ⟨P1, -⟩ := P (k / 2) (by omega)
    fin_cases k <;> simp [spPd, htt] at P1 ⊢ <;> rcases P1 with ⟨q0, q1⟩ | ⟨q0, q1⟩ <;> simp [q0, q1]
  have hm : spMask c = bitsum (fun k => uu ⟨k / 2, by omega⟩) := by
    conv_lhs => rw [← spBitsum_self _ hc3]
    congr 1
    funext k
    obtain ⟨-, P2⟩ := P (k / 2) (by omega)
    fin_cases k <;> simp [huu] at P2 ⊢ <;> simp [P2]
  rw [code_expand hc1, codeTU, sumN_eq, Finset.sum_range (fun k => spAt c k * 8 ^ k), hm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hd k]

end

end CFSG.KLC.E8

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {L : List (List ℤ)} {K : List ℕ} {RK RT ST FT PT : Nat → Nat} {SO NEG FR DP KP : Nat}

theorem spC_mul (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {a b : ℕ} (ha : okC a = true)
    (hb : okC b = true) : compA 240 (spArrC L a) (spArrC L b) = spArrC L (spMul a b) := by
  apply arr_ext8 (n := 240) (by simp [compA]) (spArrC_size _ _)
  intro i hi
  have hbi := spVec_in h hb hi
  rw [compA_get hi, spArrC_get h hb hi, spArrC_get h ha hbi, spIn h.bind hbi, spVec_mul ha hb,
    spArrC_get h (okC_mul ha hb) hi]

theorem spC_valid (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {c : ℕ} (hc : okC c = true) :
    isInvA 240 (spArrC L c) (invCand 240 (spArrC L c)) = true := by
  have hlt : ∀ i < 240, (spArrC L c)[i]! < 240 := fun i hi => by
    rw [spArrC_get h hc hi]
    exact spVec_in h hc hi
  have hinj : ∀ i < 240, ∀ j < 240, (spArrC L c)[i]! = (spArrC L c)[j]! → i = j := by
    intro i hi j hj e
    rw [spArrC_get h hc hi, spArrC_get h hc hj] at e
    have e3 := spVec_inj hc (spLen h.bind hi) (spLen h.bind hj)
      (spIdx_inj h.bind (spVec_in h hc hi) (spVec_in h hc hj) e)
    calc i = L.idxOf (L.getD i []) := (idxOf_root h.bind h.sorted hi).symm
      _ = L.idxOf (L.getD j []) := by rw [e3]
      _ = j := idxOf_root h.bind h.sorted hj
  unfold isInvA
  rw [allLt_iff]
  intro i hi
  rw [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq]
  exact ⟨hlt i hi, invCand_get' hlt hinj i hi⟩

theorem spC_inj (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {a b : ℕ} (ha : okC a = true)
    (hb : okC b = true) (hq : eqA 240 (spArrC L a) (spArrC L b) = true) : a = b := by
  refine spCode_eq h ha hb fun i hi => ?_
  have e := eqA_spec hq i hi
  rw [spArrC_get h ha hi, spArrC_get h hb hi] at e
  exact spIdx_inj h.bind (spVec_in h ha hi) (spVec_in h hb hi) e

theorem spC_one (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) :
    eqA 240 (spArrC L spId) (idA 240) = true := by
  have e : spId = 0 * 2 ^ 24 + spId := by norm_num
  apply eqA_of
  intro i hi
  rw [e, spDiag_get h (by norm_num) hi, idA_get hi, spFlip_zero (spLen h.bind hi),
    idxOf_root h.bind h.sorted hi]

theorem spC_neg (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) :
    eqA 240 (spArrC L negC) (negArrL L) = true := by
  have e : negC = 255 * 2 ^ 24 + spId := by decide +kernel
  apply eqA_of
  intro i hi
  rw [e, spDiag_get h (by norm_num) hi, spFlip_255 (spLen h.bind hi)]
  unfold negArrL
  rw [getElem!_ofFn_nat _ hi]

theorem spC_sign (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {m : ℕ} (hm : m < 256)
    (_he : framePop m % 2 = 0) : eqA 240 (spArrC L (m * 2 ^ 24 + spId)) (signArrsL L)[m]! = true := by
  apply eqA_of
  intro i hi
  rw [spDiag_get h hm hi, signArrs_get hm]
  unfold signArrL
  rw [getElem!_ofFn_nat _ hi]
  rfl

theorem spC_perm (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {c : ℕ} (hc : okC c = true)
    (h0 : spMask c = 0) : eqA 240 (spArrC L c) (listPermArrL L (codeL c)) = true := by
  apply eqA_of
  intro i hi
  rw [spArrC_get h hc hi, spVec, h0, spFlip_zero (by simp [listPermVec])]
  unfold listPermArrL
  rw [getElem!_ofFn_nat _ hi]

theorem spC_refl (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {r : ℕ} (hr : r < 112) :
    eqA 240 (reflArrL L r) (spArrC L (reflCodeK DP r)) = true := by
  obtain ⟨hok, hR⟩ := spReflK h hr
  apply eqA_of
  intro i hi
  rw [spArrC_get h hok hi]
  unfold reflArrL
  rw [getElem!_ofFn_nat _ hi]
  dsimp only
  rw [hR i hi]

theorem spC_frame (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) (hf : framesOK DP FR = true)
    {v : ℕ} (hv : v < 256) :
    eqA 240 (frameArrsL L)[v]! (spArrC L (frameCodeK DP FR v)) = true := by
  have hC : ∀ k : Fin 8, okC (reflCodeK DP (pg (nat_lit 8) (nat_lit 255) FR k)) = true ∧ ∀ j < 240,
      reflVec (L.getD (frameRootL L k) []) (L.getD j []) =
        spVec (reflCodeK DP (pg (nat_lit 8) (nat_lit 255) FR k)) (L.getD j []) := by
    intro k
    unfold framesOK at hf
    obtain ⟨hf1, -⟩ := band_true hf
    rw [Orb.allN_iff] at hf1
    have h112 : pg (nat_lit 8) (nat_lit 255) FR k < 112 := blt_true (hf1 k k.isLt)
    have hr : frameRootL L k = pg (nat_lit 8) (nat_lit 255) FR k := (spFrameRoot h k).2.2
    rw [hr]
    exact spReflK h h112
  have hcode : spRec (fun k => reflCodeK DP (pg (nat_lit 8) (nat_lit 255) FR k)) v 8 =
      frameCodeK DP FR v := by
    unfold spRec spStep frameCodeK
    rfl
  apply eqA_of
  intro i hi
  obtain ⟨e1, e2⟩ := spFold h (fun k => reflCodeK DP (pg (nat_lit 8) (nat_lit 255) FR k)) hC v hi
  rw [hcode] at e1 e2
  rw [spArrC_get h e2 hi, frameArrs_get hv]
  unfold frameArrL
  rw [getElem!_ofFn_nat _ hi]
  dsimp only
  rw [e1]

theorem spC_memE1 (h : SPBind L K RK RT ST FT PT SO NEG FR DP KP) {c : ℕ} (hc : okC c = true) :
    memE1L L K (frameArrsL L) (spArrC L c) = frameK' c := by
  unfold memE1L
  have hw : frameMaskOfL L K (spArrC L c) < 256 := Nat.mod_lt _ (by norm_num)
  cases hk : frameK' c
  · rw [Bool.eq_false_iff]
    intro hq
    obtain ⟨-, hok⟩ := spFrame_get h hw (i := 0) (by norm_num)
    have e := spCode_eq h hc hok fun i hi => by
      have e := eqA_spec hq i hi
      rw [spArrC_get h hc hi, (spFrame_get h hw hi).1] at e
      exact spIdx_inj h.bind (spVec_in h hc hi) (spVec_in h hok hi) e
    rw [e, (fcK_ok _ hw).2] at hk
    exact Bool.noConfusion hk
  · obtain ⟨t, u, rfl⟩ := spFrameK' hc hk
    have hv := vtu_lt t u
    have hmask : frameMaskOfL L K (spArrC L (codeTU t u)) = vtu t u := by
      unfold frameMaskOfL
      rw [foldl_filter_pow', Nat.mod_eq_of_lt (lt_of_lt_of_eq (sumN_pow_lt' _ 8) (by norm_num))]
      conv_rhs => rw [← spBits8 _ hv]
      apply sumN_congr''
      intro i hi
      obtain ⟨k1, k2⟩ := bindList_get h.keys hi
      have hneg : (negArrL L)[K.getD i 0]! = L.idxOf ((L.getD (K.getD i 0) []).map (-·)) := by
        unfold negArrL
        rw [k1, getElem!_ofFn_nat _ k2]
      have hneg' : L.idxOf ((L.getD (K.getD i 0) []).map (-·)) < 240 := by
        rw [← hneg, (tables_sound h.bind h.sorted h.refl h.neg).2, k1, Orb.unpack_get k2]
        have hn := h.neg
        unfold negTabOK at hn
        rw [Orb.allN_iff] at hn
        have := hn _ k2
        rw [Orb.strictB_eq] at this
        exact blt_true (band_true this).1
      rw [k1] at hneg hneg'
      rw [k1, spArrC_get h hc k2, hneg]
      have hiff : (L.idxOf (spVec (codeTU t u) (L.getD (pg 8 (mask 8) KP i) [])) ==
          L.idxOf ((L.getD (pg 8 (mask 8) KP i) []).map (-·))) = (vtu t u).testBit i := by
        have hx := spVec_in h hc k2
        have tv : spVec (codeTU t u) (vecOf (frameKey i)) = if (vtu t u).testBit i then
            (vecOf (frameKey i)).map (-·) else vecOf (frameKey i) := tu_vec t u ⟨i, hi⟩
        have fn : (vecOf (frameKey i)).map (-·) ≠ vecOf (frameKey i) := frame_neg ⟨i, hi⟩
        rw [Bool.eq_iff_iff, beq_iff_eq]
        constructor
        · intro e
          have e' := spIdx_inj h.bind hx hneg' e
          by_contra hb
          have hb' : (vtu t u).testBit i = false := by simpa using hb
          rw [hb'] at tv
          rcases spKey_vec h hi with hq | hq
          · rw [hq, tv] at e'
            simp only [Bool.false_eq_true, ite_false] at e'
            exact fn e'.symm
          · rw [hq, spVec_neg, tv] at e'
            simp only [Bool.false_eq_true, ite_false] at e'
            rw [spNeg_neg] at e'
            exact fn e'
        · intro hb
          rw [hb] at tv
          simp only [ite_true] at tv
          rcases spKey_vec h hi with hq | hq
          · rw [hq, tv]
          · rw [hq, spVec_neg, tv]
      rw [hiff]
    rw [hmask]
    apply eqA_of
    intro i hi
    rw [spArrC_get h hc hi, (spFrame_get h hv hi).1, fcK_tu]

end CFSG.KLC.E8

end
