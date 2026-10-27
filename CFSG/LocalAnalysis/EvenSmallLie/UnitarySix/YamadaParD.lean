module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParDCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

abbrev Mat8 : Type := Matrix (Fin 8) (Fin 8) (ZMod 2)

@[expose] def tM : Mat8 := toMat 8 8 tBits

@[expose] def aM (m : ℕ) : Mat8 := toMat 8 8 (aBits m)

@[expose] def n0M (j : ℕ) : Mat8 := toMat 8 8 (n0Bits j)

@[expose] def n1M (j : ℕ) : Mat8 := toMat 8 8 (n1Bits j)

@[expose] def cM (j l i : ℕ) : ZMod 2 := bz ((cMask j i).testBit l)

@[expose] def hiM : Mat8 := toMat 8 8 hiMask

@[expose] def entry (M : Mat8) (r c : ℕ) : ZMod 2 :=
  if h : r < 8 ∧ c < 8 then M ⟨r, h.1⟩ ⟨c, h.2⟩ else 0

@[expose] def msumM (k mask : ℕ) (f : ℕ → Mat8) : Mat8 :=
  ∑ m ∈ Finset.range k, bz (mask.testBit m) • f m

theorem toMat_msum (k mask : ℕ) (f : ℕ → Array ℕ) :
    toMat 8 8 (msum k mask f) = msumM k mask fun m => toMat 8 8 (f m) := by
  induction k with
  | zero => simp [msum, msumM, toMat_zero8]
  | succ k ih =>
    rw [msum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, msumM,
      Finset.sum_range_succ]
    rw [msum] at ih
    by_cases h : mask.testBit k
    · rw [ite_eq_left h, toMat_bxor, ih, msumM, h, bz_true, one_smul]
    · rw [ite_eq_right h, ih, msumM, Bool.eq_false_iff.mpr h, bz_false, zero_smul, add_zero]

theorem entry_toMat (A : Array ℕ) {r c : ℕ} (hr : r < 8) (hc : c < 8) :
    entry (toMat 8 8 A) r c = bz ((A.getD r 0).testBit c) := by
  rw [entry, dite_eq_left ⟨hr, hc⟩, toMat_apply]

@[expose] def dBlockM (C : ℕ → Mat8) (k : ℕ) : Mat8 :=
  if k < 4 then tM * C k * tM + C k
  else if k < 12 then
    n0M ((k - 4) / 4) * C ((k - 4) % 4) * n1M ((k - 4) / 4) +
        msumM 4 (cMask ((k - 4) / 4) ((k - 4) % 4)) C +
      ∑ m ∈ Finset.range 4, entry (C 4) (4 * ((k - 4) / 4) + (k - 4) % 4) m • aM m
  else C 4 * hiM

theorem msumM_eq_of_lt {k mask : ℕ} {f g : ℕ → Mat8} (h : ∀ m < k, f m = g m) :
    msumM k mask f = msumM k mask g :=
  Finset.sum_congr rfl fun m hm => by rw [h m (Finset.mem_range.mp hm)]

theorem dBlockM_congr {C C' : ℕ → Mat8} (h : ∀ s < 5, C s = C' s) (k : ℕ) :
    dBlockM C k = dBlockM C' k := by
  unfold dBlockM
  split_ifs with h1 h2
  · rw [h k (by omega)]
  · rw [h ((k - 4) % 4) (by omega), h 4 (by omega),
      msumM_eq_of_lt fun m hm => h m (by omega)]
  · rw [h 4 (by omega)]

theorem toMat_dBlock (B : ℕ → Array ℕ) (k : ℕ) :
    toMat 8 8 (dBlock B k) = dBlockM (fun s => toMat 8 8 (B s)) k := by
  unfold dBlock dBlockM
  split_ifs with h1 h2
  · rw [toMat_bxor, toMat_bmul, toMat_bmul]; rfl
  · rw [toMat_bxor, toMat_bxor, toMat_bmul, toMat_bmul, toMat_msum, toMat_msum, msumM]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [entry_toMat _ (by omega) (by have := Finset.mem_range.mp hm; omega)]
    rfl
  · rw [toMat_bmul]; rfl

theorem msumM_add (k mask : ℕ) (f g : ℕ → Mat8) :
    msumM k mask (f + g) = msumM k mask f + msumM k mask g := by
  simp [msumM, smul_add, Finset.sum_add_distrib]

theorem msumM_smul (k mask : ℕ) (c : ZMod 2) (f : ℕ → Mat8) :
    msumM k mask (c • f) = c • msumM k mask f := by
  simp [msumM, Finset.smul_sum, smul_comm c]

theorem entry_add (M N : Mat8) (r c : ℕ) : entry (M + N) r c = entry M r c + entry N r c := by
  unfold entry; split_ifs <;> simp

theorem entry_smul (a : ZMod 2) (M : Mat8) (r c : ℕ) : entry (a • M) r c = a * entry M r c := by
  unfold entry; split_ifs <;> simp

theorem dBlockM_add (C C' : ℕ → Mat8) (k : ℕ) :
    dBlockM (C + C') k = dBlockM C k + dBlockM C' k := by
  unfold dBlockM
  split_ifs
  · simp only [Pi.add_apply]; noncomm_ring
  · simp only [Pi.add_apply, msumM_add, entry_add, add_smul, Finset.sum_add_distrib]
    noncomm_ring
  · simp only [Pi.add_apply, add_mul]

theorem dBlockM_smul (a : ZMod 2) (C : ℕ → Mat8) (k : ℕ) :
    dBlockM (a • C) k = a • dBlockM C k := by
  unfold dBlockM
  split_ifs
  · simp [smul_add]
  · simp only [Pi.smul_apply, msumM_smul, entry_smul, smul_add, mul_smul_comm, smul_mul_assoc,
      Finset.smul_sum, mul_smul]
  · simp only [Pi.smul_apply, smul_mul_assoc]

@[expose] def ext5 (C : Fin 5 → Mat8) (s : ℕ) : Mat8 := if h : s < 5 then C ⟨s, h⟩ else 0

theorem ext5_add (C C' : Fin 5 → Mat8) : ext5 (C + C') = ext5 C + ext5 C' := by
  ext1 s; simp only [ext5, Pi.add_apply]; split_ifs <;> simp

theorem ext5_smul (a : ZMod 2) (C : Fin 5 → Mat8) : ext5 (a • C) = a • ext5 C := by
  ext1 s; simp only [ext5, Pi.smul_apply]; split_ifs <;> simp

@[expose] def dLin : (Fin 5 → Mat8) →ₗ[ZMod 2] (Fin 13 → Mat8) where
  toFun C k := dBlockM (ext5 C) k
  map_add' C C' := by ext1 k; simp only [ext5_add, dBlockM_add, Pi.add_apply]
  map_smul' a C := by ext1 k; simp only [ext5_smul, dBlockM_smul, Pi.smul_apply, RingHom.id_apply]

@[expose] def dF : (Fin (5 * 64) → ZMod 2) →ₗ[ZMod 2] (Fin (13 * 64) → ZMod 2) :=
  (blocksEquiv 13).symm.toLinearMap ∘ₗ dLin ∘ₗ (blocksEquiv 5).toLinearMap

theorem toVec_dFb (v : ℕ) : toVec (13 * 64) (dFb v) = dF (toVec (5 * 64) v) := by
  rw [dFb, toVec_packBlks]
  simp only [dF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_symm_apply,
    blocksEquiv_apply]
  congr 1
  ext1 k
  rw [toMat_dBlock]
  refine dBlockM_congr (fun s hs => ?_) k
  rw [ext5, dite_eq_left hs, ← toMat_unpackBlk 5 v ⟨s, hs⟩]

theorem toMat_transpose_mulVec (n m : ℕ) (A : Array ℕ) (e : Fin n → ZMod 2) :
    (toMat n m A)ᵀ *ᵥ e = ∑ c : Fin n, e c • toVec m (A.getD c 0) := by
  ext i
  simp only [mulVec, dotProduct, transpose_apply, toMat_apply, Finset.sum_apply, Pi.smul_apply,
    toVec, smul_eq_mul, mul_comm]

theorem blocksOf_packBlks (k : ℕ) (f : ℕ → Array ℕ) :
    blocksOf k (toVec (k * 64) (packBlks k f)) = fun s : Fin k => toMat 8 8 (f s) := by
  rw [toVec_packBlks, blocksOf_vecOf]

theorem blocksOf_add (k : ℕ) (y y' : Fin (k * 64) → ZMod 2) :
    blocksOf k (y + y') = blocksOf k y + blocksOf k y' :=
  (blocksEquiv k).map_add y y'

theorem blocksOf_sum {ι : Type} (s : Finset ι) (k : ℕ) (y : ι → Fin (k * 64) → ZMod 2) :
    blocksOf k (∑ c ∈ s, y c) = ∑ c ∈ s, blocksOf k (y c) :=
  map_sum (blocksEquiv k) y s

theorem blocksOf_smul (k : ℕ) (a : ZMod 2) (y : Fin (k * 64) → ZMod 2) :
    blocksOf k (a • y) = a • blocksOf k y :=
  (blocksEquiv k).map_smul a y

theorem exists_dCols {C : Fin 5 → Mat8}
    (hC : ∀ k : Fin 13, dLin C k = if (k : ℕ) < 4 then aM k else 0) :
    ∃ e : Fin 19 → ZMod 2, C = blocksOf 5 (toVec (5 * 64) dY0) +
      ∑ c : Fin 19, e c • blocksOf 5 (toVec (5 * 64) (dCols.getD c 0)) := by
  have hT : toVec (13 * 64) dTarget = vecOf 13 fun k => if (k : ℕ) < 4 then aM k else 0 := by
    rw [dTarget, toVec_packBlks]
    congr 1
    ext1 k
    split_ifs
    · rfl
    · exact toMat_zero8
  have h1 : dF (vecOf 5 C) = toVec (13 * 64) dTarget := by
    rw [hT]
    simp only [dF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_apply, blocksOf_vecOf,
      blocksEquiv_symm_apply]
    congr 1
    ext1 k
    exact hC k
  have h2 : dF (toVec (5 * 64) dY0) = toVec (13 * 64) dTarget := by
    rw [← toVec_dFb]
    have := y0Check_eq_true
    rw [y0Check, beq_iff_eq] at this
    rw [this]
  have h3 : toMat (13 * 64) (5 * 64) (linBits (5 * 64) (13 * 64) dFb) *ᵥ
      (vecOf 5 C - toVec (5 * 64) dY0) = 0 := by
    rw [toMat_linBits_mulVec dFb dF (fun j => by rw [toVec_dFb, toVec_two_pow]), map_sub, h1, h2]
    exact sub_self _
  obtain ⟨e, he⟩ := exists_eq_mulVec_of_certCheckWith dCheckW_eq_true h3
  refine ⟨e, ?_⟩
  rw [sub_eq_iff_eq_add, toMat_transpose_mulVec] at he
  have := congrArg (blocksOf 5) he
  rw [blocksOf_vecOf, blocksOf_add, blocksOf_sum] at this
  simp only [blocksOf_smul] at this
  rw [this, add_comm]

@[expose] def y0M (i : ℕ) : Mat8 := toMat 8 8 (dY0Blocks.getD i zero8)

@[expose] def dirM (q i : ℕ) : Mat8 := toMat 8 8 ((dDirBlocks q).getD i zero8)

@[expose] def aSpan : Submodule (ZMod 2) Mat8 :=
  Submodule.span (ZMod 2) (Set.range fun m : Fin 4 => aM m)

theorem hiM_apply (l c : Fin 8) : hiM l c = if l = c ∧ 4 ≤ (l : ℕ) then 1 else 0 := by
  fin_cases l <;> fin_cases c <;> rfl

theorem aM_mem_aSpan (m : Fin 4) : aM m ∈ aSpan := Submodule.subset_span ⟨m, rfl⟩

theorem block_dY0 (i : Fin 5) : blocksOf 5 (toVec (5 * 64) dY0) i = y0M i := by
  rw [dY0, ofBlocks, blocksOf_packBlks]; rfl

theorem block_dDir (q : ℕ) (i : Fin 5) : blocksOf 5 (toVec (5 * 64) (dDir q)) i = dirM q i := by
  rw [dDir, ofBlocks, blocksOf_packBlks]; rfl

theorem block_dAmb (i' m : ℕ) (i : Fin 5) (hi : (i : ℕ) < 4) :
    blocksOf 5 (toVec (5 * 64) (dAmb i' m)) i = if (i : ℕ) = i' then aM m else 0 := by
  rw [dAmb, blocksOf_packBlks]
  simp only [hi, ite_true]
  split_ifs
  · rfl
  · exact toMat_zero8

theorem dCols_getD (c : Fin 19) :
    dCols.getD c 0 = if (c : ℕ) < 3 then dDir c else dAmb (((c : ℕ) - 3) / 4) (((c : ℕ) - 3) % 4) :=
  getD_ofFn _ c

theorem exists_candidate (φ : Fin 4 → Mat8) (lam : Fin 2 → Fin 4 → Fin 4 → ZMod 2)
    (hδ : ∀ i : Fin 4, tM * φ i * tM + φ i = aM i)
    (hν : ∀ (j : Fin 2) (i : Fin 4), n0M j * φ i * n1M j + ∑ l : Fin 4, cM j l i • φ l +
      ∑ m : Fin 4, lam j i m • aM m = 0) :
    ∃ z : Fin 3 → ZMod 2, ∀ i : Fin 4,
      φ i - (y0M i + ∑ q : Fin 3, z q • dirM q i) ∈ aSpan := by
  set Λ : Mat8 := Matrix.of fun r c =>
    if h : (c : ℕ) < 4 then lam ⟨(r : ℕ) / 4, by omega⟩ ⟨(r : ℕ) % 4, by omega⟩ ⟨c, h⟩ else 0
    with hΛ
  set C : Fin 5 → Mat8 := fun s => if h : (s : ℕ) < 4 then φ ⟨s, h⟩ else Λ with hCdef
  have hext : ∀ s (hs : s < 4), ext5 C s = φ ⟨s, hs⟩ := fun s hs => by
    simp [ext5, C, show s < 5 by omega, hs]
  have hext4 : ext5 C 4 = Λ := by simp [ext5, C]
  have hC : ∀ k : Fin 13, dLin C k = if (k : ℕ) < 4 then aM k else 0 := by
    intro k
    change dBlockM (ext5 C) k = _
    unfold dBlockM
    split_ifs with h1 h2
    · rw [hext k h1]; exact hδ ⟨k, h1⟩
    · have hj : ((k : ℕ) - 4) / 4 < 2 := by omega
      have hi : ((k : ℕ) - 4) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have := hν ⟨_, hj⟩ ⟨_, hi⟩
      have e1 : msumM 4 (cMask (((k : ℕ) - 4) / 4) (((k : ℕ) - 4) % 4)) (ext5 C) =
          ∑ l : Fin 4, cM (((k : ℕ) - 4) / 4) l (((k : ℕ) - 4) % 4) • φ l := by
        rw [msumM, Finset.sum_range (fun l => bz ((cMask (((k : ℕ) - 4) / 4)
          (((k : ℕ) - 4) % 4)).testBit l) • ext5 C l)]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hext l l.isLt]; rfl
      have e2 : ∑ m ∈ Finset.range 4,
          entry (ext5 C 4) (4 * (((k : ℕ) - 4) / 4) + ((k : ℕ) - 4) % 4) m • aM m =
          ∑ m : Fin 4, lam ⟨_, hj⟩ ⟨_, hi⟩ m • aM m := by
        rw [Finset.sum_range (fun m => entry (ext5 C 4)
          (4 * (((k : ℕ) - 4) / 4) + ((k : ℕ) - 4) % 4) m • aM m)]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hext4, entry, dite_eq_left ⟨by omega, by omega⟩, hΛ, Matrix.of_apply,
          dite_eq_left (show ((⟨(m : ℕ), by omega⟩ : Fin 8) : ℕ) < 4 from m.isLt)]
        congr 3 <;> simp
        omega
      rw [hext _ hi, e1, e2]
      exact this
    · rw [hext4]
      ext r c
      rw [mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hiM_apply]
      split_ifs with hl
      · obtain ⟨rfl, hl4⟩ := hl
        simp [Λ, show ¬ (l : ℕ) < 4 by omega]
      · rw [mul_zero]
  obtain ⟨e, he⟩ := exists_dCols hC
  refine ⟨fun q => e (Fin.castAdd 16 q), fun i => ?_⟩
  have hi := congrFun he ⟨i, by omega⟩
  have hφ : C ⟨i, by omega⟩ = φ i := by simp [C]
  rw [hφ, Pi.add_apply, Finset.sum_apply, block_dY0] at hi
  have hsum := Fin.sum_univ_add (a := 3) (b := 16) fun c =>
    (e c • blocksOf 5 (toVec (5 * 64) (dCols.getD (c : ℕ) 0))) ⟨i, by omega⟩
  rw [hi, show ∑ c : Fin 19, (e c • blocksOf 5 (toVec (5 * 64) (dCols.getD (c : ℕ) 0)))
    ⟨i, by omega⟩ = _ from hsum]
  have hsplit : ∀ q : Fin 3, (e (Fin.castAdd 16 q) • blocksOf 5 (toVec (5 * 64)
      (dCols.getD (Fin.castAdd 16 q : Fin 19) 0))) ⟨i, by omega⟩ =
      e (Fin.castAdd 16 q) • dirM q i := fun q => by
    rw [Pi.smul_apply, dCols_getD, ite_eq_left (by simp), block_dDir]
    rfl
  simp only [hsplit]
  rw [show ∀ a b c : Mat8, a + (b + c) - (a + b) = c from fun a b c => by abel]
  refine Submodule.sum_mem _ fun r _ => ?_
  rw [Pi.smul_apply, dCols_getD, ite_eq_right (by simp), block_dAmb _ _ _ (by simp)]
  refine Submodule.smul_mem _ _ ?_
  split_ifs
  · exact aM_mem_aSpan ⟨_, Nat.mod_lt _ (by norm_num)⟩
  · exact Submodule.zero_mem _

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
