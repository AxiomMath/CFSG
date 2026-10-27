module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Blk
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParD

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def tM2 : Mat8 := toMat 8 8 t2Bits

@[expose] def aM2 (m : ℕ) : Mat8 := toMat 8 8 (aBits2 m)

@[expose] def n0M2 (j : ℕ) : Mat8 := toMat 8 8 (n0Bits2 j)

@[expose] def n1M2 (j : ℕ) : Mat8 := toMat 8 8 (n1Bits2 j)

@[expose] def candM (z i : ℕ) : Mat8 := toMat 8 8 (candBlock z i)

@[expose] def entry8 (M : Mat8) (r c : ℕ) : ZMod 2 :=
  if h : r < 8 ∧ c < 8 then M ⟨r, h.1⟩ ⟨c, h.2⟩ else 0

@[expose] def msum8 (k mask : ℕ) (f : ℕ → Mat8) : Mat8 :=
  ∑ m ∈ Finset.range k, bz (mask.testBit m) • f m

theorem entry8_toMat (A : Array ℕ) {r c : ℕ} (hr : r < 8) (hc : c < 8) :
    entry8 (toMat 8 8 A) r c = bz ((A.getD r 0).testBit c) := by
  rw [entry8, dite_eq_left ⟨hr, hc⟩, toMat_apply]

theorem msum8_eq_of_lt {k mask : ℕ} {f g : ℕ → Mat8} (h : ∀ m < k, f m = g m) :
    msum8 k mask f = msum8 k mask g :=
  Finset.sum_congr rfl fun m hm => by rw [h m (Finset.mem_range.mp hm)]

theorem msum8_add (k mask : ℕ) (f g : ℕ → Mat8) :
    msum8 k mask (f + g) = msum8 k mask f + msum8 k mask g := by
  simp [msum8, smul_add, Finset.sum_add_distrib]

theorem msum8_smul (k mask : ℕ) (c : ZMod 2) (f : ℕ → Mat8) :
    msum8 k mask (c • f) = c • msum8 k mask f := by
  simp [msum8, Finset.smul_sum, smul_comm c]

theorem entry8_add (M N : Mat8) (r c : ℕ) : entry8 (M + N) r c = entry8 M r c + entry8 N r c := by
  unfold entry8; split_ifs <;> simp

theorem entry8_smul (a : ZMod 2) (M : Mat8) (r c : ℕ) :
    entry8 (a • M) r c = a * entry8 M r c := by
  unfold entry8; split_ifs <;> simp

@[expose] def ext5M (C : Fin 5 → Mat8) (s : ℕ) : Mat8 := if h : s < 5 then C ⟨s, h⟩ else 0

theorem ext5M_add (C C' : Fin 5 → Mat8) : ext5M (C + C') = ext5M C + ext5M C' := by
  ext1 s; simp only [ext5M, Pi.add_apply]; split_ifs <;> simp

theorem ext5M_smul (a : ZMod 2) (C : Fin 5 → Mat8) : ext5M (a • C) = a • ext5M C := by
  ext1 s; simp only [ext5M, Pi.smul_apply]; split_ifs <;> simp

theorem toMat_transpose_mulVec8 (n m : ℕ) (A : Array ℕ) (e : Fin n → ZMod 2) :
    (toMat n m A)ᵀ *ᵥ e = ∑ c : Fin n, e c • toVec m (A.getD c 0) := by
  ext i
  simp only [mulVec, dotProduct, transpose_apply, toMat_apply, Finset.sum_apply, Pi.smul_apply,
    toVec, smul_eq_mul, mul_comm]

theorem blocksOf_packBlks8 (k : ℕ) (f : ℕ → Array ℕ) :
    blocksOf k (toVec (k * 64) (packBlks k f)) = fun s : Fin k => toMat 8 8 (f s) := by
  rw [toVec_packBlks, blocksOf_vecOf]

theorem blocksOf_add8 (k : ℕ) (y y' : Fin (k * 64) → ZMod 2) :
    blocksOf k (y + y') = blocksOf k y + blocksOf k y' :=
  (blocksEquiv k).map_add y y'

theorem blocksOf_sum8 {ι : Type} (s : Finset ι) (k : ℕ) (y : ι → Fin (k * 64) → ZMod 2) :
    blocksOf k (∑ c ∈ s, y c) = ∑ c ∈ s, blocksOf k (y c) :=
  map_sum (blocksEquiv k) y s

theorem blocksOf_smul8 (k : ℕ) (a : ZMod 2) (y : Fin (k * 64) → ZMod 2) :
    blocksOf k (a • y) = a • blocksOf k y :=
  (blocksEquiv k).map_smul a y

theorem toMat_zero8' : toMat 8 8 zero8 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_msum2 (k mask : ℕ) (f : ℕ → Array ℕ) :
    toMat 8 8 (msum2 k mask f) = msum8 k mask fun m => toMat 8 8 (f m) := by
  induction k with
  | zero => simp [msum2, msum8, toMat_zero8']
  | succ k ih =>
    rw [msum2, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, msum8,
      Finset.sum_range_succ]
    rw [msum2] at ih
    by_cases h : mask.testBit k
    · rw [ite_eq_left h, toMat_bxor, ih, msum8, h, bz_true, one_smul]
    · rw [ite_eq_right h, ih, msum8, Bool.eq_false_iff.mpr h, bz_false, zero_smul, add_zero]

@[expose] def lamOfM (L : Mat8) (j m : ℕ) (q : ℕ) : ZMod 2 :=
  entry8 L (2 * j + m / 2) (4 * (m % 2) + q)

theorem bz_lamMaskOf (L : Array ℕ) {j m q : ℕ} (hj : j < 4) (hm : m < 4) (hq : q < 4) :
    bz ((lamMaskOf L j m).testBit q) = lamOfM (toMat 8 8 L) j m q := by
  rw [lamOfM, entry8_toMat _ (by omega) (by omega), lamMaskOf]
  congr 1
  rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [hq, decide_true, Bool.true_and]

@[expose] def dBlockM2 (C : ℕ → Mat8) (k : ℕ) : Mat8 :=
  if k < 4 then tM2 * C k * tM2 + C k
  else
    n0M2 ((k - 4) / 4) * C ((k - 4) % 4) * n1M2 ((k - 4) / 4) +
        msum8 4 (cMask2 ((k - 4) / 4) ((k - 4) % 4)) C +
      ∑ q ∈ Finset.range 4, lamOfM (C 4) ((k - 4) / 4) ((k - 4) % 4) q • aM2 q

theorem dBlockM2_congr {C C' : ℕ → Mat8} (h : ∀ s < 5, C s = C' s) (k : ℕ) (hk : k < 20) :
    dBlockM2 C k = dBlockM2 C' k := by
  unfold dBlockM2
  split_ifs with h1
  · rw [h k (by omega)]
  · rw [h ((k - 4) % 4) (by omega), h 4 (by omega), msum8_eq_of_lt fun m hm => h m (by omega)]

theorem toMat_dBlock2 (B : ℕ → Array ℕ) (k : ℕ) (hk : k < 20) :
    toMat 8 8 (dBlock2 B k) = dBlockM2 (fun s => toMat 8 8 (B s)) k := by
  unfold dBlock2 dBlockM2
  split_ifs with h1
  · rw [toMat_bxor, toMat_bmul, toMat_bmul]; rfl
  · rw [toMat_bxor, toMat_bxor, toMat_bmul, toMat_bmul, toMat_msum2, toMat_msum2, msum8]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [bz_lamMaskOf _ (by omega) (by omega) (Finset.mem_range.mp hq)]
    rfl

theorem dBlockM2_add (C C' : ℕ → Mat8) (k : ℕ) :
    dBlockM2 (C + C') k = dBlockM2 C k + dBlockM2 C' k := by
  unfold dBlockM2 lamOfM
  split_ifs
  · simp only [Pi.add_apply]; noncomm_ring
  · simp only [Pi.add_apply, msum8_add, entry8_add, add_smul, Finset.sum_add_distrib]
    noncomm_ring

theorem dBlockM2_smul (a : ZMod 2) (C : ℕ → Mat8) (k : ℕ) :
    dBlockM2 (a • C) k = a • dBlockM2 C k := by
  unfold dBlockM2 lamOfM
  split_ifs
  · simp [smul_add]
  · simp only [Pi.smul_apply, msum8_smul, entry8_smul, smul_add, mul_smul_comm, smul_mul_assoc,
      Finset.smul_sum, mul_smul]

@[expose] def dLin2 : (Fin 5 → Mat8) →ₗ[ZMod 2] (Fin 20 → Mat8) where
  toFun C k := dBlockM2 (ext5M C) k
  map_add' C C' := by ext1 k; simp only [ext5M_add, dBlockM2_add, Pi.add_apply]
  map_smul' a C := by
    ext1 k; simp only [ext5M_smul, dBlockM2_smul, Pi.smul_apply, RingHom.id_apply]

@[expose] def dF2 : (Fin (5 * 64) → ZMod 2) →ₗ[ZMod 2] (Fin (20 * 64) → ZMod 2) :=
  (blocksEquiv 20).symm.toLinearMap ∘ₗ dLin2 ∘ₗ (blocksEquiv 5).toLinearMap

theorem toVec_dFb2 (v : ℕ) : toVec (20 * 64) (dFb2 v) = dF2 (toVec (5 * 64) v) := by
  rw [dFb2, toVec_packBlks]
  simp only [dF2, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_symm_apply,
    blocksEquiv_apply]
  congr 1
  ext1 k
  rw [toMat_dBlock2 _ _ k.isLt]
  refine dBlockM2_congr (fun s hs => ?_) k k.isLt
  rw [ext5M, dite_eq_left hs, ← toMat_unpackBlk 5 v ⟨s, hs⟩]

theorem dCheck2_cert :
    certCheckWith (5 * 64) 18 (20 * 64) (linBits (5 * 64) (20 * 64) dFb2) dCols2 dEcols2
      dQcols2 = true := by
  have h := dCheck2W_eq_true
  rw [dCheck2W, Bool.and_eq_true] at h
  exact h.1

theorem dCheck2_cand {z : ℕ} (hz : z < 4) :
    dFb2 (packBlks 5 fun s => candBlock z s) = dTarget2 := by
  have h := dCheck2W_eq_true
  rw [dCheck2W, Bool.and_eq_true, List.all_eq_true] at h
  exact beq_iff_eq.mp (h.2 z (List.mem_range.mpr hz))

theorem dTarget2_vec : toVec (20 * 64) dTarget2 =
    vecOf 20 fun k => if (k : ℕ) < 4 then aM2 k else 0 := by
  rw [dTarget2, toVec_packBlks]
  congr 1
  ext1 k
  split_ifs
  · rfl
  · exact toMat_zero8'

theorem exists_dCols2 {C : Fin 5 → Mat8}
    (hC : ∀ k : Fin 20, dLin2 C k = if (k : ℕ) < 4 then aM2 k else 0) :
    ∃ e : Fin 18 → ZMod 2, C = blocksOf 5 (toVec (5 * 64) dY0b) +
      ∑ c : Fin 18, e c • blocksOf 5 (toVec (5 * 64) (dCols2.getD c 0)) := by
  have h1 : dF2 (vecOf 5 C) = toVec (20 * 64) dTarget2 := by
    rw [dTarget2_vec]
    simp only [dF2, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquiv_apply, blocksOf_vecOf,
      blocksEquiv_symm_apply]
    congr 1
    ext1 k
    exact hC k
  have h2 : dF2 (toVec (5 * 64) dY0b) = toVec (20 * 64) dTarget2 := by
    rw [← toVec_dFb2]
    have := y0Check2_eq_true
    rw [y0Check2, beq_iff_eq] at this
    rw [this]
  have h3 : toMat (20 * 64) (5 * 64) (linBits (5 * 64) (20 * 64) dFb2) *ᵥ
      (vecOf 5 C - toVec (5 * 64) dY0b) = 0 := by
    rw [toMat_linBits_mulVec dFb2 dF2 (fun j => by rw [toVec_dFb2, toVec_two_pow]), map_sub, h1,
      h2]
    exact sub_self _
  obtain ⟨e, he⟩ := exists_eq_mulVec_of_certCheckWith dCheck2_cert h3
  refine ⟨e, ?_⟩
  rw [sub_eq_iff_eq_add, toMat_transpose_mulVec8] at he
  have := congrArg (blocksOf 5) he
  rw [blocksOf_vecOf, blocksOf_add8, blocksOf_sum8] at this
  simp only [blocksOf_smul8] at this
  rw [this, add_comm]

@[expose] def aSpan2 : Submodule (ZMod 2) Mat8 :=
  Submodule.span (ZMod 2) (Set.range fun m : Fin 4 => aM2 m)

theorem aM2_mem (m : Fin 4) : aM2 m ∈ aSpan2 := Submodule.subset_span ⟨m, rfl⟩

theorem dCols2_getD (c : Fin 18) :
    dCols2.getD c 0 =
      if (c : ℕ) < 2 then dDir2 c else dAmb2 (((c : ℕ) - 2) / 4) (((c : ℕ) - 2) % 4) :=
  getD_ofFn _ c

theorem block_dY0b (i : Fin 5) :
    blocksOf 5 (toVec (5 * 64) dY0b) i = toMat 8 8 (dY0Blocks2.getD i zero8) := by
  rw [dY0b, ofBlocks2, blocksOf_packBlks8]

theorem block_dDir2 (q : ℕ) (i : Fin 5) :
    blocksOf 5 (toVec (5 * 64) (dDir2 q)) i = toMat 8 8 ((dDirBlocks2 q).getD i zero8) := by
  rw [dDir2, ofBlocks2, blocksOf_packBlks8]

theorem block_dAmb2 (i' m : ℕ) (i : Fin 5) (hi : (i : ℕ) < 4) :
    blocksOf 5 (toVec (5 * 64) (dAmb2 i' m)) i = if (i : ℕ) = i' then aM2 m else 0 := by
  rw [dAmb2, blocksOf_packBlks8]
  simp only [hi, ite_true]
  split_ifs
  · rfl
  · exact toMat_zero8'

theorem candM_eq (z i : ℕ) : candM z i = toMat 8 8 (dY0Blocks2.getD i zero8) +
    (if z.testBit 0 then toMat 8 8 ((dDirBlocks2 0).getD i zero8) else 0) +
    (if z.testBit 1 then toMat 8 8 ((dDirBlocks2 1).getD i zero8) else 0) := by
  rw [candM, candBlock, toMat_bxor, toMat_bxor]
  congr 1 <;> [congr 1; skip] <;> split_ifs <;> first | rfl | exact toMat_zero8'

theorem exists_candidate2 (φ : Fin 4 → Mat8)
    (lam : Fin 4 → Fin 4 → Fin 4 → ZMod 2)
    (hδ : ∀ i : Fin 4, tM2 * φ i * tM2 + φ i = aM2 i)
    (hν : ∀ j m : Fin 4, n0M2 j * φ m * n1M2 j +
      msum8 4 (cMask2 j m) (fun n => if h : n < 4 then φ ⟨n, h⟩ else 0) +
      ∑ q : Fin 4, lam j m q • aM2 q = 0) :
    ∃ z < 4, ∀ i : Fin 4, φ i + candM z i ∈ aSpan2 := by
  set Λ : Mat8 := Matrix.of fun r c => lam ⟨(r : ℕ) / 2, by omega⟩
    ⟨2 * ((r : ℕ) % 2) + (c : ℕ) / 4, by omega⟩ ⟨(c : ℕ) % 4, by omega⟩ with hΛ
  set C : Fin 5 → Mat8 := fun s => if h : (s : ℕ) < 4 then φ ⟨s, h⟩ else Λ with hCdef
  have hext : ∀ s (hs : s < 4), ext5M C s = φ ⟨s, hs⟩ := fun s hs => by
    simp [ext5M, C, show s < 5 by omega, hs]
  have hext4 : ext5M C 4 = Λ := by simp [ext5M, C]
  have hlam : ∀ (j m q : ℕ) (hj : j < 4) (hm : m < 4) (hq : q < 4),
      lamOfM Λ j m q = lam ⟨j, hj⟩ ⟨m, hm⟩ ⟨q, hq⟩ := by
    intro j m q hj hm hq
    rw [lamOfM, entry8, dite_eq_left ⟨by omega, by omega⟩, hΛ, Matrix.of_apply]
    congr 1 <;> ext <;> simp <;> omega
  have hC : ∀ k : Fin 20, dLin2 C k = if (k : ℕ) < 4 then aM2 k else 0 := by
    intro k
    change dBlockM2 (ext5M C) k = _
    unfold dBlockM2
    split_ifs with h1
    · rw [hext k h1]; exact hδ ⟨k, h1⟩
    · have hj : ((k : ℕ) - 4) / 4 < 4 := by omega
      have hm : ((k : ℕ) - 4) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have := hν ⟨_, hj⟩ ⟨_, hm⟩
      have e1 : msum8 4 (cMask2 (((k : ℕ) - 4) / 4) (((k : ℕ) - 4) % 4)) (ext5M C) =
          msum8 4 (cMask2 (((k : ℕ) - 4) / 4) (((k : ℕ) - 4) % 4))
            (fun n => if h : n < 4 then φ ⟨n, h⟩ else 0) :=
        msum8_eq_of_lt fun n hn => by rw [hext n hn, dite_eq_left hn]
      have e2 : ∑ q ∈ Finset.range 4, lamOfM (ext5M C 4) (((k : ℕ) - 4) / 4)
          (((k : ℕ) - 4) % 4) q • aM2 q = ∑ q : Fin 4, lam ⟨_, hj⟩ ⟨_, hm⟩ q • aM2 q := by
        rw [Finset.sum_range (fun q => lamOfM (ext5M C 4) (((k : ℕ) - 4) / 4)
          (((k : ℕ) - 4) % 4) q • aM2 q)]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hext4, hlam _ _ _ hj hm q.isLt]
      rw [hext _ hm, e1, e2]
      exact this
  obtain ⟨e, he⟩ := exists_dCols2 hC
  have hamb : ∀ i : Fin 4, ∑ c : Fin 16, (e (Fin.natAdd 2 c) • blocksOf 5 (toVec (5 * 64)
      (dCols2.getD (Fin.natAdd 2 c : Fin 18) 0))) ⟨i, by omega⟩ ∈ aSpan2 := by
    intro i
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [Pi.smul_apply, dCols2_getD, ite_eq_right (by simp only [Fin.val_natAdd]; omega),
      block_dAmb2 _ _ _ (by simp)]
    refine Submodule.smul_mem _ _ ?_
    split_ifs
    · exact aM2_mem ⟨_, Nat.mod_lt _ (by norm_num)⟩
    · exact Submodule.zero_mem _
  have hφi : ∀ i : Fin 4, φ i = toMat 8 8 (dY0Blocks2.getD i zero8) +
      (e 0 • toMat 8 8 ((dDirBlocks2 0).getD i zero8) +
        e 1 • toMat 8 8 ((dDirBlocks2 1).getD i zero8)) +
      ∑ c : Fin 16, (e (Fin.natAdd 2 c) • blocksOf 5 (toVec (5 * 64)
        (dCols2.getD (Fin.natAdd 2 c : Fin 18) 0))) ⟨i, by omega⟩ := by
    intro i
    have hi := congrFun he ⟨i, by omega⟩
    have hφ : C ⟨i, by omega⟩ = φ i := by simp [C]
    rw [hφ, Pi.add_apply, Finset.sum_apply, block_dY0b] at hi
    have hB0 : (e (Fin.castAdd 16 (0 : Fin 2)) • blocksOf 5 (toVec (5 * 64)
        (dCols2.getD (Fin.castAdd 16 (0 : Fin 2) : Fin 18) 0))) ⟨i, by omega⟩ =
        e 0 • toMat 8 8 ((dDirBlocks2 0).getD i zero8) := by
      rw [Pi.smul_apply, show (Fin.castAdd 16 (0 : Fin 2) : Fin 18) = 0 from rfl, dCols2_getD,
        ite_eq_left (by simp), block_dDir2]; rfl
    have hB1 : (e (Fin.castAdd 16 (1 : Fin 2)) • blocksOf 5 (toVec (5 * 64)
        (dCols2.getD (Fin.castAdd 16 (1 : Fin 2) : Fin 18) 0))) ⟨i, by omega⟩ =
        e 1 • toMat 8 8 ((dDirBlocks2 1).getD i zero8) := by
      rw [Pi.smul_apply, show (Fin.castAdd 16 (1 : Fin 2) : Fin 18) = 1 from rfl, dCols2_getD,
        ite_eq_left (by simp), block_dDir2]; rfl
    rw [hi, Fin.sum_univ_add (a := 2) (b := 16), Fin.sum_univ_two, hB0, hB1]
    abel
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have key : ∀ z < 4, (∀ X : Mat8, e 0 • X = if z.testBit 0 then X else 0) →
      (∀ X : Mat8, e 1 • X = if z.testBit 1 then X else 0) →
      ∃ z < 4, ∀ i : Fin 4, φ i + candM z i ∈ aSpan2 := by
    intro z hz h0 h1
    refine ⟨z, hz, fun i => ?_⟩
    rw [hφi i, candM_eq, h0, h1]
    have hr : ∀ a b c e' : Mat8, a + (b + c) + e' + (a + b + c) =
        e' + ((a + a) + (b + b) + (c + c)) := by intros; abel
    rw [hr]
    simp only [matN_add_self, add_zero]
    exact hamb i
  rcases hcases (e 0) with h0 | h0 <;> rcases hcases (e 1) with h1 | h1
  · exact key 0 (by norm_num)
      (fun X => by rw [h0, zero_smul, show Nat.testBit 0 0 = false by decide]; simp)
      (fun X => by rw [h1, zero_smul, show Nat.testBit 0 1 = false by decide]; simp)
  · exact key 2 (by norm_num)
      (fun X => by rw [h0, zero_smul, show Nat.testBit 2 0 = false by decide]; simp)
      (fun X => by rw [h1, one_smul, show Nat.testBit 2 1 = true by decide]; simp)
  · exact key 1 (by norm_num)
      (fun X => by rw [h0, one_smul, show Nat.testBit 1 0 = true by decide]; simp)
      (fun X => by rw [h1, zero_smul, show Nat.testBit 1 1 = false by decide]; simp)
  · exact key 3 (by norm_num)
      (fun X => by rw [h0, one_smul, show Nat.testBit 3 0 = true by decide]; simp)
      (fun X => by rw [h1, one_smul, show Nat.testBit 3 1 = true by decide]; simp)

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
