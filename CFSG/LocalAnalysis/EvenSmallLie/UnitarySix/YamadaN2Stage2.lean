module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Lay2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagCheck

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def tauM : Mat18 := toMat 18 18 tauBits

@[expose] def eM (m : ℕ) : Mat18 := toMat 18 18 (eBits18 m)

@[expose] def vM (j : ℕ) : Mat18 := toMat 18 18 (vBits j)

@[expose] def yM (z m : ℕ) : Mat18 := toMat 18 18 (yBits z m)

@[expose] def eProdM (mask : ℕ) : Mat18 := toMat 18 18 (eProdBits mask)

@[expose] def yProdM (z : ℕ) (l : List ℕ) : Mat18 := toMat 18 18 (yProd z l)

theorem toMat_foldl_bmul (B : ℕ → Array ℕ) (l : List ℕ) (A : Array ℕ) :
    toMat 18 18 (l.foldl (fun acc n => bmul 18 18 acc (B n)) A) =
      toMat 18 18 A * (l.map fun n => toMat 18 18 (B n)).prod := by
  induction l generalizing A with
  | nil => simp
  | cons n l ih => rw [List.foldl_cons, ih, toMat_bmul, List.map_cons, List.prod_cons, mul_assoc]

theorem toMat_foldl_bmul_if (p : ℕ → Bool) (B : ℕ → Array ℕ) (l : List ℕ) (A : Array ℕ) :
    toMat 18 18 (l.foldl (fun acc n => if p n then bmul 18 18 acc (B n) else acc) A) =
      toMat 18 18 A * ((l.filter p).map fun n => toMat 18 18 (B n)).prod := by
  induction l generalizing A with
  | nil => simp
  | cons n l ih =>
    rw [List.foldl_cons, ih]
    by_cases h : p n
    · rw [ite_eq_left h, toMat_bmul, List.filter_cons_of_pos h, List.map_cons, List.prod_cons,
        mul_assoc]
    · rw [ite_eq_right h, List.filter_cons_of_neg h]

theorem toMat_foldl_bxor (t : ℕ → Array ℕ) (n : ℕ) (A : Array ℕ) :
    toMat 18 18 ((List.range n).foldl (fun acc i => bxor 18 acc (t i)) A) =
      toMat 18 18 A + ∑ i ∈ Finset.range n, toMat 18 18 (t i) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, toMat_bxor, ih,
      Finset.sum_range_succ, add_assoc]

theorem toMat_id18 : toMat 18 18 id18 = 1 := by
  ext i j
  rw [toMat_apply, id18, getD_ofFn, one_apply_eq_bz, Nat.testBit_two_pow]
  congr 1

theorem eProdM_eq (mask : ℕ) : eProdM mask = ((bitList mask).map eM).prod := by
  rw [eProdM, eProdBits, toMat_foldl_bmul_if, toMat_id18, one_mul]
  rfl

theorem yProdM_eq (z : ℕ) (l : List ℕ) : yProdM z l = (l.map (yM z)).prod := by
  rw [yProdM, yProd, toMat_foldl_bmul, toMat_id18, one_mul]
  rfl

@[expose] def dsOf (δ : Fin 128 → ZMod 2) (m : ℕ) : Fin 32 → ZMod 2 :=
  fun k => if h : 32 * m + k < 128 then δ ⟨32 * m + k, h⟩ else 0

@[expose] def linEM (z j m : ℕ) (Δ : ℕ → Mat18) : Mat18 :=
  vM j * Δ m * vM j + ∑ i ∈ Finset.range (bitList (cMask2 j m)).length,
    Δ ((bitList (cMask2 j m)).getD i 0) *
      (yProdM z ((bitList (cMask2 j m)).drop (i + 1)) * eProdM (lamZ z j m))

@[expose] def s2OutM (z : ℕ) (Δ : ℕ → Mat18) (k : ℕ) : Mat18 :=
  if k < 4 then Δ k * (tauM * yM z k * tauM) + tauM * Δ k * tauM
  else linEM z ((k - 4) / 4) ((k - 4) % 4) Δ

@[expose] def tgtM (z k : ℕ) : Mat18 :=
  if k < 4 then eM k + yM z k * (tauM * yM z k * tauM)
  else yProdM z (bitList (cMask2 ((k - 4) / 4) ((k - 4) % 4))) *
      eProdM (lamZ z ((k - 4) / 4) ((k - 4) % 4)) +
    vM ((k - 4) / 4) * yM z ((k - 4) % 4) * vM ((k - 4) / 4)

theorem dsOf_add (δ δ' : Fin 128 → ZMod 2) (m : ℕ) : dsOf (δ + δ') m = dsOf δ m + dsOf δ' m := by
  ext k; simp only [dsOf, Pi.add_apply]; split_ifs <;> simp

theorem dsOf_smul (a : ZMod 2) (δ : Fin 128 → ZMod 2) (m : ℕ) :
    dsOf (a • δ) m = a • dsOf δ m := by
  ext k; simp only [dsOf, Pi.smul_apply]; split_ifs <;> simp

theorem linEM_add (z j m : ℕ) (Δ Δ' : ℕ → Mat18) :
    linEM z j m (Δ + Δ') = linEM z j m Δ + linEM z j m Δ' := by
  simp only [linEM, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  abel

theorem linEM_smul (z j m : ℕ) (a : ZMod 2) (Δ : ℕ → Mat18) :
    linEM z j m (a • Δ) = a • linEM z j m Δ := by
  simp only [linEM, Pi.smul_apply, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_add]

theorem s2OutM_add (z : ℕ) (Δ Δ' : ℕ → Mat18) (k : ℕ) :
    s2OutM z (Δ + Δ') k = s2OutM z Δ k + s2OutM z Δ' k := by
  unfold s2OutM
  split_ifs
  · simp only [Pi.add_apply, add_mul, mul_add]; abel
  · exact linEM_add _ _ _ _ _

theorem s2OutM_smul (z : ℕ) (a : ZMod 2) (Δ : ℕ → Mat18) (k : ℕ) :
    s2OutM z (a • Δ) k = a • s2OutM z Δ k := by
  unfold s2OutM
  split_ifs
  · simp only [Pi.smul_apply, smul_mul_assoc, mul_smul_comm, smul_add]
  · exact linEM_smul _ _ _ _ _

@[expose] def S2 (z : ℕ) : (Fin 128 → ZMod 2) →ₗ[ZMod 2] (Fin (20 * 32) → ZMod 2) where
  toFun δ j := blk2M (s2OutM z (fun m => emb2M (dsOf δ m)) (j / 32)) ⟨(j : ℕ) % 32,
    Nat.mod_lt _ (by norm_num)⟩
  map_add' δ δ' := by
    ext j
    have : (fun m => emb2M (dsOf (δ + δ') m)) =
        (fun m => emb2M (dsOf δ m)) + fun m => emb2M (dsOf δ' m) := by
      ext1 m; rw [dsOf_add, emb2M_add]; rfl
    simp only [this, s2OutM_add, blk2M_add, Pi.add_apply]
  map_smul' a δ := by
    ext j
    have : (fun m => emb2M (dsOf (a • δ) m)) = a • fun m => emb2M (dsOf δ m) := by
      ext1 m; rw [dsOf_smul, emb2M_smul]; rfl
    simp only [this, s2OutM_smul, blk2M_smul, Pi.smul_apply, RingHom.id_apply]

theorem toMat_emb2m {v : ℕ} (hv : v < 2 ^ 128) (m : ℕ) :
    toMat 18 18 (emb2m v m) = emb2M (dsOf (toVec 128 v) m) := by
  rw [emb2m, toMat_emb2Bits]
  congr 1
  ext i
  rw [toVec_split32, dsOf]
  by_cases h : 32 * m + (i : ℕ) < 128
  · rw [dite_eq_left h]; rfl
  · rw [dite_eq_right h, Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by norm_num) (by omega))), bz_false]

theorem toMat_linE {v : ℕ} (hv : v < 2 ^ 128) (z j m : ℕ) :
    toMat 18 18 (linE z j m v) = linEM z j m fun n => emb2M (dsOf (toVec 128 v) n) := by
  unfold linE
  rw [toMat_foldl_bxor, toMat_bmul, toMat_bmul, toMat_emb2m hv]
  unfold linEM vM yProdM eProdM
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
  rw [toMat_bmul, toMat_bmul, toMat_emb2m hv]

theorem toMat_s2Block_mat {v : ℕ} (hv : v < 2 ^ 128) (z k : ℕ) :
    blk2M (s2OutM z (fun n => emb2M (dsOf (toVec 128 v) n)) k) = toVec 32 (s2Block z v k) := by
  rw [s2Block, s2OutM]
  split_ifs with hk
  · rw [toVec_blk2Bits, toMat_bxor, toMat_bmul, toMat_bmul, toMat_bmul, toMat_emb2m hv, tytBits,
      toMat_bmul, toMat_bmul]
    rfl
  · rw [toVec_blk2Bits, toMat_linE hv]

theorem fin640_eq (j : Fin (20 * 32)) :
    j = ⟨32 * ((j : ℕ) / 32) + (j : ℕ) % 32, by omega⟩ := Fin.ext (by simp; omega)

theorem toVec_s2Fb {v : ℕ} (hv : v < 2 ^ 128) (z : ℕ) :
    toVec (20 * 32) (s2Fb z v) = S2 z (toVec 128 v) := by
  ext j
  have hk : (j : ℕ) / 32 < 20 := by omega
  rw [fin640_eq j]
  have := toVec_cat20 (s2Block z v) ⟨(j : ℕ) / 32, hk⟩ ⟨(j : ℕ) % 32, Nat.mod_lt _ (by norm_num)⟩
  rw [s2Fb]
  rw [this]
  simp only [S2, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← toMat_s2Block_mat hv]
  congr 3 <;> simp <;> omega

@[expose] def tgtV (z : ℕ) : Fin (20 * 32) → ZMod 2 :=
  fun j => blk2M (tgtM z ((j : ℕ) / 32)) ⟨(j : ℕ) % 32, Nat.mod_lt _ (by norm_num)⟩

theorem toVec_s2TBlock (z k : ℕ) : toVec 32 (s2TBlock z k) = blk2M (tgtM z k) := by
  rw [s2TBlock, tgtM]
  split_ifs with hk
  · rw [toVec_blk2Bits, toMat_bxor, toMat_bmul, tytBits, toMat_bmul, toMat_bmul]; rfl
  · rw [toVec_blk2Bits, toMat_bxor, toMat_bmul, toMat_bmul, toMat_bmul]; rfl

theorem toVec_s2Target (z : ℕ) : toVec (20 * 32) (s2Target z) = tgtV z := by
  ext j
  have hk : (j : ℕ) / 32 < 20 := by omega
  rw [fin640_eq j]
  have := toVec_cat20 (s2TBlock z) ⟨(j : ℕ) / 32, hk⟩ ⟨(j : ℕ) % 32, Nat.mod_lt _ (by norm_num)⟩
  rw [s2Target, this, toVec_s2TBlock, tgtV]
  congr 3 <;> simp <;> omega

theorem s2Check_spec :
    (∀ z < 2, injCheckWith 128 640 (linBits 128 640 (s2Fb z)) (s2Qcols z) = true ∧
      s2Fb z (s2Sol z) = s2Target z) ∧
    (∀ z, 2 ≤ z → z < 4 → (∀ j < 128, par640 (s2Farkas z &&& s2Fb z (2 ^ j)) = false) ∧
      par640 (s2Farkas z &&& s2Target z) = true) := by
  have h := s2CheckW_eq_true
  simp only [s2CheckW, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  refine ⟨fun z hz => h.1 z hz, fun z hz2 hz4 => ?_⟩
  obtain ⟨hF, hT⟩ := h.2 (z - 2) (by omega)
  rw [show z - 2 + 2 = z by omega] at hF hT
  exact ⟨hF, hT⟩

theorem s2Sol_lt (z : ℕ) : s2Sol z < 2 ^ 128 := by
  unfold s2Sol; split_ifs <;> norm_num

theorem two_pow_lt_128 (j : Fin 128) : 2 ^ (j : ℕ) < 2 ^ 128 :=
  Nat.pow_lt_pow_right (by norm_num) j.isLt

theorem eq_of_S2_eq {z : ℕ} (hz : z < 2) {δ : Fin 128 → ZMod 2}
    (h : S2 z δ = tgtV z) : δ = toVec 128 (s2Sol z) := by
  obtain ⟨hinj, hsol⟩ := s2Check_spec.1 z hz
  have hsolV : S2 z (toVec 128 (s2Sol z)) = tgtV z := by
    rw [← toVec_s2Fb (s2Sol_lt z), hsol, toVec_s2Target]
  have h0 : toMat 640 128 (linBits 128 640 (s2Fb z)) *ᵥ (δ - toVec 128 (s2Sol z)) = 0 := by
    rw [toMat_linBits_mulVec (s2Fb z) (S2 z) (fun j => by
      rw [toVec_s2Fb (two_pow_lt_128 j), toVec_two_pow]), map_sub, h, hsolV]
    exact sub_self _
  exact sub_eq_zero.mp (eq_zero_of_injCheckWith hinj h0)

theorem bz_par640 (a b : ℕ) : bz (par640 (a &&& b)) = toVec 640 a ⬝ᵥ toVec 640 b := by
  rw [par640, bz_xorFold]
  simp only [dotProduct, toVec, Nat.testBit_and, bz_and]

theorem S2_ne_tgtV {z : ℕ} (hz2 : 2 ≤ z) (hz4 : z < 4)
    (δ : Fin 128 → ZMod 2) : S2 z δ ≠ tgtV z := by
  obtain ⟨hF, hT⟩ := s2Check_spec.2 z hz2 hz4
  intro h
  have hbasis : ∀ j : Fin 128, toVec 640 (s2Farkas z) ⬝ᵥ S2 z (Pi.single j 1) = 0 := fun j => by
    have := bz_par640 (s2Farkas z) (s2Fb z (2 ^ (j : ℕ)))
    rw [hF j j.isLt, bz_false] at this
    rw [← toVec_two_pow, ← toVec_s2Fb (two_pow_lt_128 j)]
    exact this.symm
  have hδ : δ = ∑ j : Fin 128, δ j • (Pi.single j 1 : Fin 128 → ZMod 2) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : toVec 640 (s2Farkas z) ⬝ᵥ S2 z δ = 0 := by
    rw [hδ, map_sum, dotProduct_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, dotProduct_smul, hbasis, smul_zero]
  have h2 : toVec 640 (s2Farkas z) ⬝ᵥ tgtV z = 1 := by
    rw [← toVec_s2Target, ← bz_par640, hT, bz_true]
  rw [h] at h1
  rw [h1] at h2
  exact zero_ne_one h2

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
