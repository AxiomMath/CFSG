module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Finset

abbrev FrameVec : Type := Fin 8 → ZMod 2

@[expose] def frameZ : FrameVec := fun _ => 1

@[expose] def frameE (i : Fin 8) : FrameVec := fun j => if j = i then 1 else 0

@[expose] def permVec (σ : Equiv.Perm (Fin 8)) (v : FrameVec) : FrameVec := fun i => v (σ.symm i)

theorem permVec_apply (σ : Equiv.Perm (Fin 8)) (v : FrameVec) (i : Fin 8) :
    permVec σ v i = v (σ.symm i) := rfl

theorem permVec_add (σ : Equiv.Perm (Fin 8)) (v w : FrameVec) :
    permVec σ (v + w) = permVec σ v + permVec σ w := rfl

theorem permVec_mul (σ τ : Equiv.Perm (Fin 8)) (v : FrameVec) :
    permVec (σ * τ) v = permVec σ (permVec τ v) := rfl

theorem permVec_one (v : FrameVec) : permVec 1 v = v := rfl

theorem permVec_inv_permVec (σ : Equiv.Perm (Fin 8)) (v : FrameVec) :
    permVec σ⁻¹ (permVec σ v) = v := by
  rw [← permVec_mul, inv_mul_cancel, permVec_one]

theorem permVec_permVec_inv (σ : Equiv.Perm (Fin 8)) (v : FrameVec) :
    permVec σ (permVec σ⁻¹ v) = v := by
  rw [← permVec_mul, mul_inv_cancel, permVec_one]

theorem permVec_injective (σ : Equiv.Perm (Fin 8)) : Function.Injective (permVec σ) :=
  fun v w h => by rw [← permVec_inv_permVec σ v, h, permVec_inv_permVec]

theorem permVec_frameZ (σ : Equiv.Perm (Fin 8)) : permVec σ frameZ = frameZ := rfl

theorem permVec_frameE (σ : Equiv.Perm (Fin 8)) (i : Fin 8) :
    permVec σ (frameE i) = frameE (σ i) := by
  funext j
  simp only [permVec, frameE, Equiv.symm_apply_eq]

@[expose] def frameDecode (n : ℕ) : FrameVec := fun i => if n.testBit i then 1 else 0

@[expose] def frameEncode (v : FrameVec) : ℕ := ∑ i : Fin 8, (v i).val * 2 ^ (i : ℕ)

theorem frameEncode_frameDecode : ∀ n < 256, frameEncode (frameDecode n) = n := by
  decide +kernel

theorem frameDecode_xor (a b : ℕ) : frameDecode (a ^^^ b) = frameDecode a + frameDecode b := by
  funext i
  simp only [frameDecode, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem frameDecode_surjective (v : FrameVec) : ∃ n < 256, frameDecode n = v := by
  classical
  have hinj : Set.InjOn frameDecode (range 256 : Finset ℕ) := by
    intro a ha b hb hab
    rw [← frameEncode_frameDecode a (mem_range.mp ha), hab,
      frameEncode_frameDecode b (mem_range.mp hb)]
  have huniv : (range 256).image frameDecode = univ := by
    apply eq_univ_of_card
    rw [card_image_of_injOn hinj, card_range, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rfl
  have hv : v ∈ (range 256).image frameDecode := huniv ▸ mem_univ v
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hv
  exact ⟨n, mem_range.mp hn, rfl⟩

theorem frameDecode_frameEncode (v : FrameVec) : frameDecode (frameEncode v) = v := by
  obtain ⟨n, hn, rfl⟩ := frameDecode_surjective v
  rw [frameEncode_frameDecode n hn]

theorem frameEncode_lt (v : FrameVec) : frameEncode v < 256 := by
  obtain ⟨n, hn, rfl⟩ := frameDecode_surjective v
  rwa [frameEncode_frameDecode n hn]

theorem frameEncode_injective : Function.Injective frameEncode := fun v w h => by
  rw [← frameDecode_frameEncode v, h, frameDecode_frameEncode]

theorem frameEncode_add (v w : FrameVec) :
    frameEncode (v + w) = frameEncode v ^^^ frameEncode w := by
  have hlt : frameEncode v ^^^ frameEncode w < 256 :=
    Nat.xor_lt_two_pow (n := 8) (frameEncode_lt v) (frameEncode_lt w)
  rw [← frameEncode_frameDecode _ hlt, frameDecode_xor, frameDecode_frameEncode,
    frameDecode_frameEncode]

theorem frameDecode_255 : frameDecode 255 = frameZ := by
  funext i
  revert i
  decide

theorem frameZ_ne_zero : frameZ ≠ 0 := fun h => by
  have := congrFun h 0
  exact absurd this (by decide)

theorem frameE_eq_frameDecode (i : Fin 8) : frameE i = frameDecode (2 ^ (i : ℕ)) := by
  funext j
  revert i j
  decide

theorem frameEncode_frameZ : frameEncode frameZ = 255 := by
  rw [← frameDecode_255, frameEncode_frameDecode 255 (by decide)]

theorem card_filter_frameVec (P : FrameVec → Prop) [DecidablePred P] :
    (univ.filter P).card = ((range 256).filter fun n => P (frameDecode n)).card := by
  symm
  apply card_nbij' frameDecode frameEncode
  · intro n hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn
    simp [hn.2]
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    exact ⟨frameEncode_lt v, by rwa [frameDecode_frameEncode]⟩
  · intro n hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn
    exact frameEncode_frameDecode n hn.1
  · intro v _
    exact frameDecode_frameEncode v

theorem smul_zero_of_hadd {N M : Type*} [Group N] [AddCommGroup M] [MulAction N M]
    (hadd : ∀ (n : N) (x y : M), n • (x + y) = n • x + n • y) (n : N) : n • (0 : M) = 0 := by
  have h := hadd n 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

@[expose] def framePop (n : ℕ) : ℕ :=
  (n &&& 1) + ((n >>> 1) &&& 1) + ((n >>> 2) &&& 1) + ((n >>> 3) &&& 1) +
    ((n >>> 4) &&& 1) + ((n >>> 5) &&& 1) + ((n >>> 6) &&& 1) + ((n >>> 7) &&& 1)

@[expose] def frameIsPlane (n : ℕ) : Bool :=
  n == 15 || n == 51 || n == 60 || n == 85 || n == 90 || n == 102 || n == 105 || n == 150 ||
    n == 153 || n == 165 || n == 170 || n == 195 || n == 204 || n == 240

@[expose] def frameClass (n : ℕ) : ℕ :=
  if framePop n < 4 then framePop n
  else if framePop n = 4 then (if frameIsPlane n then 4 else 5) else framePop n + 1

@[expose] def frameCls (v : FrameVec) : ℕ := frameClass (frameEncode v)

theorem frameCls_frameDecode {n : ℕ} (hn : n < 256) : frameCls (frameDecode n) = frameClass n := by
  rw [frameCls, frameEncode_frameDecode n hn]

theorem frameClass_le : ∀ n < 256, frameClass n ≤ 9 := by decide +kernel

theorem frameClass_eq_nine : ∀ n < 256, frameClass n = 9 ↔ n = 255 := by decide +kernel

theorem frameClass_eq_zero : ∀ n < 256, frameClass n = 0 ↔ n = 0 := by decide +kernel

theorem frameCls_le (v : FrameVec) : frameCls v ≤ 9 := frameClass_le _ (frameEncode_lt v)

theorem frameCls_eq_nine_iff (v : FrameVec) : frameCls v = 9 ↔ v = frameZ := by
  rw [frameCls, frameClass_eq_nine _ (frameEncode_lt v), ← frameEncode_frameZ]
  exact frameEncode_injective.eq_iff

theorem frameCls_eq_zero_iff (v : FrameVec) : frameCls v = 0 ↔ v = 0 := by
  have h0 : frameEncode 0 = 0 := by decide
  rw [frameCls, frameClass_eq_zero _ (frameEncode_lt v), ← h0]
  exact frameEncode_injective.eq_iff

@[expose] def frameBlocks : Finset (Finset (Fin 8)) :=
  {{0, 1, 2, 3}, {0, 1, 4, 5}, {0, 1, 6, 7}, {0, 2, 4, 6}, {0, 2, 5, 7}, {0, 3, 4, 7},
    {0, 3, 5, 6}, {1, 2, 4, 7}, {1, 2, 5, 6}, {1, 3, 4, 6}, {1, 3, 5, 7}, {2, 3, 4, 5},
    {2, 3, 6, 7}, {4, 5, 6, 7}}

@[expose] def blockVec (B : Finset (Fin 8)) : FrameVec := fun i => if i ∈ B then 1 else 0

theorem frameClass_eq_four : ∀ n < 256,
    frameClass n = 4 ↔ ∃ B ∈ frameBlocks, frameDecode n = blockVec B := by
  decide +kernel

theorem frameCls_eq_four_iff (v : FrameVec) :
    frameCls v = 4 ↔ ∃ B ∈ frameBlocks, v = blockVec B := by
  rw [frameCls, frameClass_eq_four _ (frameEncode_lt v), frameDecode_frameEncode]

@[expose] def frameAut : Set (Equiv.Perm (Fin 8)) :=
  {σ | ∀ B ∈ frameBlocks, B.map σ.toEmbedding ∈ frameBlocks}

@[expose] def frameSinger : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 4, 6, 3, 1, 7, 5]
  invFun := ![0, 5, 1, 4, 2, 7, 3, 6]
  left_inv := by decide
  right_inv := by decide

@[expose] def frameFlip : Equiv.Perm (Fin 8) where
  toFun := ![1, 0, 3, 2, 4, 5, 6, 7]
  invFun := ![1, 0, 3, 2, 4, 5, 6, 7]
  left_inv := by decide
  right_inv := by decide

@[expose] def frameGens : Set (Equiv.Perm (Fin 8)) := {frameSinger, frameFlip}

@[expose] def frameGen (k : Fin 2) : Equiv.Perm (Fin 8) := if k = 0 then frameSinger else frameFlip

@[expose] def frameWord (w : List (Fin 2)) : Equiv.Perm (Fin 8) := (w.map frameGen).prod

theorem frameGen_mem (k : Fin 2) : frameGen k ∈ frameGens := by
  unfold frameGen frameGens
  split_ifs
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

theorem frameWord_mem_closure (w : List (Fin 2)) : frameWord w ∈ Subgroup.closure frameGens := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons k w ih =>
    rw [frameWord, List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (frameGen_mem k)) ih

theorem frameGens_subset_frameAut : frameGens ⊆ frameAut := by
  rintro σ (rfl | rfl) <;> change ∀ B ∈ frameBlocks, _ <;> decide +kernel

@[expose] def frameRep (c : ℕ) : ℕ :=
  if c = 1 then 1 else if c = 2 then 3 else if c = 3 then 7 else if c = 5 then 23
  else if c = 6 then 31 else if c = 7 then 63 else 127

@[expose] def frameOrbitWords : List (List (Fin 2)) := [
    [], [], [1], [], [0, 1], [0], [1, 0, 0, 0], [], [1, 0, 1], [0, 0, 0], [1, 0], [1],
    [0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [], [0, 0, 1], [0, 0],
    [1, 0, 0], [0, 1, 0, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0], [0], [1, 0, 0], [], [0, 0, 1, 0, 0, 0],
    [0, 0], [1, 0], [1], [0, 1, 0, 0], [0], [1, 0], [], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 1],
    [1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1], [0, 0, 0, 1, 0, 1],
    [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0],
    [], [1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [],
    [1, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0], [], [0, 1, 0, 1], [0, 0, 0, 0], [1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1], [0, 1, 0], [0, 1], [1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0],
    [0, 0, 0], [1, 0, 1], [0, 1, 0, 1, 0, 0, 0, 1], [0, 1, 0], [0, 1], [1, 0, 1],
    [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1],
    [0, 1, 0, 0, 1, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0], [], [1, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0], [0, 0], [], [0, 1, 0, 0, 1, 0, 0, 0], [0, 1, 0], [0], [1, 0], [0],
    [0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1],
    [1, 0, 1, 0, 1, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1], [], [0, 1, 0, 0, 0, 0, 0],
    [0, 1, 0, 1, 0, 0, 0], [], [0, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1],
    [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
    [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0], [],
    [0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0],
    [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 1], [1, 0, 0, 1],
    [0, 1, 0, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0], [],
    [0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0], [], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 0],
    [0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [], [1, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0],
    [0, 0, 0, 1], [], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
    [0, 1, 0, 1, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1],
    [0, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0],
    [1, 0, 1, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1],
    [1, 0, 1, 0, 0, 0], [0, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0],
    [1, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 0, 0],
    [1, 0, 0, 0, 0], [], [0, 1, 0, 1], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 1], [0, 0, 0], [0, 0, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 1, 0, 0, 0], [], [1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 1], [1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0, 0],
    [0, 1, 0, 1], [0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0], [0, 0], [1, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0, 0], [0, 1, 0],
    [0, 0], [1, 0, 0], [0], [0, 1, 0, 1, 0, 1], [0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0],
    [1, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0], [1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0],
    [0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0], [], [0, 1, 0, 0, 0, 1, 0, 0],
    [1, 0, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0],
    [1, 0, 0, 0], [1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0], [0, 1, 0, 0],
    [0, 0], [1, 0, 0], []]

theorem frame_orbit_words : ∀ n < 256, frameClass n ≠ 0 → frameClass n ≠ 4 → frameClass n ≠ 9 →
    frameDecode n =
      permVec (frameWord (frameOrbitWords.getD n [])) (frameDecode (frameRep (frameClass n))) := by
  decide +kernel

theorem mem_of_frameCls_eq {Y : Set FrameVec}
    (hY : ∀ σ ∈ Subgroup.closure frameGens, ∀ v ∈ Y, permVec σ v ∈ Y) {u v : FrameVec}
    (huv : frameCls u = frameCls v) (h0 : frameCls u ≠ 0) (h4 : frameCls u ≠ 4)
    (h9 : frameCls u ≠ 9) (hu : u ∈ Y) : v ∈ Y := by
  have key : ∀ x : FrameVec, frameCls x = frameCls u → x = permVec
      (frameWord (frameOrbitWords.getD (frameEncode x) []))
      (frameDecode (frameRep (frameCls u))) := by
    intro x hx
    have hx' : frameClass (frameEncode x) = frameCls u := hx
    have h := frame_orbit_words (frameEncode x) (frameEncode_lt x) (hx' ▸ h0) (hx' ▸ h4)
      (hx' ▸ h9)
    rwa [frameDecode_frameEncode, hx'] at h
  set r := frameDecode (frameRep (frameCls u))
  set σ := frameWord (frameOrbitWords.getD (frameEncode u) [])
  have hr : r ∈ Y := by
    have h := hY σ⁻¹ (Subgroup.inv_mem _ (frameWord_mem_closure _)) u hu
    rwa [key u rfl, permVec_inv_permVec] at h
  rw [key v huv.symm]
  exact hY _ (frameWord_mem_closure _) r hr

@[expose] def frameRealized (N : Type*) [Group N] [MulAction N FrameVec] :
    Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∃ n : N, ∀ v : FrameVec, n • v = permVec σ v}
  mul_mem' := by
    rintro σ τ ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n * m, fun v => by rw [mul_smul, hm, hn, permVec_mul]⟩
  one_mem' := ⟨1, fun v => by rw [one_smul, permVec_one]⟩
  inv_mem' := by
    rintro σ ⟨n, hn⟩
    refine ⟨n⁻¹, fun v => ?_⟩
    calc n⁻¹ • v = n⁻¹ • (n • permVec σ⁻¹ v) := by rw [hn, permVec_permVec_inv]
      _ = permVec σ⁻¹ v := inv_smul_smul n _

theorem closure_le_frameRealized {N : Type*} [Group N] [MulAction N FrameVec]
    (hgen : ∀ σ ∈ frameGens, ∃ n : N, ∀ v : FrameVec, n • v = permVec σ v) :
    Subgroup.closure frameGens ≤ frameRealized N :=
  (Subgroup.closure_le _).2 hgen

end CFSG.EvenSmallLie.OmegaEight
