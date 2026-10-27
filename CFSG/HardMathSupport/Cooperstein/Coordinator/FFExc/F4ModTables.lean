module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitTables

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open Matrix

@[expose] def bvec (m : ℕ) : Ix → ZMod 2 := fun j => if m.testBit j.val then 1 else 0

@[expose] def Nact (k : ℕ) (v : Ix → ZMod 2) : Ix → ZMod 2 :=
  if graphRoot (e6root k) = e6root k then Em2 k *ᵥ v
  else Em2 k *ᵥ v + Em2 (gamK k) *ᵥ v + Em2 k *ᵥ (Em2 (gamK k) *ᵥ v)

@[expose] def Nrow (k : ℕ) (w : Ix → ZMod 2) : Ix → ZMod 2 :=
  if graphRoot (e6root k) = e6root k then w ᵥ* Em2 k
  else w ᵥ* Em2 k + w ᵥ* Em2 (gamK k) + (w ᵥ* Em2 k) ᵥ* Em2 (gamK k)

theorem Gm2_sub_one_mulVec (k : ℕ) (v : Ix → ZMod 2) : (Gm2 k - 1) *ᵥ v = Nact k v := by
  unfold Gm2 Nact
  by_cases h : graphRoot (e6root k) = e6root k
  · rw [ite_eq_left h, ite_eq_left h, show 1 + Em2 k - 1 = Em2 k by abel]
  · rw [ite_eq_right h, ite_eq_right h]
    have : (1 + Em2 k) * (1 + Em2 (gamK k)) - 1 =
        Em2 k + Em2 (gamK k) + Em2 k * Em2 (gamK k) := by noncomm_ring
    rw [this, add_mulVec, add_mulVec, ← mulVec_mulVec]

theorem vecMul_Gm2_sub_one (k : ℕ) (w : Ix → ZMod 2) : w ᵥ* (Gm2 k - 1) = Nrow k w := by
  unfold Gm2 Nrow
  by_cases h : graphRoot (e6root k) = e6root k
  · rw [ite_eq_left h, ite_eq_left h, show 1 + Em2 k - 1 = Em2 k by abel]
  · rw [ite_eq_right h, ite_eq_right h]
    have : (1 + Em2 k) * (1 + Em2 (gamK k)) - 1 =
        Em2 k + Em2 (gamK k) + Em2 k * Em2 (gamK k) := by noncomm_ring
    rw [this, vecMul_add, vecMul_add, ← vecMul_vecMul]

@[expose] def fixCert : List (ℕ × List (ℕ × ℕ)) := [(2, [(0, 1)]), (4, [(2, 2)]), (8, [(3, 4)]), (16, [(1, 8)]), (32, [(2, 8)]), (64, [(1, 32)]), (128, [(0, 32)]), (256, [(3, 64)]), (512, [(0, 64)]), (1024, [(2, 256)]), (2048, [(0, 256)]), (32768, [(0, 4096)]), (65536, [(2, 8192)]), (131072, [(0, 65536)]), (262144, [(3, 65536)]), (524288, [(0, 262144)]), (1048576, [(1, 262144)]), (2097152, [(0, 1048576)]), (4194304, [(2, 524288)]), (8388608, [(1, 4194304)]), (16777216, [(3, 8388608)]), (33554432, [(2, 16777216)]), (67108864, [(0, 33554432)]), (12288, [(0, 1024), (0, 4096)]), (24576, [(2, 2048), (2, 8192)])]

theorem fixCert_check : ∀ p ∈ fixCert,
    (p.2.map fun q => Nrow q.1 (bvec q.2)).sum = bvec p.1 := by
  decide +kernel

@[expose] def genChain : List (ℕ × ℕ × ℕ) := [(1, 0, 0), (2, 0, 6), (4, 0, 17), (8, 0, 27), (16, 0, 37), (32, 0, 38), (64, 0, 46), (128, 0, 47), (256, 0, 53), (512, 0, 54), (1024, 0, 59), (2048, 0, 60), (67133440, 0, 64), (65536, 0, 67), (262144, 0, 69), (1048576, 0, 71), (33574912, 1, 59), (32768, 1, 64), (131072, 1, 67), (524288, 1, 69), (2097152, 1, 71), (16789504, 2, 53), (4194304, 2, 69), (8388608, 2, 71), (8400896, 3, 46), (2117632, 5, 37)]

theorem genChain_check : ∀ i < genChain.length, 0 < i →
    bvec (genChain.getD i (0, 0, 0)).1 =
      Nact (genChain.getD i (0, 0, 0)).2.2 (bvec (genChain.getD (genChain.getD i (0, 0, 0)).2.1
        (0, 0, 0)).1) ∧ (genChain.getD i (0, 0, 0)).2.1 < i ∧ (genChain.getD i (0, 0, 0)).2.2 < 72 := by
  decide +kernel

theorem genChain_zero : (genChain.getD 0 (0, 0, 0)).1 = 1 := by decide +kernel

@[expose] def genCert : List (ℕ × List ℕ) := [(1, [0]), (2, [1]), (4, [2]), (8, [3]), (16, [4]), (32, [5]), (64, [6]), (128, [7]), (256, [8]), (512, [9]), (1024, [10]), (2048, [11]), (32768, [17]), (65536, [13]), (131072, [18]), (262144, [14]), (524288, [19]), (1048576, [15]), (2097152, [20]), (4194304, [22]), (8388608, [23]), (16777216, [21, 23, 24]), (33554432, [16, 20, 25]), (67108864, [12, 20, 23, 24, 25]), (12288, [23, 24]), (24576, [20, 23, 24, 25])]

theorem genCert_check : ∀ p ∈ genCert,
    (p.2.map fun i => bvec (genChain.getD i (0, 0, 0)).1).sum = bvec p.1 ∧
      ∀ i ∈ p.2, i < genChain.length := by
  decide +kernel

theorem fixCert_rows : ∀ p ∈ fixCert, ∀ q ∈ p.2, q.1 < 4 := by decide +kernel

theorem fixCert_single : ∀ i : Ix, ¬ (i.val = 0 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14) →
    ∃ p ∈ fixCert, p.1 = 1 <<< i.val := by decide +kernel

theorem fixCert_mem_12_13 : ∃ p ∈ fixCert, p.1 = 12288 := by decide +kernel

theorem fixCert_mem_13_14 : ∃ p ∈ fixCert, p.1 = 24576 := by decide +kernel

theorem bvec_single : ∀ i : Ix, bvec (1 <<< i.val) = Pi.single i 1 := by decide +kernel

theorem bvec_12_13 : bvec 12288 = Pi.single (⟨12, by decide⟩ : Ix) 1 + Pi.single (⟨13, by decide⟩ : Ix) 1 := by
  decide +kernel

theorem bvec_13_14 : bvec 24576 = Pi.single (⟨13, by decide⟩ : Ix) 1 + Pi.single (⟨14, by decide⟩ : Ix) 1 := by
  decide +kernel

theorem genCert_single : ∀ i : Ix, ¬ (i.val = 12 ∨ i.val = 13 ∨ i.val = 14) →
    ∃ p ∈ genCert, p.1 = 1 <<< i.val := by decide +kernel

theorem genCert_mem_12_13 : ∃ p ∈ genCert, p.1 = 12288 := by decide +kernel

theorem genCert_mem_13_14 : ∃ p ∈ genCert, p.1 = 24576 := by decide +kernel

section DotK

variable {K : Type*} [Field K] [CharP K 2]

@[expose] def dotK (v : Ix → ZMod 2) (x : Ix → K) : K := (cast2 K ∘ v) ⬝ᵥ x

theorem dotK_add (v w : Ix → ZMod 2) (x : Ix → K) : dotK (v + w) x = dotK v x + dotK w x := by
  unfold dotK
  have : cast2 K ∘ (v + w) = cast2 K ∘ v + cast2 K ∘ w := funext fun j => map_add _ _ _
  rw [this, add_dotProduct]

theorem dotK_zero (x : Ix → K) : dotK 0 x = 0 := by
  unfold dotK
  have : cast2 K ∘ (0 : Ix → ZMod 2) = 0 := funext fun j => map_zero _
  rw [this, zero_dotProduct]

@[expose] def dotKHom (x : Ix → K) : (Ix → ZMod 2) →+ K where
  toFun v := dotK v x
  map_zero' := dotK_zero x
  map_add' v w := dotK_add v w x

theorem dotK_list_sum (L : List (Ix → ZMod 2)) (x : Ix → K) :
    dotK L.sum x = (L.map fun v => dotK v x).sum :=
  map_list_sum (dotKHom x) L

theorem dotK_single (i : Ix) (x : Ix → K) : dotK (Pi.single i 1) x = x i := by
  unfold dotK
  have : cast2 K ∘ (Pi.single i 1 : Ix → ZMod 2) = Pi.single i 1 := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [this, single_dotProduct, one_mul]

theorem dotK_Nrow (k : ℕ) (w : Ix → ZMod 2) (x : Ix → K)
    (hx : (Gm2 k - 1).map (cast2 K) *ᵥ x = 0) : dotK (Nrow k w) x = 0 := by
  unfold dotK
  rw [← vecMul_Gm2_sub_one, ← map_vecMul', ← dotProduct_mulVec, hx, dotProduct_zero]

end DotK

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
