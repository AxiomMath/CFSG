
module

public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

@[expose] public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight

open QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal

section Field

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_eq_one_of_card_eq_two (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  classical
  by_contra h
  push Not at h
  have : Fintype K := Fintype.ofFinite K
  have h3 : 3 ≤ Fintype.card K := by
    have hsub : ({0, 1, c} : Finset K).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h.1.symm, zero_ne_one]),
        Finset.card_pair (Ne.symm h.2)]
    rw [← hsub]
    exact Finset.card_le_univ _
  rw [← Nat.card_eq_fintype_card, hK] at h3
  omega

theorem charP_two_of_card_eq_two (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])

theorem one_add_one_eq_zero (hK : Nat.card K = 2) : (1 : K) + 1 = 0 := by
  have := charP_two_of_card_eq_two hK
  rw [one_add_one_eq_two]
  exact CharTwo.two_eq_zero

@[expose] def ind (K : Type) [Field K] (b : Bool) : K := if b then 1 else 0

omit [Finite K] in
theorem ind_and (a b : Bool) : ind K (a && b) = ind K a * ind K b := by
  cases a <;> cases b <;> simp [ind]

theorem ind_xor (hK : Nat.card K = 2) (a b : Bool) :
    ind K (a ^^ b) = ind K a + ind K b := by
  cases a <;> cases b <;> simp [ind, one_add_one_eq_zero hK]

omit [Finite K] in
theorem ind_injective : Function.Injective (ind K) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ind]

end Field

@[expose] def cidx : Fin 4 ⊕ Fin 4 → ℕ
  | .inl i => i
  | .inr i => i + 4

@[expose] def vecK (K : Type) [Field K] (v : ℕ) : Fin 4 ⊕ Fin 4 → K :=
  fun c => ind K (v.testBit (cidx c))

section Vectors

variable {K : Type} [Field K]

theorem vecK_zero : vecK K 0 = 0 := by
  funext c
  simp [vecK, ind]

theorem ind_smul_vecK (b : Bool) (v : ℕ) : ind K b • vecK K v = vecK K (if b then v else 0) := by
  cases b <;> simp [ind, vecK_zero]

variable [Finite K] (hK : Nat.card K = 2)
include hK

theorem vecK_xor (a b : ℕ) : vecK K (a ^^^ b) = vecK K a + vecK K b := by
  funext c
  simp only [vecK, Pi.add_apply, Nat.testBit_xor, ind_xor hK]

theorem quadPlus_vecK (v : ℕ) : quadPlus 4 K (vecK K v) = ind K (qNat v) := by
  rw [quadPlus_apply, Fin.sum_univ_four]
  simp only [vecK, cidx, ← ind_and, qNat, ind_xor hK]
  rfl

theorem polar_vecK (v w : ℕ) :
    polar (quadPlus 4 K) (vecK K v) (vecK K w) = ind K (bNat v w) := by
  rw [polar_quadPlus, Fin.sum_univ_four]
  simp only [vecK, cidx, ← ind_and, bNat, ind_xor hK]
  rfl

theorem eichler_vecK {a b : ℕ} (ha : qNat a = false) (hab : bNat a b = false) (x : ℕ) :
    eichler (quadPlus 4 K) (vecK K a) (vecK K b) (vecK K x) = vecK K (eichNat a b x) := by
  have hu : quadPlus 4 K (vecK K a) = 0 := by rw [quadPlus_vecK hK, ha]; rfl
  have hw : polar (quadPlus 4 K) (vecK K a) (vecK K b) = 0 := by rw [polar_vecK hK, hab]; rfl
  have := charP_two_of_card_eq_two hK
  rw [eichler_apply hu hw, polar_vecK hK, polar_vecK hK, quadPlus_vecK hK, ← ind_and,
    CharTwo.sub_eq_add, add_smul, ind_smul_vecK, ind_smul_vecK, ind_smul_vecK, eichNat,
    vecK_xor hK, vecK_xor hK, vecK_xor hK]
  abel

omit [Finite K] hK in
theorem vecK_injective {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : vecK K a = vecK K b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 8
  · obtain ⟨c, rfl⟩ : ∃ c, cidx c = k := by
      by_cases h4 : k < 4
      · exact ⟨.inl ⟨k, h4⟩, rfl⟩
      · exact ⟨.inr ⟨k - 4, by omega⟩, by simp only [cidx]; omega⟩
    exact ind_injective (congrFun h c)
  · have hle : 256 ≤ 2 ^ k := by
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem vecK_bijective : Function.Bijective fun n : Fin 256 => vecK K n := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun n m h => Fin.ext (vecK_injective n.2 m.2 h), ?_⟩
  rw [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    ← Nat.card_eq_fintype_card, hK]
  rfl

theorem exists_vecK (v : Fin 4 ⊕ Fin 4 → K) : ∃ n < 256, vecK K n = v := by
  obtain ⟨n, hn⟩ := (vecK_bijective hK).2 v
  exact ⟨n, n.2, hn⟩

end Vectors

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

abbrev NS (K : Type) [Field K] : Type := {v : Fin 4 ⊕ Fin 4 → K // quadPlus 4 K v = 1}

theorem qNat_of_quadPlus {n : ℕ} (hv : quadPlus 4 K (vecK K n) = 1) : qNat n = true := by
  rw [quadPlus_vecK hK] at hv
  by_contra h
  simp [ind, h] at hv

omit [Finite K] hK in
theorem quadPlus_elementary (g : orthElementaryGroup (quadPlus 4 K)) (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K ((g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v) = quadPlus 4 K v :=
  map_of_mem (orthElementaryGroup_le _ g.2) v

omit [Finite K] hK in
@[expose] def nsPerm (g : orthElementaryGroup (quadPlus 4 K)) : Equiv.Perm (NS K) :=
  Equiv.Perm.subtypePerm (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).toEquiv
    fun v => by rw [LinearEquiv.coe_toEquiv, quadPlus_elementary]

end Action

theorem genArrs_getElem! {i : ℕ} (hi : i < 8) : genArrs[i]! = rootArr (rootPairs.getD i []) := by
  have hlen : rootPairs.length = 8 := rfl
  rw [genArrs, getElem!_pos _ i (by simp [hlen]; omega),
    Array.getElem_append_left (by simp [hlen]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]

theorem rootArr_getElem! (p : List (ℕ × ℕ)) {j : ℕ} (hj : j < 120) :
    (rootArr p)[j]! = nsIdx[eichNat (p.getD 0 (0, 0)).1 (p.getD 0 (0, 0)).2 nsArr[j]!]! := by
  rw [rootArr, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ (by omega)]
  simp only [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, mul_zero, zero_add]

@[expose] def pair0 (i : ℕ) : ℕ × ℕ := (rootPairs.getD i []).getD 0 (0, 0)

theorem pair0_ok {i : ℕ} (hi : i < 8) : qNat (pair0 i).1 = false ∧
    bNat (pair0 i).1 (pair0 i).2 = false ∧ (pair0 i).1 < 256 ∧ (pair0 i).2 < 256 := by
  interval_cases i <;> decide

theorem eichNat_lt {a b x : ℕ} (ha : a < 256) (hb : b < 256) (hx : x < 256) :
    eichNat a b x < 256 := by
  have h0 : (0 : ℕ) < 2 ^ 8 := by norm_num
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num] at ha hb hx ⊢
  unfold eichNat
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx ?_) ?_) ?_ <;>
    split_ifs <;> assumption

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

omit [Finite K] hK in
@[expose] def eichGen (K : Type) [Field K] (i : ℕ) : orthElementaryGroup (quadPlus 4 K) :=
  ⟨eichler (quadPlus 4 K) (vecK K (pair0 i).1) (vecK K (pair0 i).2),
    eichler_mem_elementaryGroup _ _ _⟩

theorem card_elementaryGroup_four : Nat.card (orthElementaryGroup (quadPlus 4 K)) = 174182400 := by
  have := charP_two_of_card_eq_two hK
  have h := CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadPlus (K := K) (n := 4) le_rfl
  rw [hK] at h
  have e : ((2 : ℤ) ^ (4 * (4 - 1)) * (2 ^ 4 - 1) *
      ∏ i ∈ Finset.Icc 1 (4 - 1), ((2 : ℤ) ^ (2 * i) - 1)) = 174182400 := by
    decide
  have h' : (Nat.card (elementaryGroup (quadPlus 4 K)) : ℤ) = 174182400 := by
    push_cast at h
    rw [h, ← e]
    norm_num
  exact_mod_cast h'

theorem finite_elementaryGroup_four : Finite (orthElementaryGroup (quadPlus 4 K)) :=
  Nat.finite_of_card_ne_zero (by rw [card_elementaryGroup_four hK]; norm_num)

end Action

end CFSG.EvenSmallLie.OmegaEight
