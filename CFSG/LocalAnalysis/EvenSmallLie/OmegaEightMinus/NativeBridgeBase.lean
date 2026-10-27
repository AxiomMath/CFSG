
module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridgeBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData

@[expose] public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail (quadTail minusTailForm quadTail_apply
  polar_quadTail minusTailForm_apply minusTailIsometry)
open CFSG.EvenSmallLie.OmegaEight (ind ind_and ind_xor ind_injective charP_two_of_card_eq_two
  one_add_one_eq_zero)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry (elementaryIsometryEquiv)

abbrev qM (K : Type) [Field K] : QuadraticForm K ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) :=
  quadTail 3 (minusTailForm K 1 1)

@[expose] def cidx : Fin 3 ⊕ Fin 3 → ℕ
  | .inl i => i
  | .inr i => i + 3

@[expose] def vecK (K : Type) [Field K] (v : ℕ) : (Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K) :=
  (fun c => ind K (v.testBit (cidx c)), fun i => ind K (v.testBit (i + 6)))

section Vectors

variable {K : Type} [Field K]

theorem vecK_zero : vecK K 0 = 0 := by
  refine Prod.ext (funext fun c => ?_) (funext fun i => ?_) <;> simp [vecK, ind]

theorem ind_smul_vecK (b : Bool) (v : ℕ) : ind K b • vecK K v = vecK K (if b then v else 0) := by
  cases b <;> simp [ind, vecK_zero]

theorem ind_sq (b : Bool) : ind K b ^ 2 = ind K b := by
  cases b <;> simp [ind]

variable [Finite K] (hK : Nat.card K = 2)
include hK

theorem vecK_xor (a b : ℕ) : vecK K (a ^^^ b) = vecK K a + vecK K b := by
  refine Prod.ext (funext fun c => ?_) (funext fun i => ?_) <;>
    simp only [vecK, Prod.fst_add, Prod.snd_add, Pi.add_apply, Nat.testBit_xor, ind_xor hK]

theorem quad_vecK (v : ℕ) : qM K (vecK K v) = ind K (qNat v) := by
  rw [quadTail_apply, quadPlus_apply, Fin.sum_univ_three, minusTailForm_apply]
  simp only [vecK, cidx, ind_sq, one_mul, ← ind_and, qNat, ind_xor hK]
  rfl

theorem polar_minusTail (a b : Fin 2 → K) :
    polar (minusTailForm K 1 1) a b = a 0 * b 1 + b 0 * a 1 := by
  have := charP_two_of_card_eq_two hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [polar, minusTailForm_apply, minusTailForm_apply, minusTailForm_apply]
  simp only [Pi.add_apply]
  linear_combination (a 0 * b 0 + a 1 * b 1) * h2

theorem polar_vecK (v w : ℕ) : polar (qM K) (vecK K v) (vecK K w) = ind K (bNat v w) := by
  rw [polar_quadTail, polar_quadPlus, Fin.sum_univ_three, polar_minusTail hK]
  simp only [vecK, cidx, ← ind_and, bNat, ind_xor hK]
  rfl

theorem eichler_vecK {a b : ℕ} (ha : qNat a = false) (hab : bNat a b = false) (x : ℕ) :
    eichler (qM K) (vecK K a) (vecK K b) (vecK K x) = vecK K (eichNat a b x) := by
  have hu : qM K (vecK K a) = 0 := by rw [quad_vecK hK, ha]; rfl
  have hw : polar (qM K) (vecK K a) (vecK K b) = 0 := by rw [polar_vecK hK, hab]; rfl
  have := charP_two_of_card_eq_two hK
  rw [eichler_apply hu hw, polar_vecK hK, polar_vecK hK, quad_vecK hK, ← ind_and,
    CharTwo.sub_eq_add, add_smul, ind_smul_vecK, ind_smul_vecK, ind_smul_vecK, eichNat,
    vecK_xor hK, vecK_xor hK, vecK_xor hK]
  abel

omit [Finite K] hK in
theorem vecK_injective {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : vecK K a = vecK K b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 8
  · by_cases h6 : k < 6
    · obtain ⟨c, rfl⟩ : ∃ c, cidx c = k := by
        by_cases h3 : k < 3
        · exact ⟨.inl ⟨k, h3⟩, rfl⟩
        · exact ⟨.inr ⟨k - 3, by omega⟩, by simp only [cidx]; omega⟩
      exact ind_injective (congrFun (congrArg Prod.fst h) c)
    · have e := ind_injective (congrFun (congrArg Prod.snd h) ⟨k - 6, by omega⟩)
      simp only [Nat.sub_add_cancel (show 6 ≤ k by omega)] at e
      exact e
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
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card, hK]
  rfl

theorem exists_vecK (v : (Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) : ∃ n < 256, vecK K n = v := by
  obtain ⟨n, hn⟩ := (vecK_bijective hK).2 v
  exact ⟨n, n.2, hn⟩

end Vectors

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

abbrev NS (K : Type) [Field K] : Type := {v : (Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K) // qM K v = 1}

theorem qNat_of_quad {n : ℕ} (hv : qM K (vecK K n) = 1) : qNat n = true := by
  rw [quad_vecK hK] at hv
  by_contra h
  simp [ind, h] at hv

omit [Finite K] hK in
theorem quad_elementary (g : orthElementaryGroup (qM K))
    (v : (Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) :
    qM K ((g : ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] _) v) = qM K v :=
  map_of_mem (orthElementaryGroup_le _ g.2) v

omit [Finite K] hK in
@[expose] def nsPerm (g : orthElementaryGroup (qM K)) : Equiv.Perm (NS K) :=
  Equiv.Perm.subtypePerm (g : ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] _).toEquiv
    fun v => by rw [LinearEquiv.coe_toEquiv, quad_elementary]

end Action

theorem genArrs_getElem! {i : ℕ} (hi : i < 10) : genArrs[i]! = eichArr (gPairs.getD i (0, 0)) := by
  have hlen : gPairs.length = 10 := rfl
  rw [genArrs, getElem!_pos _ i (by simp [hlen]; omega),
    Array.getElem_append_left (by simp [hlen]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]

theorem eichArr_getElem! (p : ℕ × ℕ) {j : ℕ} (hj : j < 136) :
    (eichArr p)[j]! = nsIdx[eichNat p.1 p.2 nsArr[j]!]! := by
  rw [eichArr, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ hj]

theorem pair_ok {i : ℕ} (hi : i < 10) : qNat (gPairs.getD i (0, 0)).1 = false ∧
    bNat (gPairs.getD i (0, 0)).1 (gPairs.getD i (0, 0)).2 = false ∧
    (gPairs.getD i (0, 0)).1 < 256 ∧ (gPairs.getD i (0, 0)).2 < 256 := by
  interval_cases i <;> decide

theorem eichNat_lt {a b x : ℕ} (ha : a < 256) (hb : b < 256) (hx : x < 256) :
    eichNat a b x < 256 := by
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num] at ha hb hx ⊢
  unfold eichNat
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx ?_) ?_) ?_ <;>
    split_ifs <;> first | assumption | exact Nat.two_pow_pos 8

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

omit [Finite K] hK in
@[expose] def eichGen (K : Type) [Field K] (i : ℕ) : orthElementaryGroup (qM K) :=
  ⟨eichler (qM K) (vecK K (gPairs.getD i (0, 0)).1) (vecK K (gPairs.getD i (0, 0)).2),
    eichler_mem_elementaryGroup _ _ _⟩

theorem card_elementaryGroup_qM : Nat.card (orthElementaryGroup (qM K)) = 197406720 := by
  have := charP_two_of_card_eq_two hK
  have hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := by
    intro s
    rcases OmegaEight.eq_zero_or_eq_one_of_card_eq_two hK s with rfl | rfl
    · simp
    · rw [one_pow, one_mul, one_add_one_eq_zero hK, zero_add]
      exact one_ne_zero
  have h := CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadMinus (K := K) (n := 4)
    (by norm_num) hirr
  rw [hK] at h
  have e : ((2 : ℕ) : ℤ) ^ (4 * (4 - 1)) * (((2 : ℕ) : ℤ) ^ 4 + 1) *
      ∏ i ∈ Finset.Icc 1 (4 - 1), (((2 : ℕ) : ℤ) ^ (2 * i) - 1) = 197406720 := by
    decide
  rw [e] at h
  have h' : Nat.card (elementaryGroup (quadMinus 4 K 1 1)) = 197406720 := by exact_mod_cast h
  rw [← h']
  exact Nat.card_congr (elementaryIsometryEquiv (minusTailIsometry 4 K 1 1)).toEquiv

theorem finite_elementaryGroup_qM : Finite (orthElementaryGroup (qM K)) :=
  Nat.finite_of_card_ne_zero (by rw [card_elementaryGroup_qM hK]; norm_num)

end Action

end CFSG.EvenSmallLie.OmegaEightMinus
