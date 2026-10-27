module

public import CFSG.GF2Type.SmithTypeE.LMod.Points
public import CFSG.LargeExtraspecial.SMod20Basic
public import Certificates.Certificate38601

public section

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_apply decode_xor decode_zero decode_two_pow
  eq_of_decode_eq colsLin colsLin_apply colsLin_single decode_applyCols linearMap_ext_single
  linearEquiv_ext_single bit bit_xor bit_and bit_foldl decode_apply_bit)

theorem tvInvCheck_holds : chkTvInv = true :=
  Certificates.certificate38601.1

theorem pairsCheck_holds : chkPairs = true :=
  Certificates.certificate38601.2.1

theorem twCheck_holds : chkTW = true :=
  Certificates.certificate38601.2.2.1

theorem formInvCheck_holds : chkFormInv = true :=
  Certificates.certificate38601.2.2.2

theorem size_tvCols (k : Nat) : (tvCols k).size = 20 := by
  simp [tvCols]

theorem tvArr_get {k : Nat} (hk : k < 1953) : tvArr[k]! = tvCols k := by
  simp [tvArr, getElem!_pos, hk]

theorem wtArr_get {i : Nat} (hi : i < 1395) : wtArr[i]! = wt i := by
  simp [wtArr, getElem!_pos, hi]

@[expose] noncomputable def tvLin (k : Nat) : V →ₗ[ZMod 2] V := colsLin (tvCols k)

theorem tvLin_decode (k c : Nat) : tvLin k (decode c) = decode (applyCols (tvCols k) c) :=
  (decode_applyCols (size_tvCols k) c).symm

theorem tvLin_single (k : Nat) (m : Fin 20) :
    tvLin k (Pi.single m 1) = decode (tvCols k)[m.val]! :=
  colsLin_single _ m

theorem tvInv_parts {k : Nat} (hk : k < 1953) :
    ∀ m < 20, (tvCols k)[m]! < 2 ^ 20 ∧ applyCols (tvCols k) (tvCols k)[m]! = 2 ^ m := by
  have h := tvInvCheck_holds
  simp only [chkTvInv, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨-, h2⟩ := h k hk
  rw [tvArr_get hk] at h2
  exact h2

theorem tvLin_tvLin {k : Nat} (hk : k < 1953) (v : V) :
    tvLin k (tvLin k v) = v := by
  have : tvLin k ∘ₗ tvLin k = LinearMap.id := by
    apply linearMap_ext_single
    intro m
    rw [LinearMap.comp_apply, LinearMap.id_apply, tvLin_single, tvLin_decode,
      (tvInv_parts hk m m.2).2, decode_two_pow]
  exact LinearMap.congr_fun this v

@[expose] noncomputable def tvEquiv (k : Nat) :
    V ≃ₗ[ZMod 2] V :=
  if hk : k < 1953 then LinearEquiv.ofInvolutive (tvLin k) (tvLin_tvLin hk)
  else LinearEquiv.refl (ZMod 2) V

theorem tvEquiv_apply {k : Nat} (hk : k < 1953) (v : V) :
    tvEquiv k v = tvLin k v := by
  simp only [tvEquiv, hk, ↓reduceDIte]
  rfl

theorem tvEquiv_decode {k : Nat} (hk : k < 1953) (c : Nat) :
    tvEquiv k (decode c) = decode (applyCols (tvCols k) c) := by
  rw [tvEquiv_apply hk, tvLin_decode]

theorem tvEquiv_single {k : Nat} (hk : k < 1953) (m : Fin 20) :
    tvEquiv k (Pi.single m 1) = decode (tvCols k)[m.val]! := by
  rw [tvEquiv_apply hk, tvLin_single]

theorem tvEquiv_mul_self {k : Nat} (hk : k < 1953) :
    tvEquiv k * tvEquiv k = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, tvEquiv_apply hk, tvEquiv_apply hk, tvLin_tvLin hk]
  rfl

@[expose] def planeSet (i : Nat) : Finset (Fin 1953) :=
  Finset.univ.filter fun a => inPlane i a.val

theorem mem_planeSet {i : Nat} {a : Fin 1953} : a ∈ planeSet i ↔ inPlane i a.val = true := by
  simp [planeSet]

@[expose] def wtV (i : Nat) : V := decode (wt i)

theorem planePtsArr_get {i : Nat} (hi : i < 1395) : planePtsArr[i]! = planePts i := by
  simp [planePtsArr, getElem!_pos, hi]

theorem flagArr_get {j a : Nat} (hj : j < 1395) (ha : a < 1953) :
    (flagArr[j]!)[a]! = inPlane j a := by
  simp [flagArr, getElem!_pos, hj, ha]

theorem mem_planePts {i a : Nat} : a ∈ planePts i ↔ a < 1953 ∧ inPlane i a = true := by
  simp [planePts, List.mem_filter]

theorem card_planeSet_eq (i : Nat) : (planeSet i).card = (planePts i).size := by
  have h : (planeSet i).map Fin.valEmbedding = (Finset.range 1953).filter (inPlane i ·) := by
    ext a
    simp only [Finset.mem_map, mem_planeSet, Fin.valEmbedding_apply, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨⟨a, ha⟩, hb, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Finset.card_def, Finset.filter_val,
    Finset.range_val, Multiset.range, Multiset.filter_coe, Multiset.coe_card]
  simp [planePts]

theorem meetCard_eq_length {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    meetCard i j = ((List.range 1953).filter fun a => inPlane i a && inPlane j a).length := by
  unfold meetCard
  rw [planePtsArr_get hi, Array.countP_eq_size_filter, planePts, List.filter_toArray,
    List.size_toArray, List.filter_filter]
  refine congrArg List.length (List.filter_congr fun a ha => ?_)
  rw [flagArr_get hj (List.mem_range.mp ha), Bool.and_comm]

theorem meetCard_eq_card {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    meetCard i j = (planeSet i ∩ planeSet j).card := by
  have h : (planeSet i ∩ planeSet j).map Fin.valEmbedding =
      (Finset.range 1953).filter fun a => inPlane i a && inPlane j a := by
    ext a
    simp only [Finset.mem_map, Finset.mem_inter, mem_planeSet, Fin.valEmbedding_apply,
      Finset.mem_filter, Finset.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
      exact ⟨b.2, hb1, hb2⟩
    · rintro ⟨ha, hb1, hb2⟩
      exact ⟨⟨a, ha⟩, ⟨hb1, hb2⟩, rfl⟩
  rw [meetCard_eq_length hi hj, ← Finset.card_map Fin.valEmbedding, h]
  simp only [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card, Bool.decide_eq_true]

theorem flagArr_row_size {j : Nat} (hj : j < 1395) : (flagArr[j]!).size = 1953 := by
  simp [flagArr, getElem!_pos, hj]

theorem pairs_parts {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    (i = j → meetCard i j = 49) ∧
      (i ≠ j → meetCard i j = 0 ∨ meetCard i j = 1 ∨ meetCard i j = 9) ∧
      fB wtArr[i]! wtArr[j]! = decide (meetCard i j = 0) ∧
      adjM i j = decide (9 ≤ meetCard i j) := by
  have h := pairsCheck_holds
  simp only [chkPairs, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h i hi j hj
  refine ⟨fun hij => ?_, fun hij => ?_, ?_, h3⟩
  · simpa [hij] using h1
  · simpa [hij, or_assoc] using h1
  · by_cases hc : meetCard i j = 0 <;> simp [h2, hc]

theorem card_planeSet {i : Nat} (hi : i < 1395) :
    (planeSet i).card = 49 := by
  have := (pairs_parts hi hi).1 rfl
  rwa [meetCard_eq_card hi hi, Finset.inter_self] at this

theorem planeSet_injective {i j : Nat} (hi : i < 1395)
    (hj : j < 1395) (h : planeSet i = planeSet j) : i = j := by
  by_contra hij
  have h1 := (pairs_parts hi hj).2.1 hij
  rw [meetCard_eq_card hi hj, ← h, Finset.inter_self, card_planeSet hi] at h1
  omega

theorem tw_parts {k i : Nat} (hk : k < 1953) (hi : i < 1395) :
    planeImg k i < 1395 ∧ wt (planeImg k i) = applyCols (tvCols k) (wt i) ∧
      ∀ a < 1953, inPlane i a = true →
        tvImg k a < 1953 ∧ inPlane (planeImg k i) (tvImg k a) = true := by
  have h := twCheck_holds
  simp only [chkTW, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Array.all_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk i hi
  rw [wtArr_get h1, wtArr_get hi, tvArr_get hk] at h2
  refine ⟨h1, h2, fun a ha hai => ?_⟩
  have h4 := h3 a (by rw [planePtsArr_get hi]; exact mem_planePts.mpr ⟨ha, hai⟩)
  rw [tvTab_get hk ha] at h4
  have hx : tvImg k a < 1953 := by
    by_contra hx
    have : (flagArr[planeImg k i]!)[tvImg k a]! = false := by
      rw [getElem!_neg _ _ (by rw [flagArr_row_size h1]; exact hx)]
      rfl
    rw [this] at h4
    exact absurd h4 (by decide)
  exact ⟨hx, by rwa [flagArr_get h1 hx] at h4⟩

theorem tvEquiv_wtV {k i : Nat} (hk : k < 1953)
    (hi : i < 1395) : tvEquiv k (wtV i) = wtV (planeImg k i) := by
  rw [wtV, wtV, tvEquiv_decode hk, (tw_parts hk hi).2.1]

@[expose] def Opp (i j : Nat) : Prop := Disjoint (planeSet i) (planeSet j)

theorem opp_iff_meetCard {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    Opp i j ↔ meetCard i j = 0 := by
  rw [Opp, Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero, ← meetCard_eq_card hi hj]

@[expose] def fVal (v w : V) : ZMod 2 := ∑ t : Fin 20, v t * w (Fin.rev t)

@[expose] noncomputable def fModel : LinearMap.BilinForm (ZMod 2) V :=
  LinearMap.mk₂ (ZMod 2) fVal
    (fun v v' w => by
      simp only [fVal, Pi.add_apply, add_mul, ← Finset.sum_add_distrib])
    (fun c v w => by
      simp only [fVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun v w w' => by
      simp only [fVal, Pi.add_apply, mul_add, ← Finset.sum_add_distrib])
    (fun c v w => by
      simp only [fVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

theorem fModel_apply (v w : V) : fModel v w = fVal v w := rfl

theorem fModel_decode (u v : Nat) : fModel (decode u) (decode v) = bit (fB u v) := by
  rw [fModel_apply, fVal, fB, bit_foldl, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h : (Fin.rev t).val = 19 - t.val := by
    rw [Fin.val_rev]
    omega
  simp only [decode_apply_bit, bit_and, h]

open Classical in
theorem fModel_wtV {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    fModel (wtV i) (wtV j) = if Opp i j then 1 else 0 := by
  have e := (pairs_parts hi hj).2.2.1
  rw [wtArr_get hi, wtArr_get hj] at e
  rw [wtV, wtV, fModel_decode, e]
  by_cases ho : Opp i j
  · have : meetCard i j = 0 := (opp_iff_meetCard hi hj).mp ho
    simp [ho, this, bit]
  · have : ¬ meetCard i j = 0 := fun h => ho ((opp_iff_meetCard hi hj).mpr h)
    simp [ho, this, bit]

theorem fModel_tvEquiv {k : Nat} (hk : k < 1953) (v w : V) :
    fModel (tvEquiv k v) (tvEquiv k w) = fModel v w := by
  have h := formInvCheck_holds
  simp only [chkFormInv, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have key : fModel.compl₁₂ (tvEquiv k : V →ₗ[ZMod 2] V) (tvEquiv k : V →ₗ[ZMod 2] V) =
      fModel := by
    refine LinearMap.ext_basis (Pi.basisFun (ZMod 2) (Fin 20)) (Pi.basisFun (ZMod 2) (Fin 20))
      fun a b => ?_
    simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply, LinearEquiv.coe_coe]
    rw [tvEquiv_single hk, tvEquiv_single hk, fModel_decode, ← decode_two_pow, ← decode_two_pow,
      fModel_decode]
    have e := h k hk a a.2 b b.2
    rw [tvArr_get hk] at e
    rw [e]
  have := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V => B v w) key
  simpa using this

theorem fModel_single (v : V) (s : Fin 20) : fModel v (Pi.single s 1) = v (Fin.rev s) := by
  rw [fModel_apply, fVal, Finset.sum_eq_single (Fin.rev s)]
  · simp
  · intro b _ hb
    have : Fin.rev b ≠ s := fun h => hb (by rw [← h, Fin.rev_rev])
    simp [this]
  · simp

theorem fModel_nondegenerate {v : V} (h : ∀ w, fModel v w = 0) : v = 0 := by
  funext m
  have := h (Pi.single (Fin.rev m) 1)
  rw [fModel_single, Fin.rev_rev] at this
  exact this

end CFSG.GF2Type.SmithTypeE.LMod
