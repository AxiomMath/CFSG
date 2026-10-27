module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Check

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

@[expose] def zeroRV : RV := ⟨0, 0, 0, 0⟩

theorem ofRV_zeroRV : ofRV zeroRV = 0 := by
  ext i
  fin_cases i <;> simp [ofRV, zeroRV, zc]

@[expose] def inFR (w : RV) : Bool := fR.contains w

@[expose] def rneg (a : R4) : R4 :=
  ⟨(4 - a.a00) % 4, (4 - a.a01) % 4, (4 - a.a02) % 4, (4 - a.a03) % 4,
   (4 - a.a10) % 4, (4 - a.a11) % 4, (4 - a.a12) % 4, (4 - a.a13) % 4,
   (4 - a.a20) % 4, (4 - a.a21) % 4, (4 - a.a22) % 4, (4 - a.a23) % 4,
   (4 - a.a30) % 4, (4 - a.a31) % 4, (4 - a.a32) % 4, (4 - a.a33) % 4⟩

theorem ofR4_rneg {a : R4} (ha : a.wf) : ofR4 (rneg a) = -ofR4 a := by
  obtain ⟨h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33⟩ := ha
  have key : ∀ x : ℕ, x < 4 → zc ((4 - x) % 4) = -zc x := by
    intro x hx
    obtain rfl | rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    all_goals decide
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofR4, rneg, Matrix.neg_apply] <;> exact key _ ‹_›

@[expose] def sqsR : List R4 := (q0R.map fun a => rmul a a).dedup

@[expose] def sqprodsR : List R4 := sqsR.flatMap fun a => sqsR.map (rmul a)

@[expose] def uSqprodCheck : Bool :=
  q0R.all fun b => sqprodsR.contains b || sqprodsR.contains (rneg b)

theorem sqprod_of_check (h : uSqprodCheck = true) : ∀ B ∈ q0List, ∃ A₁ ∈ q0List, ∃ A₂ ∈ q0List,
    B = A₁ * A₁ * (A₂ * A₂) ∨ B = -(A₁ * A₁ * (A₂ * A₂)) := by
  intro B hB
  have hb : toR4 B ∈ q0R := List.mem_map.2 ⟨B, hB, rfl⟩
  have h1 := (List.all_eq_true.1 h) _ hb
  have key : ∀ b : R4, b ∈ sqprodsR → ∃ A₁ ∈ q0List, ∃ A₂ ∈ q0List,
      ofR4 b = A₁ * A₁ * (A₂ * A₂) := by
    intro b hbm
    obtain ⟨a₁, ha₁, hrest⟩ := List.mem_flatMap.1 hbm
    obtain ⟨a₂, ha₂, rfl⟩ := List.mem_map.1 hrest
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 ha₁)
    obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 ha₂)
    obtain ⟨A₁, hA₁, rfl⟩ := List.mem_map.1 hc₁
    obtain ⟨A₂, hA₂, rfl⟩ := List.mem_map.1 hc₂
    refine ⟨A₁, hA₁, A₂, hA₂, ?_⟩
    rw [ofR4_rmul, ofR4_rmul, ofR4_rmul, ofR4_toR4, ofR4_toR4]
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h1
  rcases h1 with h1 | h1
  · obtain ⟨A₁, hA₁, A₂, hA₂, he⟩ := key _ h1
    rw [ofR4_toR4] at he
    exact ⟨A₁, hA₁, A₂, hA₂, Or.inl he⟩
  · obtain ⟨A₁, hA₁, A₂, hA₂, he⟩ := key _ h1
    rw [ofR4_rneg (wf_toR4 B), ofR4_toR4] at he
    refine ⟨A₁, hA₁, A₂, hA₂, Or.inr ?_⟩
    rw [← he, neg_neg]

theorem mem_allVR (v : V4) : toRV v ∈ allVR := by
  unfold allVR
  refine List.mem_map.2 ⟨(v 0).val + 4 * (v 1).val + 16 * (v 2).val + 64 * (v 3).val, ?_, ?_⟩
  · have h0 := ZMod.val_lt (v 0)
    have h1 := ZMod.val_lt (v 1)
    have h2 := ZMod.val_lt (v 2)
    have h3 := ZMod.val_lt (v 3)
    exact List.mem_range.2 (by omega)
  · have h0 := ZMod.val_lt (v 0)
    have h1 := ZMod.val_lt (v 1)
    have h2 := ZMod.val_lt (v 2)
    have h3 := ZMod.val_lt (v 3)
    simp only [toRV, RV.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem inFR_iff {w : RV} (hw : w.wf) : inFR w = true ↔ ofRV w ∈ fVecs := by
  unfold inFR fR
  rw [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [ofRV_toRV]
  · intro h
    exact ⟨ofRV w, h, toRV_ofRV hw⟩

@[expose] def uLamCheck (sr : List R4) : Bool :=
  sr.all fun b => allVR.all fun v =>
    !(inFR (radd v v)) || inFR (radd (rmv b v) (rmv b v))

@[expose] def uKerCheck (sr : List R4) : Bool :=
  sr.all fun b => !(omR.all fun v => rmv b v == v) || b == R4.one || b == R4.negOne

@[expose] def uFxCheck (sr : List R4) : Bool :=
  sr.all fun b => !(rmul b b == R4.one) ||
    fR.any (fun v => rmv b (radd tRV v) == radd tRV v) ||
    allVR.all fun w => !(radd (radd w (rmv b w)) (radd w (rmv b w)) == zeroRV) ||
      inFR (radd w w)

@[expose] def uSCheck (a : R4) : Bool :=
  uLamCheck (sListR a) && uKerCheck (sListR a) && uFxCheck (sListR a)

theorem lamInv_sound {sr : List R4} (h : uLamCheck sr = true) :
    ∀ B ∈ sr.map ofR4, ∀ v : V4, v + v ∈ fVecs → B *ᵥ v + B *ᵥ v ∈ fVecs := by
  intro B hB v hv
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hB
  simp only [uLamCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  have h1 := h b hb (toRV v) (mem_allVR v)
  have hv' : inFR (radd (toRV v) (toRV v)) = true := by
    rw [inFR_iff (wf_radd _ _), ofRV_radd, ofRV_toRV]
    exact hv
  rcases h1 with h1 | h1
  · rw [hv'] at h1
    exact absurd h1 (by simp)
  · rw [inFR_iff (wf_radd _ _), ofRV_radd, ofRV_rmv, ofRV_toRV] at h1
    exact h1

theorem ker_sound {sr : List R4} (hom : ∀ v ∈ omList, v + v = 0) (h : uKerCheck sr = true) :
    ∀ B ∈ sr.map ofR4, (∀ v : V4, v + v = 0 → B *ᵥ v = v) → B = 1 ∨ B = -1 := by
  intro B hB hker
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hB
  simp only [uKerCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  have hall : (omR.all fun v => rmv b v == v) = true := by
    simp only [List.all_eq_true, beq_iff_eq]
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    apply ofRV_inj (wf_rmv _ _) (wf_toRV _)
    rw [ofRV_rmv, ofRV_toRV]
    exact hker v (hom v hv)
  rcases h b hb with (h1 | h1) | h1
  · rw [hall] at h1
    exact absurd h1 (by simp)
  · left
    rw [h1, ofR4_one]
  · right
    rw [h1, ofR4_negOne]

theorem fx_sound {sr : List R4} (h : uFxCheck sr = true) :
    ∀ B ∈ sr.map ofR4, B * B = 1 → (∃ v ∈ fVecs, B *ᵥ (tVec + v) = tVec + v) ∨
      (∀ w : V4, (w + B *ᵥ w) + (w + B *ᵥ w) = 0 → w + w ∈ fVecs) := by
  intro B hB hBB
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hB
  simp only [uFxCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    List.any_eq_true, beq_eq_false_iff_ne] at h
  have hbb : rmul b b = R4.one := by
    apply ofR4_inj (wf_rmul _ _) wf_one
    rw [ofR4_rmul, ofR4_one]
    exact hBB
  rcases h b hb with (h1 | ⟨v', hv', h2⟩) | h3
  · exact absurd hbb h1
  · left
    refine ⟨ofRV v', ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv'
      rwa [ofRV_toRV]
    · have := congrArg ofRV h2
      have e : ofRV tRV = tVec := ofRV_toRV tVec
      rw [ofRV_rmv, ofRV_radd, e] at this
      exact this
  · right
    intro w hw
    have h4 := h3 (toRV w) (mem_allVR w)
    have hz : radd (radd (toRV w) (rmv b (toRV w))) (radd (toRV w) (rmv b (toRV w))) = zeroRV := by
      apply ofRV_inj (wf_radd _ _) (by decide)
      rw [ofRV_radd, ofRV_radd, ofRV_rmv, ofRV_toRV, ofRV_zeroRV]
      exact hw
    rcases h4 with h4 | h4
    · exact absurd hz h4
    · rw [inFR_iff (wf_radd _ _), ofRV_radd, ofRV_toRV] at h4
      exact h4

theorem ufactsOf_of_check (α : M4) (hom : ∀ v ∈ omList, v + v = 0) (h : uSCheck (toR4 α) = true) :
    UFactsOf (sList α) := by
  simp only [uSCheck, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [sList_eq]
  exact ⟨lamInv_sound h1, fx_sound h3, ker_sound hom h2⟩

end CFSG.EvenSporadicStandard.TwoHS
