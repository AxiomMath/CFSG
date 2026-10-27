
module

public import Certificates.Data.Kernel.GammaUColK
public import CFSG.Certificates.Kernel.GammaUFrameSound
public import CFSG.GF2Type.Smith1979.GammaU.StepCInputs
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairInputs

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem anyB_iff (n : Nat) (f : Nat → Bool) : anyB n f = true ↔ ∃ k < n, f k = true := by
  induction n with
  | zero => simp [anyB]
  | succ n ih =>
    change (f n || anyB n f) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨k, hk, hf⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, hf⟩
    · rintro ⟨k, hk, hf⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inr ⟨k, hk, hf⟩
      · exact Or.inl hf

theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem appN_rowsP (S n : Nat) : appN (rowsP S) n = ap12 S n := by
  have hr : ∀ x ∈ rowsP S, x < 4096 := by
    intro x hx
    simp only [rowsP, List.mem_toArray, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  refine vecOf_inj (appN_lt hr n) (ap12_lt S n) ?_
  rw [vecOf_appN, vecOf_ap12]
  rfl

theorem cpCond_eq (e : Nat) : cpCond e = (e != 0 && !q0b e && e != a0 && e != theta0N a0 &&
    e != (a0 ^^^ theta0N a0)) := by
  simp only [cpCond, not_beq_eq]
  rfl

theorem inCP_iff (TE NE e : Nat) : inCP TE NE e = true ↔ ∃ n < NE, ap12 (look TE n) 3072 = e := by
  unfold inCP
  rw [anyB_iff]
  simp only [Nat.beq_eq]

theorem killOK_spec {S F e : Nat} (h : killOK S F e = true) (n : Nat) :
    Nat.xor (ap12 S n) n ≠ e := by
  unfold killOK at h
  rw [Bool.and_eq_true, allBelow_iff, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.beq_eq] at h
  obtain ⟨hz, hne⟩ := h
  have hlin : (linP F).comp (linP S + LinearMap.id) = 0 := by
    refine linMap_ext fun j => ?_
    have := Nat.eq_of_beq_eq_true (hz j j.2)
    have hv := congrArg vecOf this
    rw [vecOf_ap12, xor_eq, vecOf_xor, vecOf_ap12, vecOf_zero] at hv
    simpa using hv
  intro hn
  apply hne
  have hv : vecOf (ap12 F e) = 0 := by
    rw [← hn, vecOf_ap12, xor_eq, vecOf_xor, vecOf_ap12]
    have := congrArg (fun f => f (vecOf n)) hlin
    simpa using this
  exact (vecOf_eq_zero (ap12_lt F e)).1 hv

theorem cpOK_spec {SL : List Nat} {S TE NE : Nat} {R : List (List Nat)}
    (h : cpOK SL S TE NE R = true) :
    (∀ e ∈ SL, (cpCond e = true ∧ ∃ n < 4096, Nat.xor (ap12 S n) n = e) ↔
      ∃ n < NE, ap12 (look TE n) 3072 = e) ∧ ∀ n < NE, ap12 (look TE n) 3072 ∈ SL := by
  unfold cpOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, List.all_eq_true, allBelow_iff,
    memN_iff] at h
  obtain ⟨⟨hlen, hall⟩, hin⟩ := h
  refine ⟨fun e he => ?_, hin⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  have hkR : k < R.length := by rw [← hlen]; exact hk
  have hz : (SL[k], R[k]) ∈ List.zip SL R := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_zip]; omega, by rw [List.getElem_zip]⟩
  have hent : cpEnt S TE NE SL[k] R[k] = true := hall _ hz
  unfold cpEnt at hent
  rw [← inCP_iff]
  cases ht0 : Nat.beq (nthD 0 R[k] 0) 0
  · rw [ht0, cond_false] at hent
    cases ht1 : Nat.beq (nthD 0 R[k] 0) 1
    · rw [ht1, cond_false] at hent
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hent
      obtain ⟨⟨hc, hcp⟩, hkill⟩ := hent
      rw [hcp]
      simp only [Bool.false_eq_true, iff_false, not_and, not_exists]
      exact fun _ n _ => killOK_spec hkill n
    · rw [ht1, cond_true] at hent
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hent
      obtain ⟨⟨⟨hc, hcp⟩, hlt⟩, hw⟩ := hent
      exact ⟨fun _ => hcp, fun _ => ⟨hc, _, hlt, hw⟩⟩
  · rw [ht0, cond_true] at hent
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hent
    obtain ⟨hc, hcp⟩ := hent
    rw [hc, hcp]
    simp

theorem colPts_iff {S TE NE : Nat} {R : List (List Nat)} (h : cpOK (spanList d0) S TE NE R = true)
    (e : Nat) : e ∈ colPts (rowsP S) ↔ ∃ n < NE, ap12 (look TE n) 3072 = e := by
  obtain ⟨h1, h2⟩ := cpOK_spec h
  unfold colPts
  simp only [← cpCond_eq, List.mem_filter, Bool.and_eq_true, List.contains_iff_mem, List.mem_map,
    List.mem_range, appN_rowsP]
  constructor
  · rintro ⟨he, hc, n, hn, hne⟩
    exact (h1 e he).1 ⟨hc, n, hn, hne⟩
  · intro hx
    obtain ⟨n, hn, rfl⟩ := hx
    have he := h2 n hn
    obtain ⟨hc, m, hm, hme⟩ := (h1 _ he).2 ⟨n, hn, rfl⟩
    exact ⟨he, hc, m, hm, hme⟩

end CFSG.KC.GUV

end
