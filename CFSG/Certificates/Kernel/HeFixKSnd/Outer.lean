
module

public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.HeFixKSnd.Search

public section

namespace CFSG.KC.HeFixKSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.KC.HeFixK
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.Sporadic.SmallOddCore
open CFSG.KLie.CT (fget)

theorem out1_rec_eq (step : Nat → Nat → Nat) (N : Nat) :
    ∀ r, r ≤ N → ∀ c, Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (step (Nat.sub (Nat.sub N r) 1) c) ih) r c =
        (List.range' (N - r) r).foldl (fun c j => step j c) c := by
  intro r
  induction r with
  | zero => intro _ c; rfl
  | succ r ih =>
    intro hr c
    have h1 : N - (r + 1) = N - r - 1 := by omega
    have h2 : N - r - 1 + 1 = N - r := by omega
    have e : List.range' (N - (r + 1)) (r + 1) = (N - r - 1) :: List.range' (N - r) r := by
      rw [h1, List.range'_succ, h2]
    show strictN (step (N - r - 1) c)
        (Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
          (fun r ih c => strictN (step (Nat.sub (Nat.sub N r) 1) c) ih) r) =
        (List.range' (N - (r + 1)) (r + 1)).foldl (fun c j => step j c) c
    rw [strictN_app, ih (by omega) (step (N - r - 1) c), e, List.foldl_cons]

theorem out1_foldl_steps {step : Nat → Nat → Nat} (hz : ∀ k, step k 0 = 0) :
    ∀ (L : List Nat) (c : Nat), L.foldl (fun c j => step j c) c ≠ 0 →
      c ≠ 0 ∧ ∀ k ∈ L, ∃ c', c' ≠ 0 ∧ step k c' ≠ 0 := by
  intro L
  induction L with
  | nil => intro c hc; exact ⟨hc, by simp⟩
  | cons a L ih =>
    intro c hc
    obtain ⟨h1, h2⟩ := ih (step a c) hc
    have hc0 : c ≠ 0 := by
      intro h0
      apply h1
      rw [h0]
      exact hz a
    refine ⟨hc0, ?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with h | h
    · subst h
      exact ⟨c, hc0, h1⟩
    · exact h2 k h

theorem out1_pair_trip {N : Nat} {T : Nat → Nat} {IT WT a c j : Nat}
    (h : pairK N T IT WT a c j ≠ 0) (hc : c ≠ 0) (hbit : bitK IT j = true)
    (hcomm : comm 32 6 (T j) a = true) :
    tripK N T a (T j) (fget WT (c - 1) 30) = true := by
  unfold pairK at h
  simp only [strictN_app, nIf_ite] at h
  split_ifs at h with h1 h2
  · exact absurd rfl h
  · exact h2
  · exact absurd rfl h

theorem out1_outerAt_inner {TA : Nat → Nat} {N : Nat} {T : Nat → Nat} {IT WT i c : Nat}
    (h : outerAt TA N T IT WT i c ≠ 0) (hc : c ≠ 0)
    (hsq : Nat.beq (mul 32 6 (TA i) (TA i)) (pidn 32 6) = true)
    (hnot : inL N T (TA i) = false) :
    innerK N T IT WT (TA i) c ≠ 0 := by
  unfold outerAt at h
  simp only [strictN_app, nIf_ite] at h
  split_ifs at h with h1 h2
  · exact absurd rfl h
  · exact absurd (h2.symm.trans hnot) (by decide)
  · exact h

theorem outerK_spec {NA N IT WT : Nat} {TA T : Nat → Nat} (h : 0 < outerK NA TA N T IT WT) :
    ∀ i < NA, Nat.beq (mul 32 6 (TA i) (TA i)) (pidn 32 6) = true → inL N T (TA i) = false →
      ∀ j < N, bitK IT j = true → comm 32 6 (T j) (TA i) = true →
        ∃ c, c ≠ 0 ∧ tripK N T (TA i) (T j) (fget WT (c - 1) 30) = true := by
  intro i hi hsq hnot j hj hbit hcomm
  have hO : outerK NA TA N T IT WT =
      (List.range' 0 NA).foldl (fun c k => outerAt TA N T IT WT k c) 1 := by
    have := out1_rec_eq (fun k c => outerAt TA N T IT WT k c) NA NA (Nat.le_refl NA) 1
    rw [Nat.sub_self] at this
    exact this
  have hzo : ∀ k, (fun k c => outerAt TA N T IT WT k c) k 0 = 0 := by
    intro k
    show strictN (TA k) (fun _ => 0) = 0
    rw [strictN_app]
  have hO0 : (List.range' 0 NA).foldl (fun c k => outerAt TA N T IT WT k c) 1 ≠ 0 := by
    intro h0
    have h1 := hO.trans h0
    omega
  obtain ⟨-, hsO⟩ := out1_foldl_steps (step := fun k c => outerAt TA N T IT WT k c) hzo
    (List.range' 0 NA) 1 hO0
  obtain ⟨c, hc, hcO⟩ := hsO i (List.mem_range'_1.mpr ⟨Nat.zero_le i, by omega⟩)
  have hcO' : outerAt TA N T IT WT i c ≠ 0 := hcO
  have hI : innerK N T IT WT (TA i) c ≠ 0 := out1_outerAt_inner hcO' hc hsq hnot
  have hIn : ∀ a d, innerK N T IT WT a d =
      (List.range' 0 N).foldl (fun c' k => pairK N T IT WT a c' k) d := by
    intro a d
    have := out1_rec_eq (fun k c' => pairK N T IT WT a c' k) N N (Nat.le_refl N) d
    rw [Nat.sub_self] at this
    exact this
  have hzi : ∀ k, (fun k c' => pairK N T IT WT (TA i) c' k) k 0 = 0 := fun k => rfl
  have hI' : (List.range' 0 N).foldl (fun c' k => pairK N T IT WT (TA i) c' k) c ≠ 0 := by
    intro h0
    exact hI ((hIn (TA i) c).trans h0)
  obtain ⟨-, hsI⟩ := out1_foldl_steps (step := fun k c' => pairK N T IT WT (TA i) c' k) hzi
    (List.range' 0 N) c hI'
  obtain ⟨c', hc', hpair⟩ := hsI j (List.mem_range'_1.mpr ⟨Nat.zero_le j, by omega⟩)
  have hpair' : pairK N T IT WT (TA i) c' j ≠ 0 := hpair
  exact ⟨c', hc', out1_pair_trip hpair' hc' hbit hcomm⟩

theorem tabsOf_found {N : Nat} {T : Nat → Nat} {x : Nat} (hT : ∀ i < N, PP 32 6 (T i))
    (hx : PP 32 6 x) (h : inL N T x = true) :
    found (indexOf (tabsOf N T)) (tabsOf N T) (unpack 32 6 x) = true := by
  rw [CFSG.KS.PEnum.found_indexOf_iff]
  unfold inL at h
  rw [strictB_app, anyN_eq, List.any_eq_true] at h
  obtain ⟨i, hi, hb⟩ := h
  have hi' := List.mem_range.1 hi
  have e : x = T i := Nat.eq_of_beq_eq_true hb
  exact ⟨i, by rw [tabsOf_size]; exact hi', by rw [tabsOf_get T hi', e]⟩

theorem bit_of_itK {N IT : Nat} {T : Nat → Nat} (h : itK N T IT = true) {j : Nat} (hj : j < N)
    (hs : Nat.beq (mul 32 6 (T j) (T j)) (pidn 32 6) = true) : bitK IT j = true := by
  have h1 := CFSG.KS.allN_spec h j hj
  unfold CFSG.KC.HeFixK.itK at h1
  simp only [strictB_app] at h1
  rw [hs] at h1
  revert h1
  cases bitK IT j <;> simp [CFSG.KC.HeAutK.eqB, CFSG.KLie.CT.notB]

theorem outer_tabs {NT NA IT WT : Nat} {TT TA : Nat → Nat} (hT : ∀ i < NT, PP 32 6 (TT i))
    (hA : ∀ i < NA, PP 32 6 (TA i)) (hi : itK NT TT IT = true)
    (ho : 0 < outerK NA TA NT TT IT WT) :
    hfOuterE8Check 32 (tabsOf NT TT) (tabsOf NA TA) = true := by
  have spec := outerK_spec ho
  unfold hfOuterE8Check
  simp only [allBelow, List.all_eq_true, List.mem_range, tabsOf_size, Bool.or_eq_true,
    Bool.not_eq_true']
  intro i hiA
  have PAi := hA i hiA
  rw [tabsOf_get TA hiA]
  by_cases hf : found (indexOf (tabsOf NT TT)) (tabsOf NT TT) (unpack 32 6 (TA i)) = true
  · exact Or.inl (Or.inl hf)
  have hinL : inL NT TT (TA i) = false := by
    cases hc : inL NT TT (TA i)
    · rfl
    · exact absurd (tabsOf_found hT PAi hc) hf
  by_cases hsq : (comp 32 (unpack 32 6 (TA i)) (unpack 32 6 (TA i)) == idTab 32) = true
  swap
  · exact Or.inl (Or.inr (by simpa using hsq))
  right
  rw [tab_sq PAi] at hsq
  intro j hj
  rw [tabsOf_get TT hj]
  have PTj := hT j hj
  by_cases hsqj : (comp 32 (unpack 32 6 (TT j)) (unpack 32 6 (TT j)) == idTab 32) = true
  swap
  · exact Or.inl (Or.inl (by simpa using hsqj))
  rw [tab_sq PTj] at hsqj
  by_cases hcm : (comp 32 (unpack 32 6 (TT j)) (unpack 32 6 (TA i)) ==
      comp 32 (unpack 32 6 (TA i)) (unpack 32 6 (TT j))) = true
  swap
  · exact Or.inl (Or.inr (by simpa using hcm))
  rw [tab_comm PTj PAi] at hcm
  right
  obtain ⟨c, -, hc⟩ := spec i hiA hsq hinL j hj (bit_of_itK hi hj hsqj) hcm
  exact hfPairOK_of_tripK hT PAi PTj hc

end CFSG.KC.HeFixKSnd

end
