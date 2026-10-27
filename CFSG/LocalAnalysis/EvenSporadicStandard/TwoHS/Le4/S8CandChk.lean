module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

@[expose] def alphaRepsR : List R4 := alphaReps.map toR4

@[expose] def CRaw : Prop :=
  (∀ a ∈ candR, rmv a tRV = zpRV ∧ rmv a zpRV = tRV) ∧
  (∀ α ∈ alphaRepsR, α ∈ candR) ∧
  ∀ a ∈ candR, (∀ p ∈ q0R, rmv p zpRV = zpRV → ∃ q ∈ q0R, rmul p a = rmul a q) →
    rmul a a ∈ q0R → ∃ α₀ ∈ alphaRepsR, ∃ r ∈ repsR, ∃ q ∈ q0R, a = rmul (rmul r α₀) q

instance : Decidable CRaw := by unfold CRaw; infer_instance

@[expose] def candR_check : Bool := decide CRaw

theorem candFacts_of_raw (h : CRaw) : CandFacts := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨h11, h12⟩ := h1 (toR4 A) (List.mem_map.2 ⟨A, hA, rfl⟩)
    refine ⟨?_, ?_⟩
    · have := congrArg ofRV h11
      rw [ofRV_rmv, ofR4_toR4] at this
      simpa [tRV, zpRV, ofRV_toRV] using this
    · have := congrArg ofRV h12
      rw [ofRV_rmv, ofR4_toR4] at this
      simpa [tRV, zpRV, ofRV_toRV] using this
  · intro α hα
    obtain ⟨C, hC, hCα⟩ := List.mem_map.1 (h2 (toR4 α) (List.mem_map.2 ⟨α, hα, rfl⟩))
    rw [← ofR4_toR4 α, ← hCα, ofR4_toR4]
    exact hC
  · intro A hA hP1 hP2
    have ha : toR4 A ∈ candR := List.mem_map.2 ⟨A, hA, rfl⟩
    have hP1' : ∀ p ∈ q0R, rmv p zpRV = zpRV → ∃ q ∈ q0R, rmul p (toR4 A) = rmul (toR4 A) q := by
      intro p hp hpz
      obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hp
      have hPz : P *ᵥ zpVec = zpVec := by
        have := congrArg ofRV hpz
        rw [ofRV_rmv, ofR4_toR4] at this
        simpa [zpRV, ofRV_toRV] using this
      obtain ⟨Q, hQ, hPQ⟩ := hP1 P hP hPz
      refine ⟨toR4 Q, List.mem_map.2 ⟨Q, hQ, rfl⟩, ?_⟩
      apply ofR4_inj (wf_rmul _ _) (wf_rmul _ _)
      rw [ofR4_rmul, ofR4_rmul, ofR4_toR4, ofR4_toR4, ofR4_toR4]
      exact hPQ
    have hP2' : rmul (toR4 A) (toR4 A) ∈ q0R := by
      refine List.mem_map.2 ⟨A * A, hP2, ?_⟩
      apply ofR4_inj (wf_toR4 _) (wf_rmul _ _)
      rw [ofR4_toR4, ofR4_rmul, ofR4_toR4]
    obtain ⟨α₀', hα₀', r', hr', q', hq', hrq⟩ := h3 _ ha hP1' hP2'
    obtain ⟨α₀, hα₀, rfl⟩ := List.mem_map.1 hα₀'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hq'
    refine ⟨α₀, hα₀, r, hr, q, hq, ?_⟩
    have := congrArg ofR4 hrq
    rw [ofR4_rmul, ofR4_rmul, ofR4_toR4, ofR4_toR4, ofR4_toR4, ofR4_toR4] at this
    exact this

end CFSG.EvenSporadicStandard.TwoHS
