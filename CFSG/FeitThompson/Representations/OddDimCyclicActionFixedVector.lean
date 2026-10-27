module

public import CFSG.FeitThompson.Representations.CyclicConjugationEigenspaceDimensions
import CFSG.FeitThompson.Representations.ZeroCoordinateAutocorrelationGaps

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module CyclicAutocorrelation

section

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

lemma mem_eigenspace_one_iff {T : V ≃ₗ[k] V} {v : V} :
    v ∈ Module.End.eigenspace (T : Module.End k V) 1 ↔ T v = v := by
  rw [Module.End.mem_eigenspace_iff, one_smul]
  rfl

variable [IsAlgClosed k] [FiniteDimensional k V] {r : ℕ} {ε : k}

theorem hasEigenvalue_one_of_finrank_conjEigenspace
    (hr : 3 ≤ r) (hrodd : Odd r) (hrk : (r : k) ≠ 0) (hε : IsPrimitiveRoot ε r)
    {T : V ≃ₗ[k] V} (hT : T ^ r = 1) (hV1 : 1 < finrank k V) (hVodd : Odd (finrank k V))
    (hE : ∀ m : ZMod r, m ≠ 0 →
      finrank k (conjEigenspace ε T (0 : ZMod r)) = finrank k (conjEigenspace ε T m) + 1) :
    Module.End.HasEigenvalue (T : Module.End k V) 1 := by
  have : NeZero r := ⟨by omega⟩
  rw [Module.End.hasEigenvalue_iff]
  intro hbot
  set n : ZMod r → ℕ := fun i ↦ finrank k (cyclicEigenspace ε T i) with hn
  have h0 : n 0 = 0 := by
    have hb : cyclicEigenspace ε T (0 : ZMod r) = ⊥ := by
      rw [cyclicEigenspace_eq_eigenspace]
      simpa using hbot
    rw [hn]
    simp [hb]
  have hc : ∀ m : ZMod r, finrank k (conjEigenspace ε T m) = autocorr n m := fun m ↦ by
    rw [finrank_conjEigenspace hrk hε hT m, autocorr_apply]
  have hgap : ∀ m : ZMod r, m ≠ 0 → autocorr n 0 = autocorr n m + 1 := fun m hm ↦ by
    rw [← hc, ← hc]; exact hE m hm
  have hd : ∑ i, n i = finrank k V :=
    (finrank_eq_sum_finrank_cyclicEigenspace hrk hε hT).symm
  rcases sum_eq_one_or_eq_card_sub_one (by omega) h0 hgap with h | h
  · omega
  · obtain ⟨t, ht⟩ := hrodd
    obtain ⟨s, hs⟩ := hVodd
    omega

theorem exists_ne_zero_fixed_of_finrank_conjEigenspace
    (hr : 3 ≤ r) (hrodd : Odd r) (hrk : (r : k) ≠ 0) (hε : IsPrimitiveRoot ε r)
    {T : V ≃ₗ[k] V} (hT : T ^ r = 1) (hV1 : 1 < finrank k V) (hVodd : Odd (finrank k V))
    (hE : ∀ m : ZMod r, m ≠ 0 →
      finrank k (conjEigenspace ε T (0 : ZMod r)) = finrank k (conjEigenspace ε T m) + 1) :
    ∃ v : V, v ≠ 0 ∧ T v = v := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Module.End.hasEigenvalue_iff.1
      (hasEigenvalue_one_of_finrank_conjEigenspace hr hrodd hrk hε hT hV1 hVodd hE))
  exact ⟨v, hv0, mem_eigenspace_one_iff.1 hv⟩

theorem cyclicEigenspace_zero_ne_bot_of_finrank_conjEigenspace
    (hr : 3 ≤ r) (hrodd : Odd r) (hrk : (r : k) ≠ 0) (hε : IsPrimitiveRoot ε r)
    {T : V ≃ₗ[k] V} (hT : T ^ r = 1) (hV1 : 1 < finrank k V) (hVodd : Odd (finrank k V))
    (hE : ∀ m : ZMod r, m ≠ 0 →
      finrank k (conjEigenspace ε T (0 : ZMod r)) = finrank k (conjEigenspace ε T m) + 1) :
    cyclicEigenspace ε T (0 : ZMod r) ≠ ⊥ := by
  have : NeZero r := ⟨by omega⟩
  rw [cyclicEigenspace_eq_eigenspace]
  simpa using Module.End.hasEigenvalue_iff.1
    (hasEigenvalue_one_of_finrank_conjEigenspace hr hrodd hrk hε hT hV1 hVodd hE)

end

end

end CFSG.FeitThompson
