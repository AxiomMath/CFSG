module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Fin

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec122_stab_fixed {v : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (h : ∀ σ ∈ alternatingGroup (Fin 5), σ 0 = 0 → permVec σ v = v) : v = 0 ∨ v = wvec 0 := by
  revert h hv v
  simp only [Equiv.Perm.mem_alternatingGroup]
  unfold IsEvenVec wvec permVec
  decide +kernel

theorem sec122_schur (δ : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hev : ∀ v, IsEvenVec v → IsEvenVec (δ v))
    (hadd : ∀ v w, IsEvenVec v → IsEvenVec w → δ (v + w) = δ v + δ w)
    (hcomm : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEvenVec v →
      δ (permVec σ v) = permVec σ (δ v)) :
    (∀ v, IsEvenVec v → δ v = 0) ∨ (∀ v, IsEvenVec v → δ v = v) := by
  have ha : δ (wvec 0) = 0 ∨ δ (wvec 0) = wvec 0 := by
    apply sec122_stab_fixed (hev _ (wvec_even 0))
    intro σ hσ h0
    have h1 : permVec σ (wvec 0) = wvec 0 := by rw [permVec_wvec, h0]
    have h2 := hcomm σ hσ (wvec 0) (wvec_even 0)
    rw [h1] at h2
    exact h2.symm
  have hcase : (∀ i, δ (wvec i) = 0) ∨ (∀ i, δ (wvec i) = wvec i) := by
    rcases ha with h0 | h0
    · left
      intro i
      obtain ⟨σ, hσ, hσi⟩ := exists_alt_apply 0 i
      have h2 := hcomm σ hσ (wvec 0) (wvec_even 0)
      rw [permVec_wvec σ 0, hσi, h0] at h2
      rw [h2]
      rfl
    · right
      intro i
      obtain ⟨σ, hσ, hσi⟩ := exists_alt_apply 0 i
      have h2 := hcomm σ hσ (wvec 0) (wvec_even 0)
      rw [permVec_wvec σ 0, hσi, h0, permVec_wvec σ 0, hσi] at h2
      exact h2
  have hsum : ∀ v, IsEvenVec v → ∃ a b c d : Fin 5, v = (wvec a + wvec b) + (wvec c + wvec d) ∧
      δ v = (δ (wvec a) + δ (wvec b)) + (δ (wvec c) + δ (wvec d)) := by
    intro v hv
    obtain ⟨a, b, c, d, rfl⟩ := even_eq_four_wvec hv
    refine ⟨a, b, c, d, rfl, ?_⟩
    rw [hadd _ _ (wvec_add_even a b) (wvec_add_even c d), hadd _ _ (wvec_even a) (wvec_even b),
      hadd _ _ (wvec_even c) (wvec_even d)]
  rcases hcase with h0 | h0
  · left
    intro v hv
    obtain ⟨a, b, c, d, -, h⟩ := hsum v hv
    rw [h, h0, h0, h0, h0]
    simp
  · right
    intro v hv
    obtain ⟨a, b, c, d, h1, h⟩ := hsum v hv
    rw [h, h0, h0, h0, h0, ← h1]

end CFSG.OddStandard.SmallF3.Omega
