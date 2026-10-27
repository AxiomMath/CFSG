module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreTwistedA
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.DefChar.TwA
  CFSG.RankThree.Classical

set_option linter.unusedSectionVars false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem gLAPPrimeCoreOf_eq_bot_primeFormP_char (h : UnitaryFieldData p f K) (hn3 : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) (hp2 : p ≠ 2)
    {x : MulAut (primeFormP h (Cm n K))} (hx : x ∈ innerAut (primeFormP h (Cm n K)))
    (hxo : orderOf x = p) {H : Subgroup (MulAut (primeFormP h (Cm n K)))}
    (hH : innerAut (primeFormP h (Cm n K)) ≤ H) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut (primeFormP h (Cm n K))))) =
      ⊥ := by
  have hp : p.Prime := h.prime
  have : NeZero n := ⟨by omega⟩
  have : Finite K := h.finite
  have : Finite (primeFormP h (Cm n K)) := by infer_instance
  have hS := isSimpleGroup_primeFormP_one h hn3 hq
  have hnab : ∃ a b : primeFormP h (Cm n K), a * b ≠ b * a := by
    have := not_commute_primeFormP_one h hn3 hq
    push Not at this
    exact this
  have hZ : Subgroup.center (primeFormP h (Cm n K)) = ⊥ := center_eq_bot_of_simple hS hnab
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = p := by
    rw [← orderOf_injective (MulAut.conj : primeFormP h (Cm n K) →* _)
      (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  obtain ⟨u, N, hu1, hN, hN0, hUN, hu⟩ := exists_unipotent_lift (h := h) g hord
  refine gLAPPrimeCoreOf_eq_bot_of_framework' hZ hp g {q' | q' ∈ GenSet h N} ?_ ?_ ?_ ?_ ?_ H hH
    _ rfl
  · intro q' hq'
    rw [← hu1]
    exact GenSet_comm hu hq'
  · intro s q' hs hq'
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective s
    have hs' : (σ : primeFormP h (Cm n K)) * (u : primeFormP h (Cm n K)) =
        (u : primeFormP h (Cm n K)) * (σ : primeFormP h (Cm n K)) := by
      rw [hσ, hu1]
      exact hs
    have hσN := commute_lift hN hu hs'
    have := GenSet_conj hσN hq'
    rw [← hσ]
    exact this
  · intro q' hq' q'' hq''
    exact GenSet_p3 hp2 hq' hq''
  · intro s hs hcop hGen
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective s
    have hs' : (σ : primeFormP h (Cm n K)) * (u : primeFormP h (Cm n K)) =
        (u : primeFormP h (Cm n K)) * (σ : primeFormP h (Cm n K)) := by
      rw [hσ, hu1]
      exact hs
    have hcop' : (orderOf (σ : primeFormP h (Cm n K))).Coprime p := by
      rw [hσ]
      exact hcop
    have h1 := uniq_inner hn3 hp2 hN hN0 hUN hu σ hs' hcop' (by
      intro q0 hq0
      have h2 := hGen q0 hq0
      rw [hσ]
      exact h2)
    rw [hσ] at h1
    exact h1
  · intro α hα hfix
    refine uniq_out hn3 hp2 hN hN0 hUN hu α hα ?_
    intro q' hq'
    exact hfix q' (by rw [hu1] at hq'; exact hq')

end CFSG.HardMathSupport.Solomon.Coordinator
