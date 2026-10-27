module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0PlaneX
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.CocodeFacts

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

section Masks


theorem epsListFrom_smul_planeXN (k : ℕ) :
    ∀ (s m i : ℕ), s + k ≤ 11 → i < 891 →
      maskAct (epsTabsFrom (planeTabs ()) k s) m i < 891 ∧
      maskProd (epsListFrom k s) m • planeXN i =
        planeXN (maskAct (epsTabsFrom (planeTabs ()) k s) m i) := by
  induction k with
  | zero =>
    intro s m i _ hi
    simp only [epsTabsFrom, epsListFrom, maskAct, maskProd_nil, one_smul]
    exact ⟨hi, trivial⟩
  | succ k ih =>
    intro s m i hsk hi
    obtain ⟨hlt, hsm⟩ := ih (s + 1) (m / 2) i (by omega) hi
    have hs : s < 11 := by omega
    simp only [epsTabsFrom, epsListFrom, maskAct, maskProd_cons]
    by_cases hm : m % 2 = 1
    · simp only [if_pos hm]
      refine ⟨planeTabs_lt (s := 2 + s) (by omega) hlt, ?_⟩
      rw [mul_smul, hsm, epsAt_of_lt hs, ← planeGen_eps hs,
        planeGen_smul_planeXN (by omega) hlt]
    · simp only [if_neg hm, one_mul]
      exact ⟨hlt, hsm⟩

theorem epsMask_smul_planeXN (m : ℕ) {i : ℕ} (hi : i < 891) :
    epsMask m • planeXN i = planeXN (maskAct (epsTabsFrom (planeTabs ()) 11 0) m i) :=
  (epsListFrom_smul_planeXN 11 0 m i (by norm_num) hi).2

theorem eq_of_epsMask_fix {m : ℕ} (hm : m < 2 ^ 11)
    (h : ∀ i : Fin 891, epsMask m • planeX i = planeX i) :
    m = 0 ∨ m = 256 ∨ m = 1216 ∨ m = 1472 := by
  have hfix : m ∈ fixMasks (planeTabs ()) := by
    simp only [fixMasks, List.mem_filter, List.mem_range]
    refine ⟨by simpa using hm, allIn_zero_iff.2 fun i hi => ?_⟩
    have h1 := epsListFrom_smul_planeXN 11 0 m i (by norm_num) hi
    have h2 := h ⟨i, hi⟩
    change epsMask m • planeXN i = planeXN i at h2
    rw [epsMask_smul_planeXN m hi] at h2
    rw [beq_iff_eq]
    exact planeXN_inj h1.1 hi h2
  rw [planesFacts.masks] at hfix
  simpa [fixMasksExpected] using hfix

end Masks

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
