module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem invariant_chief_series {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal] :
    ∃ (m : ℕ) (Ns : Fin (m + 1) → Subgroup G), Ns 0 = ⊥ ∧ Ns (Fin.last m) = N ∧
      (∀ i, (Ns i).Normal) ∧
      (∀ i : Fin m, Ns i.castSucc < Ns i.succ ∧
        ∀ Z : Subgroup G, Z.Normal → ¬ (Ns i.castSucc < Z ∧ Z < Ns i.succ)) ∧
      (N = ⊥ → m = 0) := by
  obtain ⟨r, f, hf0, hfr, hfn, hfc⟩ := CFSG.exists_chief_series_from_to N inferInstance
  have hstep : ∀ i : Fin r, f (r - i) < f (r - (i + 1)) ∧
      ∀ Z : Subgroup G, Z.Normal → ¬ (f (r - i) < Z ∧ Z < f (r - (i + 1))) := by
    intro i
    have hj : r - (i + 1) < r := by omega
    have hjs : r - (i + 1) + 1 = r - i := by omega
    have hc := hfc (r - (i + 1)) hj
    rw [hjs] at hc
    refine ⟨hc.lt, fun Z hZ ⟨h1, h2⟩ => ?_⟩
    rcases hc.is_maximal Z hZ h1.le h2.le with h | h
    · exact h1.ne h.symm
    · exact h2.ne h
  refine ⟨r, fun i => f (r - i), ?_, ?_, fun i => hfn _ (by omega), fun i => ?_, fun hN => ?_⟩
  · simpa using hfr
  · simpa using hf0
  · simpa only [Fin.val_castSucc, Fin.val_succ] using hstep i
  · by_contra hr
    have hlt := (hstep ⟨r - 1, by omega⟩).1
    rw [show r - (r - 1 + 1) = 0 by omega, hf0, hN] at hlt
    exact not_lt_bot hlt

end CFSG.GroupTheory.SteinbergBK
