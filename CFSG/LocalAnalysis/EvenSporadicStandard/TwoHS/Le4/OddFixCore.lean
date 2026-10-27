module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFixData

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.EvenSporadicStandard.HSStd (sqPt_iff gs_all_iff gs_all_iff2)

variable {n : ℕ}

theorem quartPt_iff {x : Tab} {X : Equiv.Perm (Fin n)} (hx : TabRep x X) :
    quartPt n x = true ↔ X ^ 4 = 1 := by
  rw [quartPt, sqPt_iff (hx.comp hx),
    show X ^ 4 = X * X * (X * X) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]

theorem quartPt2_iff {w x : Tab} {W X : Equiv.Perm (Fin n)} (hw : TabRep w W)
    (hx : TabRep x X) : quartPt2 n w x = true ↔ (W * X) ^ 4 = 1 := by
  rw [quartPt2, sqPt_iff ((hw.comp hx).comp (hw.comp hx)),
    show (W * X) ^ 4 = W * X * (W * X) * (W * X * (W * X)) by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]]

theorem quartCheck_spec {H : Subgroup (Equiv.Perm (Fin n))} {T : Array Tab}
    (hH : Enumerates H T.toList) {w : Tab} {W : Equiv.Perm (Fin n)} (hw : TabRep w W)
    {gs : Array Tab} {G : ℕ → Equiv.Perm (Fin n)} (hgs : ∀ j < gs.size, TabRep gs[j]! (G j))
    (h : quartCheck n T w gs = true) :
    (∀ y ∈ H, (∀ j < gs.size, y * G j = G j * y) → y ^ 4 = 1) ∧
      ∀ y ∈ H, (∀ j < gs.size, (W * y) * G j = G j * (W * y)) → (W * y) ^ 4 = 1 := by
  simp only [quartCheck, Array.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine ⟨fun y hy hc => ?_, fun y hy hc => ?_⟩
  · obtain ⟨k, hk, hr⟩ := hH.exists_pos hy
    rw [getElem!_pos T k hk] at hr
    rcases (h k hk).1 with h1 | h1
    · rw [Bool.eq_false_iff] at h1
      exact absurd ((gs_all_iff hgs hr).2 hc) h1
    · exact (quartPt_iff hr).1 h1
  · obtain ⟨k, hk, hr⟩ := hH.exists_pos hy
    rw [getElem!_pos T k hk] at hr
    rcases (h k hk).2 with h1 | h1
    · rw [Bool.eq_false_iff] at h1
      exact absurd ((gs_all_iff2 hgs hw hr).2 hc) h1
    · exact (quartPt2_iff hw hr).1 h1

end CFSG.EvenSporadicStandard.TwoHS
