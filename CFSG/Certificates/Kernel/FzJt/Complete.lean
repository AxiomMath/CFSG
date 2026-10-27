module

public import Certificates.Data.FzJtCheck
import all Certificates.Data.FzJ36

public section

namespace CFSG.KC.FzJt

open Certificates.FzJ36 Certificates.FzFus Certificates.FzJt

theorem fzJCheck_of (u : Model) (h : ¬ MJ u) : fzJCheck u () = true := by
  unfold fzJCheck cvPairs
  refine List.all_eq_true.mpr fun p hp => List.all_eq_true.mpr fun w hw => ?_
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
  dsimp only
  simp only [sqrtList, centList, List.mem_filter, kq_eq_true, allModel_mem, true_and] at hv hw
  cases hwv : kq (w * v * w⁻¹) v⁻¹
  · rfl
  refine Bool.or_eq_true_iff.mpr (Or.inr (List.all_eq_true.mpr fun y hy => ?_))
  simp only [centListOf, centList, List.mem_filter, kq_eq_true, allModel_mem, true_and] at hy
  cases hyw : kq (y * w) (w * y)
  · rfl
  cases hy1 : kq (y * y) 1
  · cases hy2 : kq (y * y) (u * u)
    · exact absurd ⟨y, v, w, hy.1, hv.1, hw.1,
        fun hc => by rw [(kq_eq_true).mpr hc] at hy1; exact Bool.noConfusion hy1,
        fun hc => by rw [(kq_eq_true).mpr hc] at hy2; exact Bool.noConfusion hy2,
        hv.2, hw.2, (kq_eq_true).mp hwv, hy.2, (kq_eq_true).mp hyw⟩ h
    · simp
  · simp

theorem f2Check_of (h : F2Fact) : f2Check () = true := by
  unfold f2Check
  refine List.all_eq_true.mpr fun q hq => fzJCheck_of _ (h q ?_)
  simpa [f2Reps] using hq

theorem sixQ_sq : ∀ q ∈ sixQ, q * q = QuaternionGroup.a 2 := by
  decide

theorem f3Check_of (h : F3Fact) : f3Check () = true := by
  unfold f3Check
  refine List.all_eq_true.mpr fun q hq => List.all_eq_true.mpr fun v hv =>
    List.all_eq_true.mpr fun w hw => ?_
  simp only [centInv, List.mem_filter, Bool.and_eq_true, isInvB_iff, kb_iff] at hv hw
  by_cases h1 : KEq v w
  · simp [kb_iff.mpr h1]
  by_cases h2 : KEq (v * w) (w * v)
  · rcases h q (sixQ_sq q hq) v w hv.2.1 hw.2.1 hv.2.2 hw.2.2 h1 h2 with h3 | h3 | h3 <;>
      simp [inZb_iff.mpr h3]
  · simp [kb_eq_false.mpr h2]

theorem f4Check_of (h : F4Fact) : f4Check () = true := by
  unfold f4Check
  refine List.all_eq_true.mpr fun n _ => ?_
  by_cases h1 : KEq (n * n) z3M
  swap
  · simp [kb_eq_false.mpr h1]
  by_cases h2 : ∀ q : Q8, ¬ KEq n (mkE 1 1 q)
  swap
  · simp only [not_forall, not_not] at h2
    obtain ⟨q, hq⟩ := h2
    have hA : ((allQ ()).all fun q => !kb n (mkE 1 1 q)) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      have := List.all_eq_true.mp hc q (allQ_mem q)
      simp [kb_iff.mpr hq] at this
    simp [hA]
  by_cases h3 : n.right = 1 → ∃ q : Q8, ∃ z ∈ zs4 (), KEq n (mkE 1 1 q * z)
  swap
  · simp only [not_imp, not_exists, not_and] at h3
    obtain ⟨hr, hno⟩ := h3
    have hB : ((allQ ()).any fun q => (zs4 ()).any fun z => kb n (mkE 1 1 q * z)) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨q, -, hc⟩ := List.any_eq_true.mp hc
      obtain ⟨z, hz, hc⟩ := List.any_eq_true.mp hc
      exact hno q z hz (kb_iff.mp hc)
    simp [hr, hB]
  obtain ⟨v, w, hvc, hwc, hvI, hwI, hvw, hc, hvZ, hwZ, hvwZ⟩ := h n h1 h2 h3
  have hv : v ∈ centInvNZ (allM ()) (zList ()) n := by
    simp only [centInvNZ, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨allM_mem v, ⟨isInvB_iff.mpr hvI, kb_iff.mpr hvc⟩, inZb_eq_false.mpr hvZ⟩
  have hw : w ∈ centInvNZ (allM ()) (zList ()) n := by
    simp only [centInvNZ, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨allM_mem w, ⟨isInvB_iff.mpr hwI, kb_iff.mpr hwc⟩, inZb_eq_false.mpr hwZ⟩
  have hD : ((centInvNZ (allM ()) (zList ()) n).any fun v =>
      (centInvNZ (allM ()) (zList ()) n).any fun w =>
        !kb v w && kb (v * w) (w * v) && !inZb (zList ()) (v * w)) = true :=
    List.any_eq_true.mpr ⟨v, hv, List.any_eq_true.mpr ⟨w, hw, by
      simp [kb_eq_false.mpr hvw, kb_iff.mpr hc, inZb_eq_false.mpr hvwZ]⟩⟩
  simp [hD]

theorem fzJtCheck_of (h2 : F2Fact) (h3 : F3Fact) (h4 : F4Fact) : fzJtCheck () = true := by
  simp only [fzJtCheck, f2Check_of h2, f3Check_of h3, f4Check_of h4, Bool.and_self]

end CFSG.KC.FzJt
