module

public import Certificates.Data.Kernel.Misc.L52Fast

public section

namespace CFSG.KC.L52

open CFSG.Quasithin.H13.KGE64 CFSG.KD.L52

theorem all_of_covers {P Q : List Nat} (h : coversN P Q = true) (u : Nat)
    (hQ : ((List.range' 1 6).all fun i => isUTN (cj5N Q u i)) = true) :
    ((List.range' 1 6).all fun i => isUTN (cj5N P u i)) = true := by
  rw [List.all_eq_true] at hQ ⊢
  intro i hi
  unfold coversN at h
  rw [List.all_eq_true] at h
  obtain ⟨i', hi', he⟩ := List.any_eq_true.1 (h i hi)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at he
  have e : cj5N P u i = cj5N Q u i' := by
    unfold cj5N
    rw [he.1, he.2]
  rw [e]
  exact hQ i' hi'

theorem candN_eq_of_covers {P Q : List Nat} (h1 : coversN P Q = true) (h2 : coversN Q P = true) :
    candN P = candN Q := by
  unfold candN
  refine List.filter_congr fun u _ => ?_
  rw [Bool.eq_iff_iff]
  exact ⟨all_of_covers h2 u, all_of_covers h1 u⟩

theorem l52StepN_eq (Y k : Nat) : l52StepN Y k = pairN (pwN Y k) (candN (pwN Y k)) := rfl

theorem l52CheckYN_of_F {Y : Nat} (h : l52CheckYFN Y = true) : l52CheckYN Y = true := by
  unfold l52CheckYFN at h
  unfold l52CheckYN
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have hs := h k hk
  unfold l52StepFN at hs
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  rw [l52StepN_eq, candN_eq_of_covers hs.1.1 hs.1.2]
  exact hs.2

theorem l52CheckN_of_F (h : l52CheckFN = true) : l52CheckN = true := by
  unfold l52CheckFN at h
  unfold l52CheckN
  rw [List.all_eq_true] at h ⊢
  intro j hj
  have hs := h j hj
  rw [Bool.and_eq_true] at hs ⊢
  exact ⟨hs.1, l52CheckYN_of_F hs.2⟩

end CFSG.KC.L52

end
