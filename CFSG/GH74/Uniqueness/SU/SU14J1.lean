module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup
open scoped Pointwise

theorem alt5_two_group_comm {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (f : T →* alternatingGroup (Fin 5)) (hf : Function.Injective f) :
    ∀ a b : T, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  have hdvd : Nat.card T ∣ 60 := by
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Fintype.card_fin, Nat.factorial]
    rw [← hc]
    exact Subgroup.card_dvd_of_injective f hf
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    rw [← hk] at h8
    have := dvd_trans h8 hdvd
    omega
  interval_cases k
  · intro a b
    have : Nat.card T = 1 := by simpa using hk
    have hsub : Subsingleton T := (Nat.card_eq_one_iff_unique.mp this).1
    exact Subsingleton.elim _ _
  · intro a b
    have hc : IsCyclic T := isCyclic_of_prime_card (by simpa using hk)
    let _ : CommGroup T := IsCyclic.commGroup
    exact mul_comm a b
  · have hcomm : IsMulCommutative T := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hk
    exact fun a b => hcomm.is_comm.comm a b

end CFSG.GH74.Uniqueness.SU.SU14
