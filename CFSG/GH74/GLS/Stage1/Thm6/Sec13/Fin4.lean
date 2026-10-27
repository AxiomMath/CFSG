module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.SylowB
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem eq_of_sylow_le {C P' T : Subgroup G} [Finite G] (hT : Sylow2In T C) (hP'C : P' ≤ C)
    (hTP' : T ≤ P') (hP' : IsPGroup 2 ↥P') : P' = T := by
  have hrel := relIndex_mul_relIndex T P' C hTP' hP'C
  have hodd : ¬ 2 ∣ T.relIndex P' := fun hd => hT.2.2 (hrel ▸ Dvd.dvd.mul_right hd _)
  have hc := relIndex_mul_card T P'
  rw [inf_of_le_left hTP'] at hc
  obtain ⟨e, he⟩ := hP'.exists_card_eq
  have hdvd : T.relIndex P' ∣ 2 ^ e := by
    rw [← he, ← hc]
    exact Dvd.intro _ rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    apply hodd
    rw [hj]
    exact dvd_pow_self 2 hne
  rw [hj0, pow_zero, relIndex_eq_one] at hj
  exact le_antisymm hj hTP'

theorem card_eq_of_sylow {C P Q : Subgroup G} [Finite G] (hP : Sylow2In P C)
    (hQ : Sylow2In Q C) : Nat.card Q = Nat.card P := by
  obtain ⟨c, -, hc⟩ := SylowIn.conj (p := 2) (P := P) (Q := Q) (C := C) hP hQ
  have : Q = cj c P := by
    ext g
    rw [mem_cj]
    exact hc g
  rw [this, card_cj]

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
