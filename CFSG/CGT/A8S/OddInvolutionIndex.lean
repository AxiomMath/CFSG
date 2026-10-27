module

public import CFSG.CGT.A8S.TopPerm

public section

namespace CFSG.GroupTheory

open Equiv Equiv.Perm CFSG.CGT.A8S.Perm8 in
theorem four_dvd_index_centralizer_of_sign_eq_neg_one {σ : Perm (Fin 8)} (h2 : σ ^ 2 = 1)
    (hs : sign σ = -1) : 4 ∣ (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))).index := by
  have h1 : σ ≠ 1 := fun h => by rw [h, map_one] at hs; exact absurd hs (by decide)
  obtain ⟨k, hk, hk1, hk4⟩ := cycleType_eq_replicate h2 h1
  have hkodd : Odd k := by
    rw [sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul] at hs
    rcases Nat.even_or_odd k with he | ho
    · exfalso
      have heven : Even (k * 2 + k) := by
        rw [Nat.even_iff] at he ⊢
        omega
      rw [heven.neg_one_pow] at hs
      exact absurd hs (by decide)
    · exact ho
  have hc := card_centralizer_perm hk (by omega)
  have hidx := Subgroup.card_mul_index (Subgroup.centralizer ({σ} : Set (Perm (Fin 8))))
  rw [hc, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hidx
  obtain ⟨m, hm⟩ := hkodd
  have hk' : k = 1 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl
  · norm_num [Nat.factorial] at hidx
    omega
  · norm_num [Nat.factorial] at hidx
    omega

end CFSG.GroupTheory
