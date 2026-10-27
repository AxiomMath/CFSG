module

public import CFSG.LargeExtraspecial.OutSixUnitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.LargeExtraspecial.FS77

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LinearGroups

theorem factorization_card_unitarySU_two_one {m : ℕ} (hm : 1 ≤ m) :
    (Nat.card (unitarySU 2 1 (GaloisField 2 2) m)).factorization 2 = m * (m - 1) / 2 := by
  have h := S14.unitaryFieldData_two_one
  have hB := gramForm_isSymm h (G := (1 : Matrix (Fin m) (Fin m) (GaloisField 2 2))) (by
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one])
  have hBl := gramForm_separatingLeft h (G := (1 : Matrix (Fin m) (Fin m) (GaloisField 2 2)))
    (by simp)
  have hSU := (unitary_full_group_order h hB hBl (Module.finrank_fin_fun _) hm).2.2.2.2.2.2
  rw [← card_gramSU, ← unitarySU_eq_gramSU h, pow_one] at hSU
  exact Nat.pow_right_injective le_rfl hSU

theorem factorization_card_timmesfeldPSU_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    (Nat.card (timmesfeldPSU m)).factorization 2 = m * (m - 1) / 2 := by
  have h := S14.unitaryFieldData_two_one
  have hSZ := Subgroup.card_eq_card_quotient_mul_card_subgroup (unitaryScalars h m)
  rw [card_unitaryScalars h hm] at hSZ
  have hSU0 : Nat.card (unitarySU 2 1 (GaloisField 2 2) m) ≠ 0 := Nat.card_pos.ne'
  rw [hSZ] at hSU0
  have hodd : (Nat.gcd m (2 ^ 1 + 1)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h2 => by
      have := h2.trans (Nat.gcd_dvd_right m (2 ^ 1 + 1))
      omega
  have hfac := factorization_card_unitarySU_two_one hm
  rw [hSZ, Nat.factorization_mul (left_ne_zero_of_mul hSU0) (right_ne_zero_of_mul hSU0),
    Finsupp.add_apply, hodd, add_zero] at hfac
  rw [Nat.card_congr (S14.timmesfeldPSUEquiv hm).toEquiv]
  exact hfac

theorem factorization_card_timmesfeldPSU {m : ℕ} (hm : 4 ≤ m) :
    (Nat.card (timmesfeldPSU m)).factorization 2 = m * (m - 1) / 2 :=
  factorization_card_timmesfeldPSU_of_one_le (by omega)

theorem two_pow_le_of_mulEquiv_timmesfeldPSU {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hm : 4 ≤ m) (e : G ≃* timmesfeldPSU m) (H : Subgroup G) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card H) : k ≤ m * (m - 1) / 2 := by
  have hG := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
    (hk.trans (Subgroup.card_subgroup_dvd_card H))
  rwa [Nat.card_congr e.toEquiv, factorization_card_timmesfeldPSU hm] at hG

end CFSG.LargeExtraspecial.FS77
