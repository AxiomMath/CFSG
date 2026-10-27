module

public import CFSG.GH74.GLS.IVK.Proofs2.Pgl2Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter (PSL2 PGL2 IsOddPrimePower)

theorem sec5sh8_q3_not_psl {X : Type} [Group X] [Finite X] (P : Sylow 2 X)
    (hP : Nonempty (↥P ≃* DihedralGroup 4)) {F : Type} [Field F] [Finite F]
    (h3 : Nat.card F = 3) : ¬ Nonempty (X ≃* PSL2 F) := by
  rintro ⟨e⟩
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨3, 1, Nat.prime_three, ⟨1, by norm_num⟩, le_rfl, by rw [h3]; norm_num⟩
  have hcardPSL : Nat.card (PSL2 F) = 12 := by
    rw [CFSG.GorensteinWalter.psl2_card_formula F hodd, h3]
    norm_num
  have hX : Nat.card X = 12 := by
    rw [Nat.card_congr e.toEquiv, hcardPSL]
  obtain ⟨eP⟩ := hP
  have hPcard : Nat.card ↥P = 8 := by
    rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have hdvd : Nat.card ↥P ∣ Nat.card X :=
    Subgroup.card_subgroup_dvd_card (P : Subgroup X)
  rw [hPcard, hX] at hdvd
  omega

theorem sec5sh8_q3_pgl {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    (h3 : Nat.card F = 3) (e : X ≃* PGL2 F) : Nonempty (X ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨e'⟩ := CFSG.GH74.GLS.IVK.Proofs2.exists_pgl2_equiv_perm (F := F) h3
  exact ⟨e.trans e'⟩

theorem sec5sh8_five_le_of_ne_three {q : ℕ} (hq : IsOddPrimePower q) (h3 : q ≠ 3) : 5 ≤ q := by
  rcases hq with ⟨p, n, hp, hpodd, hn, hqeq⟩
  have hp3 : 3 ≤ p := by
    rcases hpodd with ⟨k, hk⟩
    have := hp.two_le
    omega
  by_cases hp5 : 5 ≤ p
  · have hle : p ^ 1 ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
    rw [pow_one, ← hqeq] at hle
    omega
  · rcases hpodd with ⟨k, hk⟩
    have hp_eq : p = 3 := by omega
    rw [hp_eq] at hqeq
    by_cases hn2 : 2 ≤ n
    · have hle : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have hq9 : 9 ≤ q := by
        rw [hqeq]
        simpa using hle
      omega
    · have hn1 : n = 1 := by omega
      rw [hn1] at hqeq
      exact absurd (by rw [hqeq]; norm_num) h3

end CFSG.OddStandard.SmallF3.Omega
