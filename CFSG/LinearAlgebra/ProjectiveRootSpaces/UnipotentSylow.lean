module

public import CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData

public section

namespace CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSylow

open scoped MatrixGroups
open CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

private theorem card_SL (hp : 5 ≤ p) (hn : 1 < n) :
    Nat.card SL(2, GaloisField p n) = p ^ n * ((p ^ n) ^ 2 - 1) := by
  have hn0 : n ≠ 0 := by omega
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p n hn0
  have hq1 : 2 ≤ p ^ n := by
    calc 2 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have key : (∏ i : Fin 2, ((p ^ n) ^ 2 - (p ^ n) ^ (i : ℕ))) =
      ((p ^ n) - 1) * (p ^ n * ((p ^ n) ^ 2 - 1)) := by
    generalize p ^ n = q at hq1
    rw [Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have h1 : q ^ 2 - q = q * (q - 1) := by
      rw [pow_two, Nat.mul_sub, mul_one]
    have h2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [(by omega : 1 ≤ q), this]; ring
    rw [h1, h2]; ring
  have := Matrix.card_SL_field (n := 2) (𝔽 := GaloisField p n)
  rw [this, hq, key]
  have : 0 < p ^ n - 1 := by omega
  exact Nat.mul_div_cancel_left _ this

private theorem card_center (hp : 5 ≤ p) (hn : 1 < n) :
    Nat.card (Subgroup.center SL(2, GaloisField p n)) = 2 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
  have h : IsPrimitiveRoot (-1 : GaloisField p n) 2 := IsPrimitiveRoot.neg_one p (by omega)
  have hm : max (Fintype.card (Fin 2)) 1 = 2 := by simp
  rw [hm]
  exact IsPrimitiveRoot.card_rootsOfUnity h

theorem card_PSL (hp : 5 ≤ p) (hn : 1 < n) :
    Nat.card PSL(2, GaloisField p n) * 2 = p ^ n * ((p ^ n) ^ 2 - 1) := by
  have h1 := card_SL p n hp hn
  have h2 := card_center p n hp hn
  have h3 := Subgroup.card_mul_index (Subgroup.center SL(2, GaloisField p n))
  have h4 : Nat.card PSL(2, GaloisField p n) =
      (Subgroup.center SL(2, GaloisField p n)).index := rfl
  rw [h1, h2] at h3
  omega

theorem card_upperSubgroup (hn : 1 < n) :
    Nat.card (upperSubgroup (GaloisField p n)) = p ^ n := by
  haveI : Finite (GaloisField p n) := inferInstance
  rw [upperSubgroup_card_of_finite]
  exact GaloisField.card p n (by omega)

theorem isPGroup_upperSubgroup (hn : 1 < n) :
    IsPGroup p (upperSubgroup (GaloisField p n)) :=
  IsPGroup.of_card (card_upperSubgroup p n hn)

theorem upperSubgroup_isSylow (hp : 5 ≤ p) (hn : 1 < n) :
    ∃ P : Sylow p PSL(2, GaloisField p n),
      (P : Subgroup PSL(2, GaloisField p n)) = upperSubgroup (GaloisField p n) := by
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow (isPGroup_upperSubgroup p n hn)
  refine ⟨P, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge hP
  rw [card_upperSubgroup p n hn]
  have hpp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
  have hdvd : Nat.card (P : Subgroup PSL(2, GaloisField p n)) ∣
      Nat.card PSL(2, GaloisField p n) := Subgroup.card_subgroup_dvd_card _
  have hdvd2 : p ^ k ∣ p ^ n * ((p ^ n) ^ 2 - 1) := by
    rw [← hk, ← card_PSL p n hp hn]
    exact Dvd.dvd.mul_right hdvd 2
  have hcop : Nat.Coprime (p ^ k) ((p ^ n) ^ 2 - 1) := by
    apply Nat.Coprime.pow_left
    rw [hpp.coprime_iff_not_dvd]
    intro h
    have h' : p ∣ (p ^ n) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
    have h1p : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow _ _ (pow_pos hpp.pos _)
    have := Nat.dvd_sub h' h
    rw [show (p ^ n) ^ 2 - ((p ^ n) ^ 2 - 1) = 1 by omega] at this
    exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
  have := hcop.dvd_of_dvd_mul_right hdvd2
  rw [hk]
  exact Nat.le_of_dvd (pow_pos hpp.pos _) this

end CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSylow
