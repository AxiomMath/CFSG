module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwX0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwKer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Quasithin.H13.U43

theorem sw_core_noninvol {Λ : Type} [Group Λ] [Finite Λ] {τ : Λ →* X₀} (hτ : SwCentralTwo τ)
    (hone : X0OneClass) (hx : orderOf xElt = 2) (hO : SwOddCent) {A₁ A₂ : Subgroup Λ} {z : Λ}
    (S : SwSetup A₁ A₂ z) {y : Λ} (hyz : y ∈ Subgroup.zpowers z) (hy : Odd (orderOf y))
    (hy1 : y ≠ 1) : False := by
  classical
  obtain ⟨P, hP2, hbig, hPle⟩ := S.exists_big_two
  have hPcent : P ≤ Subgroup.centralizer ({z} : Set Λ) :=
    hPle.trans (sup_le S.pocket₁.le_cent S.pocket₂.le_cent)
  have hPcomm : ∀ p ∈ P, p * y = y * p := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
    intro p hp
    rw [← hk]
    have hcz : Commute p z := Subgroup.mem_centralizer_singleton_iff.mp (hPcent hp)
    exact hcz.zpow_right k
  let Q : Subgroup X₀ := P.map τ
  have hQ2 : IsPGroup 2 Q := hP2.map τ
  have hQcard : 16 ≤ Nat.card Q := by
    have h := hτ.card_le_map P
    change Nat.card P ≤ 2 * Nat.card Q at h
    omega
  have hyodd : Odd (orderOf (τ y)) := hy.of_dvd_nat (orderOf_map_dvd τ y)
  have hyne : τ y ≠ 1 := fun h => hy1 (hτ.eq_one_of_odd hy h)
  have hQcent : ∀ q ∈ Q, q * τ y = τ y * q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
    rw [← map_mul, hPcomm p hp, map_mul]
  exact sw_no_big_two_group hone hx hO hQ2 hQcard hyodd hyne hQcent

end CFSG.OddStandard.SmallF3.Omega
