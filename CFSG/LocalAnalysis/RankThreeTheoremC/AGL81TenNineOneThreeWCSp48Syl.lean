module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCSp48Grp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCSp48Mat

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

namespace Sp48

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F (F8)
open Subgroup

@[expose] noncomputable def tau0 : F8 := exists_tau.choose

theorem htau0 : tau0 ^ 3 + tau0 + 1 = 0 := exists_tau.choose_spec

@[expose] noncomputable def Ag : GL (Fin 2) F8 := ⟨amat tau0, amatInv tau0, amat_mul_inv, amatInv_mul⟩

@[expose] noncomputable def Jg : GL (Fin 2) F8 := ⟨jmat, jmat, jmat_mul_self, jmat_mul_self⟩

theorem Ag_pow_nine : Ag ^ 9 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; exact amat_pow_nine htau0)

theorem Ag_pow_three_ne : Ag ^ 3 ≠ 1 := fun h => amat_pow_three_ne_one htau0 (by
  have := congrArg Units.val h
  rwa [Units.val_pow_eq_pow_val] at this)

theorem orderOf_Ag : orderOf Ag = 9 := by
  have hd : orderOf Ag ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one Ag_pow_nine
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  interval_cases k
  · have h1 : Ag = 1 := orderOf_eq_one_iff.1 (by simpa using hk')
    exact absurd (by rw [h1, one_pow]) Ag_pow_three_ne
  · have h3 : Ag ^ 3 = 1 := by
      have h := pow_orderOf_eq_one Ag
      rwa [hk', pow_one] at h
    exact absurd h3 Ag_pow_three_ne
  · simpa using hk'

theorem Jg_conj_Ag : Jg * Ag * Jg⁻¹ = Ag⁻¹ :=
  Units.ext (by show jmat * amat tau0 * jmat = amatInv tau0; exact jmat_conj_amat)

theorem Jg_conj_mem {x : GL (Fin 2) F8} (hx : x ∈ zpowers Ag) : Jg * x * Jg⁻¹ = x⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← conj_zpow, Jg_conj_Ag, inv_zpow]

theorem det_Ag : Matrix.GeneralLinearGroup.det Ag = 1 :=
  Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_amat)

theorem det_mem_zpowers {x : GL (Fin 2) F8} (hx : x ∈ zpowers Ag) :
    (x : Matrix (Fin 2) (Fin 2) F8).det = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have h : Matrix.GeneralLinearGroup.det (Ag ^ k) = 1 := by rw [map_zpow, det_Ag, one_zpow]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]

@[expose] noncomputable def T0' : Subgroup (GL Ix F8) := ((zpowers Ag).prod (zpowers Ag)).map psi

theorem T0'_le : T0' ≤ StatedSp 2 F8 := by
  rintro _ ⟨p, ⟨h1, h2⟩, rfl⟩
  exact psi_mem (det_mem_zpowers h1) (det_mem_zpowers h2)

@[expose] noncomputable def T0 : Subgroup ↥(StatedSp 2 F8) := T0'.subgroupOf (StatedSp 2 F8)

theorem card_T0' : Nat.card T0' = 81 := by
  rw [T0', Subgroup.card_map_of_injective psi_injective,
    Nat.card_congr (Subgroup.prodEquiv (zpowers Ag) (zpowers Ag)).toEquiv, Nat.card_prod,
    Nat.card_zpowers, orderOf_Ag]

theorem card_T0 : Nat.card T0 = 81 := by
  rw [T0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0'_le).toEquiv, card_T0']

@[expose] noncomputable def wS : ↥(StatedSp 2 F8) := ⟨wU, wU_mem⟩

@[expose] noncomputable def dS : ↥(StatedSp 2 F8) :=
  ⟨psi (Jg, 1), psi_mem det_jmat (by simp)⟩

theorem mem_T0_iff {s : ↥(StatedSp 2 F8)} : s ∈ T0 ↔ (s : GL Ix F8) ∈ T0' :=
  Subgroup.mem_subgroupOf

end Sp48

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
