module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Steps2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10D_basic [Finite G] (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    t * t = 1 ∧ z * z = 1 ∧ t ≠ 1 ∧ z ≠ 1 ∧ t ≠ z ∧ t * z = z * t := by
  obtain ⟨-, -, htL, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hctx.involution] at h
    simpa [pow_two] using h
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hctx.toSec10Z.pocket.1] at h
    simpa [pow_two] using h
  have ht1 : t ≠ 1 := by
    intro h
    have hinv : orderOf (1 : G) = 2 := by simpa only [h] using hctx.involution
    rw [orderOf_one] at hinv
    exact absurd hinv (by norm_num)
  have hz1 : z ≠ 1 := by
    intro h
    have hinv : orderOf (1 : G) = 2 := by simpa only [h] using hctx.toSec10Z.pocket.1
    rw [orderOf_one] at hinv
    exact absurd hinv (by norm_num)
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hctx.pocket1.2.1 hctx.pocket1.1)).1
  exact ⟨ht2, hz2, ht1, hz1, fun h => htL (h ▸ hzL), hctx.central t htS⟩

theorem sec10D_g_comm_z [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hz2 : z * z = 1) (hctx : Sec109Ctx G t L S z K1 K2 g) : g * z = z * g := by
  have hu : g * z * g⁻¹ * z⁻¹ ∈ oddCoreIn (secK0 t z) := hctx.comm2 z hctx.pocket2.1
  have hK0le : secK0 t z ≤ centralizer ({z} : Set G) := by
    unfold secK0 oTwoRes
    rw [Subgroup.closure_le]
    intro x hx
    exact (Subgroup.mem_inf.mp hx.1).2
  have huC : g * z * g⁻¹ * z⁻¹ ∈ centralizer ({z} : Set G) :=
    hK0le (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hu)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have huz : (g * z * g⁻¹ * z⁻¹) * z = z * (g * z * g⁻¹ * z⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp huC
  rw [hzi] at huz hu
  have hz'sq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hcomm : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
    have h1 : (g * z * g⁻¹) * z * z = z * ((g * z * g⁻¹) * z) := by
      simpa only [mul_assoc] using huz
    calc (g * z * g⁻¹) * z = (g * z * g⁻¹) * z * z * z := by
          rw [mul_assoc _ z z, hz2, mul_one]
      _ = z * ((g * z * g⁻¹) * z) * z := by rw [h1]
      _ = z * (g * z * g⁻¹) := by rw [mul_assoc, mul_assoc _ z z, hz2, mul_one]
  have hu2 : (g * z * g⁻¹ * z) * (g * z * g⁻¹ * z) = 1 := by
    calc (g * z * g⁻¹ * z) * (g * z * g⁻¹ * z)
        = (g * z * g⁻¹) * (z * (g * z * g⁻¹)) * z := by simp only [mul_assoc]
      _ = (g * z * g⁻¹) * ((g * z * g⁻¹) * z) * z := by rw [hcomm]
      _ = ((g * z * g⁻¹) * (g * z * g⁻¹)) * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [hz'sq, hz2, mul_one]
  have hord2 : orderOf (g * z * g⁻¹ * z) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2)
  have hordodd : Odd (orderOf (g * z * g⁻¹ * z)) :=
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (secK0 t z)).of_dvd_nat
      ((oddCoreIn (secK0 t z)).orderOf_dvd_natCard hu)
  have hord1 : orderOf (g * z * g⁻¹ * z) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h1 | h2
    · exact h1
    · rw [h2] at hordodd
      exact absurd hordodd (by norm_num)
  have h1 : g * z * g⁻¹ * z = 1 := orderOf_eq_one_iff.mp hord1
  have h2 : g * z * g⁻¹ = z := by
    have := congrArg (· * z) h1
    simpa [mul_assoc, hz2] using this
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h2]

theorem sec10D_T_pgroup [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g) : IsPGroup 2 ↥(S ⊔ zpowers g) :=
  IsPGroup.to_sup_of_normal_left' hctx.sylow.2.1 hctx.two (Subgroup.zpowers_le.mpr hctx.norm)

theorem sec10D_T_le_H [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hz2 : z * z = 1) (hctx : Sec109Ctx G t L S z K1 K2 g) :
    S ⊔ zpowers g ≤ centralizer ({z} : Set G) := by
  refine sup_le (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hs)) ?_
  exact Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_singleton_iff.mpr (sec10D_g_comm_z hz2 hctx))

theorem sec10D_T_cent_t [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g) :
    (S ⊔ zpowers g) ⊓ centralizer ({t} : Set G) = S := by
  refine le_antisymm ?_ (le_inf le_sup_left hctx.sylow.1)
  exact (hctx.sylow.eq_of_le inf_le_right (sec10D_T_pgroup hctx).to_inf_left
    (le_inf le_sup_left hctx.sylow.1)).le

end CFSG.OddStandard.SmallF3.Omega
