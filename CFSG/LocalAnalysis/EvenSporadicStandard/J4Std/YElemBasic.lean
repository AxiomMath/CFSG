module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YInterface
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.EvenSporadicStandard.J4Std.YElem

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G}

section PhiOnW

variable (hS : Setting L z) (hD : LocalData L U T0)
include hS hD

theorem sq_mem_U (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) {w : G}
    (hw : w ∈ Csub U z) : w * w ∈ U := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hphi : phiVal z (w * w) = 1 := by
    rw [phiVal_mul hS hD hw hw]
    exact hD.U_sq _ (phiVal_mem hS hD (mem_Csub.1 hw).1)
  have hV := Csub_comm_mem_V hS hD (mul_mem hw hw) ((phiVal_eq_one_iff hS).1 hphi)
  obtain ⟨u, hu, hwu⟩ := (mem_Vsub_iff hS hUL).1 hV
  rcases hwu with hwu | hwu
  · rw [hwu]; exact hu
  · exfalso
    obtain ⟨n, -, hn⟩ := htrans u hu
    exact hS.not_isConj_of_sq ⟨w, rfl⟩ (isConj_iff.2 ⟨n, by rw [hn, hwu]⟩)

theorem phi_surj [Finite G] (hW : Nat.card (Csub U z) = 2 ^ 23) {u : G} (hu : u ∈ U) :
    ∃ w ∈ Csub U z, phiVal z w = u := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  let φ := phiHom hS hD
  have hrangeU : φ.range ≤ U := by
    rintro _ ⟨c, rfl⟩
    exact phiVal_mem hS hD (mem_Csub.1 c.2).1
  have hinv : ∀ h ∈ Hloc L U, ∀ d ∈ φ.range, h * d * h⁻¹ ∈ φ.range := by
    rintro h hh _ ⟨c, rfl⟩
    obtain ⟨hc', hphi⟩ := phiVal_conj hS hD hh c.2
    exact ⟨⟨h * c * h⁻¹, hc'⟩, hphi⟩
  rcases hD.irred φ.range hrangeU hinv with hbot | htop
  · exfalso
    have hle : Csub U z ≤ Vsub U z := by
      intro c hc
      have h1 : phiVal z c = 1 := by
        have : φ ⟨c, hc⟩ ∈ φ.range := ⟨⟨c, hc⟩, rfl⟩
        rw [hbot] at this
        exact mem_bot.1 this
      exact Csub_comm_mem_V hS hD hc ((phiVal_eq_one_iff hS).1 h1)
    have := Subgroup.card_le_of_le hle
    rw [hW, card_Vsub hS hUL, hD.card_U] at this
    norm_num at this
  · have : u ∈ φ.range := by rw [htop]; exact hu
    obtain ⟨c, hc⟩ := this
    exact ⟨c.1, c.2, hc⟩

variable {Y : Subgroup G} (hY : YStruct L U z Y)
include hY

theorem mem_U_of_phiVal_eq_one {y : G} (hy : y ∈ Y) (h1 : phiVal z y = 1) : y ∈ U := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hV := Csub_comm_mem_V hS hD (hY.le_W hy) ((phiVal_eq_one_iff hS).1 h1)
  obtain ⟨u, hu, hyu⟩ := (mem_Vsub_iff hS hUL).1 hV
  rcases hyu with hyu | hyu
  · rw [hyu]; exact hu
  · exfalso
    apply hY.z_not_mem
    have : z = y * u⁻¹ := by rw [hyu, mul_inv_cancel_right]
    rw [this]
    exact Y.mul_mem hy (Y.inv_mem (hY.U_le hu))

theorem exists_phiVal_eq [Finite G] (hW : Nat.card (Csub U z) = 2 ^ 23) {u : G} (hu : u ∈ U) :
    ∃ y ∈ Y, phiVal z y = u := by
  obtain ⟨w, hw, hwu⟩ := phi_surj hS hD hW hu
  rcases hY.cover w hw with h | h
  · exact ⟨w, h, hwu⟩
  · refine ⟨z * w, h, ?_⟩
    have hzW : z ∈ Csub U z := V_le_Csub hS hD z_mem_V
    rw [phiVal_mul hS hD hzW hw, (phiVal_eq_one_iff hS).2 rfl, one_mul, hwu]

end PhiOnW

def omegaSub (Y : Subgroup G) (hab : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) : Subgroup G where
  carrier := {y | y ∈ Y ∧ y * y = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨Y.mul_mem ha hb, ?_⟩
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab b hb a ha]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨Y.one_mem, one_mul 1⟩
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    refine ⟨Y.inv_mem ha, ?_⟩
    rw [← mul_inv_rev, ha2, inv_one]

theorem mem_omegaSub {Y : Subgroup G} {hab : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y} {y : G} :
    y ∈ omegaSub Y hab ↔ y ∈ Y ∧ y * y = 1 := Iff.rfl

end CFSG.EvenSporadicStandard.J4Std.YElem
