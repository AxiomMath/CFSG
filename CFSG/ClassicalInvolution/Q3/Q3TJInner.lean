module

public import CFSG.ClassicalInvolution.Q3.Q3TIModel
public import CFSG.ClassicalInvolution.Q3.Q3TSetup

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open CFSG.ComponentClassification

variable {X : Type} [Group X] [Finite X]

theorem oddCore_eq_bot_of_quasisimple (hX : CFSG.Open.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) {z : X} (hz : orderOf z = 2) :
    classicalInvolutionOddCore X = ⊥ := by
  rcases normal_le_center_or_eq_top_qs hX
      (inferInstance : (classicalInvolutionOddCore X).Normal) with h | h
  · rw [hZ] at h
    exact le_bot_iff.mp h
  · exfalso
    have h1 : orderOf z ∣ Nat.card (classicalInvolutionOddCore X) := by
      have := orderOf_dvd_natCard (⟨z, h ▸ Subgroup.mem_top z⟩ : classicalInvolutionOddCore X)
      rwa [Subgroup.orderOf_mk] at this
    rw [hz] at h1
    exact (Nat.not_even_iff_odd.mpr (OddCore.odd_card X)) (even_iff_two_dvd.mpr h1)

omit [Finite X] in
theorem not_isSolvable_of_quasisimple (hX : CFSG.Open.IsQuasisimple X) :
    ¬ Group.IsSolvable X := by
  intro hs
  have : Nontrivial (X ⧸ Subgroup.center X) := hX.2.toNontrivial
  have : Nontrivial X := (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial X
  rw [hX.1] at h
  exact lt_irrefl _ h

omit [Finite X] in
theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 : a * x * a⁻¹ = b * x * b⁻¹ := congrArg (fun φ : MulAut X => φ x) hab
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [h1]
      _ = b⁻¹ * a * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hc, mul_one]

theorem modelOddAutRigid_inner (hX : CFSG.Open.IsQuasisimple X) (hZ : Subgroup.center X = ⊥)
    {Λ : Set (Subgroup X)} (hLie : LieSystemMod3 Λ) {z : X} (hz : orderOf z = 2) (g : X)
    (hodd : Odd (orderOf (MulAut.conj g)))
    (hfix : ∀ c ∈ Subgroup.centralizer ({z} : Set X),
      c⁻¹ * MulAut.conj g c ∈ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X))) :
    MulAut.conj g = 1 := by
  set C := Subgroup.centralizer ({z} : Set X) with hC
  have hOC : Balance.oddCoreIn C = ⊥ := by
    have h := lieSystemOddCentralizer3_proved X Λ hLie z hz
    rw [oddCore_eq_bot_of_quasisimple hX hZ hz] at h
    exact le_bot_iff.mp h
  have hcomm : ∀ c ∈ C, g * c * g⁻¹ = c := by
    intro c hc
    have h := hfix c hc
    rw [hOC, Subgroup.mem_bot, MulAut.conj_apply] at h
    calc g * c * g⁻¹ = c * (c⁻¹ * (g * c * g⁻¹)) := by group
      _ = c := by rw [h, mul_one]
  have hgC : g ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have h := hcomm z (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h]
  have hle : Subgroup.zpowers g ≤ Balance.oddCoreIn C := by
    refine Balance.le_oddCoreIn_of_normalizes ?_ ?_ ?_
    · exact (Subgroup.zpowers_le).mpr hgC
    · intro d hd
      have hdg : Commute d g := by
        have h := hcomm d hd
        have h2 : g * d = d * g := by
          calc g * d = g * d * g⁻¹ * g := by group
            _ = d * g := by rw [h]
        exact h2.symm
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        rw [(hdg.zpow_right k).eq, mul_inv_cancel_right]
        exact hw
      · intro hw
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
        have hw' : w = g ^ k := by
          have h2 : w = d⁻¹ * (d * w * d⁻¹) * d := by group
          rw [h2, ← hk, mul_assoc, ← (hdg.zpow_right k).eq, inv_mul_cancel_left]
        rw [hw']
        exact Subgroup.zpow_mem_zpowers g k
    · rw [Nat.card_zpowers]
      rwa [orderOf_injective _ (conj_injective_of_center_eq_bot hZ) g] at hodd
  rw [hOC] at hle
  have hg : g = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers g))
  rw [hg, map_one]

end CFSG.ClassicalInvolution.Q3.Q3T
