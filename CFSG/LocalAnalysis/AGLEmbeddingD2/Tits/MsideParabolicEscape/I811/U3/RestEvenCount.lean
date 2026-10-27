module

public import CFSG.Open.FusionDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Count

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

open Subgroup

theorem stronglyEmbedded_card_eq_mul_inf {G : Type} [Group G] [Finite G] {B U W : Subgroup G}
    (hB : CFSG.Open.fusionStronglyEmbedded B) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hUB : U ≤ B)
    (hidx : B.index ≤ Nat.card U + 1) (hUW : U ≤ W) (hWB : ¬ W ≤ B) :
    B.index = Nat.card U + 1 ∧ Nat.card W = B.index * Nat.card (W ⊓ B : Subgroup G) := by
  classical
  have hfix : ∀ ζ ∈ U, ζ ≠ 1 → ∀ w ∈ W, w⁻¹ * ζ * w ∈ B → w ∈ B := by
    intro ζ hζU hζ1 w _ hconj
    by_contra hwB
    have hwB' : w⁻¹ ∉ B := fun h => hwB (by simpa using inv_mem h)
    have hodd : Odd (Nat.card ↥(B ⊓ B.map (MulAut.conj w).toMonoidHom)) := by
      simpa using hB.2.2 w⁻¹ hwB'
    have hζmem : ζ ∈ B ⊓ B.map (MulAut.conj w).toMonoidHom := by
      refine ⟨hUB hζU, ?_⟩
      exact ⟨w⁻¹ * ζ * w, hconj, by simp [MulAut.conj_apply, mul_assoc]⟩
    have h2dvd : 2 ∣ orderOf ζ := by
      have h2dvdU : 2 ∣ orderOf (⟨ζ, hζU⟩ : U) :=
        IsPGroup.dvd_orderOf hU fun h => hζ1 (by simpa using congrArg Subtype.val h)
      simpa using h2dvdU
    have hoddorder : Odd (orderOf ζ) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hζmem)
    exact hoddorder.not_two_dvd_nat h2dvd
  have hU2 : 2 ≤ Nat.card U := by
    have : 1 < Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).2 hU1
    omega
  have hmod : B.relIndex W % Nat.card U = 1 := by
    have h :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3.relIndex_modEq_one
        (Z := U) hUW hUB hfix
    simp only [Nat.ModEq] at h
    rwa [Nat.mod_eq_of_lt (show 1 < Nat.card U by omega)] at h
  have hn_ne1 : B.relIndex W ≠ 1 := fun h => hWB (Subgroup.relIndex_eq_one.mp h)
  have hle : B.relIndex W ≤ B.index := by
    rw [← Subgroup.relIndex_top_right (H := B)]
    exact Subgroup.relIndex_le_of_le_right le_top (by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite)
  obtain ⟨k, hk⟩ : ∃ k, B.relIndex W = Nat.card U * k + 1 := by
    refine ⟨B.relIndex W / Nat.card U, ?_⟩
    have h := Nat.div_add_mod (B.relIndex W) (Nat.card U)
    omega
  have hk1 : k = 1 := by
    have hle' : Nat.card U * k ≤ Nat.card U * 1 := by
      rw [mul_one]
      exact Nat.add_le_add_iff_right.mp (le_trans (hk ▸ hle) hidx)
    have hk_le : k ≤ 1 := Nat.le_of_mul_le_mul_left hle' (by omega)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact absurd (by rw [hk, hk0]; ring) hn_ne1
    · omega
  have hrel : B.relIndex W = Nat.card U + 1 := by rw [hk, hk1]; ring
  have hidx' : B.index = Nat.card U + 1 := le_antisymm hidx (hrel ▸ hle)
  refine ⟨hidx', ?_⟩
  have hcard := Subgroup.relIndex_mul_card B W
  rw [hrel, inf_comm] at hcard
  rw [hidx']
  exact hcard.symm

theorem oddIdxRest_nat_eq_of_dvd {q n : ℕ} (hq : Even q) (h2 : 2 ≤ q) (h1 : q ^ 3 ∣ n)
    (h2' : q + 1 ∣ n) (hn : n ∣ q ^ 3 * (q ^ 2 - 1)) (hd : q ^ 2 - 1 ∣ (q ^ 3 + 1) * n) :
    n = q ^ 3 * (q ^ 2 - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c, rfl⟩ := h1
  have hrodd : Odd r := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hq)
  have hsub : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    have h := Nat.sq_sub_sq (r + 1) 1
    rw [one_pow, Nat.add_sub_cancel] at h
    rw [h]
    ring
  have hsum : (r + 1) ^ 3 + 1 = (r + 2) * (r ^ 2 + r + 1) := by ring
  have hcop_r2 : Nat.Coprime (r + 2) ((r + 1) ^ 3) := by
    have h : Nat.Coprime (r + 1) (r + 2) := by
      rw [show r + 2 = (r + 1) + 1 by ring, Nat.coprime_self_add_right]
      simp
    exact h.symm.pow_right 3
  have hc_q1 : r + 2 ∣ c := by
    have h2'' : r + 2 ∣ (r + 1) ^ 3 * c := by
      rw [show r + 2 = (r + 1) + 1 by ring]
      exact h2'
    exact hcop_r2.dvd_of_dvd_mul_left h2''
  have hc_dvd : c ∣ r * (r + 2) := by
    have h := hn
    rw [hsub] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  have hr2 : Nat.Coprime r (r + 2) :=
    (Nat.coprime_self_add_right (m := r) (n := 2)).mpr (Nat.coprime_two_right.mpr hrodd)
  have hrq : Nat.Coprime r (r ^ 2 + r + 1) := by
    have h : Nat.Coprime r (1 + (r + 1) * r) :=
      (Nat.coprime_add_mul_right_right r 1 (r + 1)).mpr (by simp)
    rwa [show 1 + (r + 1) * r = r ^ 2 + r + 1 by ring] at h
  have hrq1 : Nat.Coprime r ((r + 1) ^ 3) := by
    have h : Nat.Coprime r (r + 1) :=
      (Nat.coprime_self_add_right (m := r) (n := 1)).mpr (by simp)
    exact h.pow_right 3
  have hAcop : Nat.Coprime r ((r + 2) * (r ^ 2 + r + 1) * (r + 1) ^ 3) :=
    (hr2.mul_right hrq).mul_right hrq1
  have hd' : r * (r + 2) ∣ (r + 2) * (r ^ 2 + r + 1) * ((r + 1) ^ 3 * c) := by
    have h := hd
    rw [hsub, hsum] at h
    exact h
  have hdiv : r ∣ ((r + 2) * (r ^ 2 + r + 1) * (r + 1) ^ 3) * c := by
    have hr1 : r ∣ r * (r + 2) := ⟨r + 2, rfl⟩
    simpa [mul_assoc] using dvd_trans hr1 hd'
  have hrc : r ∣ c := hAcop.dvd_of_dvd_mul_left hdiv
  have hc_eq : c = r * (r + 2) :=
    Nat.dvd_antisymm hc_dvd (Nat.Coprime.mul_dvd_of_dvd_of_dvd hr2 hrc hc_q1)
  rw [hc_eq, hsub]

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
