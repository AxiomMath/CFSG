module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAFacts

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dP sP)


theorem apply_of_comm_eq {Y G c : Equiv.Perm (Fin 693)} (h : Y * G * Y⁻¹ * G⁻¹ = c)
    (p : Fin 693) : Y (G p) = c (G (Y p)) := by
  have e : c * (G * Y) = Y * G := by rw [← h]; group
  have := congrArg (fun f : Equiv.Perm (Fin 693) => f p) e
  simpa [Equiv.Perm.mul_apply] using this.symm

theorem c10Wit_spec {k d : Array ℕ} {Y : Equiv.Perm (Fin 693)}
    (hY : ∀ p : Fin 693, k[d[(p : ℕ)]!]! = ((Y p : Fin 693) : ℕ)) (hw : c10Wit k d = true) :
    ∃ w ∈ chA1.gens, Y * wP w * Y⁻¹ * (wP w)⁻¹ ∉ chZ.grp := by
  obtain ⟨idx, hidx, hgf⟩ := Array.any_eq_true.1 hw
  obtain ⟨w, hwm, hgw⟩ := O_mem_gens hidx
  rw [hgw, Bool.not_eq_true'] at hgf
  obtain ⟨P, hP⟩ := exists_of_not_allLt hgf
  have hG := rep_wA_gens gensOK_chA1 hwm
  have hz : Rep 693 gz (gP 14) := rep_gA tabs_check (by norm_num)
  simp only [rep_get hG P, rep_get hG, hY, rep_get hz, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq, Fin.val_inj] at hP
  refine ⟨w, hwm, fun hmem => ?_⟩
  rcases mem_chZ_cases hmem with hc | hc
  · exact hP.1 (apply_of_comm_eq hc P)
  · exact hP.2 (apply_of_comm_eq hc P)

theorem c10_spec {k : Equiv.Perm (Fin 693)} (hk : k ∈ chK1.grp) {i j : ℕ} (hi : i < 3)
    (hj : j < 2) (h : ∀ w ∈ chA1.gens, k * (dP ^ i * sP ^ j) * wP w *
      (k * (dP ^ i * sP ^ j))⁻¹ * (wP w)⁻¹ ∈ chZ.grp) :
    k = 1 ∧ i = 0 ∧ j = 0 := by
  obtain ⟨a, hK, hc0⟩ := c10_check k hk
  unfold c10At at hc0
  have hD := rep_dArr' hi hj
  have hc := allLt_spec hc0 (show i + 3 * j < 6 by omega)
  rw [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with hw | ⟨hq, hid⟩
  · have hY : ∀ p : Fin 693, a[(dArr[i + 3 * j]!)[(p : ℕ)]!]! =
        (((k * (dP ^ i * sP ^ j)) p : Fin 693) : ℕ) := fun p => by
      rw [rep_get hD p, rep_get hK]
      rfl
    obtain ⟨w, hwm, hn⟩ := c10Wit_spec hY hw
    exact absurd (h w hwm) hn
  · exact ⟨eq_of_eqA hK rep_idA hid, by omega, by omega⟩

theorem c8Wit_spec {k d : Array ℕ} {Y : Equiv.Perm (Fin 693)}
    (hY : ∀ p : Fin 693, k[d[(p : ℕ)]!]! = ((Y p : Fin 693) : ℕ)) (hw : c8WitL k d = true) :
    ∃ w ∈ chK1.gens, Y * wP w * Y⁻¹ * (wP w)⁻¹ ∉ chA1.grp := by
  obtain ⟨idx, hidx, hgf⟩ := Array.any_eq_true.1 hw
  obtain ⟨w, hwm, hgw⟩ := O_mem_gens hidx
  rw [hgw, Bool.not_eq_true'] at hgf
  obtain ⟨P, hP⟩ := exists_of_not_allLt hgf
  have hG := rep_wA_gens gensOK_chK1 hwm
  simp only [rep_get hG P, rep_get hG, hY, beq_eq_false_iff_ne, ne_eq] at hP
  refine ⟨w, hwm, fun hmem => hP ?_⟩
  have e := apply_of_comm_eq (rfl : _ = Y * wP w * Y⁻¹ * (wP w)⁻¹) P
  have hl := labA1_inv _ hmem (wP w (Y P))
  exact (congrArg (fun x : Fin 693 => labA1[(x : ℕ)]!) e).trans hl

theorem c8_spec {k : Equiv.Perm (Fin 693)} (hk : k ∈ chK1.grp) {i j : ℕ} (hi : i < 3)
    (hj : j < 2) (hij : i = 0 ∨ j = 1) (h : ∀ w ∈ chK1.gens, k * (dP ^ i * sP ^ j) * wP w *
      (k * (dP ^ i * sP ^ j))⁻¹ * (wP w)⁻¹ ∈ chA1.grp) :
    k = 1 ∧ i = 0 ∧ j = 0 := by
  obtain ⟨a, hK, hc0⟩ := c8_check k hk
  unfold c8At at hc0
  have hD := rep_dArr' hi hj
  have hc := allLt_spec hc0 (show i + 3 * j < 6 by omega)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with ((hq | hq) | hw) | ⟨hq, hid⟩
  · omega
  · omega
  · have hY : ∀ p : Fin 693, a[(dArr[i + 3 * j]!)[(p : ℕ)]!]! =
        (((k * (dP ^ i * sP ^ j)) p : Fin 693) : ℕ) := fun p => by
      rw [rep_get hD p, rep_get hK]
      rfl
    obtain ⟨w, hwm, hn⟩ := c8Wit_spec hY hw
    exact absurd (h w hwm) hn
  · exact ⟨eq_of_eqA hK rep_idA hid, by omega, by omega⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
