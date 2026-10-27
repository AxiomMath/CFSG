module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

open Subgroup

variable {K G : Type*} [Group K] [Finite K] [Group G]

theorem exists_le_commutator_eq_map_eq_top [Group.IsPerfect G] (ψ : K →* G) {H : Subgroup K}
    (hH : H.map ψ = ⊤) : ∃ Y ≤ H, ⁅Y, Y⁆ = Y ∧ Y.map ψ = ⊤ := by
  obtain ⟨Y, hYmin⟩ := Set.Finite.exists_minimalFor (fun Y : Subgroup K => Nat.card Y)
    {Y : Subgroup K | Y ≤ H ∧ Y.map ψ = ⊤} (Set.toFinite _) ⟨H, le_rfl, hH⟩
  obtain ⟨hYH, hYψ⟩ := hYmin.1
  have hc : (⁅Y, Y⁆ : Subgroup K).map ψ = ⊤ := by
    rw [Subgroup.map_commutator, hYψ]
    exact Group.IsPerfect.commutator_eq_top (G := G)
  have hle : ⁅Y, Y⁆ ≤ Y := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  have hcard : Nat.card ↥Y ≤ Nat.card ↥⁅Y, Y⁆ := hYmin.le ⟨hle.trans hYH, hc⟩
  exact ⟨Y, hYH, Subgroup.eq_of_le_of_card_ge hle hcard, hYψ⟩

theorem exists_isPGroup_perfect_supplement [Group.IsPerfect G] (ψ : K →* G)
    (hψ : Function.Surjective ψ) {r : ℕ} [Fact r.Prime] {R : Subgroup K} (hRN : R ≤ ψ.ker)
    (hR : IsPGroup r R) :
    ∃ S : Subgroup K, R ≤ S ∧ S ≤ ψ.ker ∧ IsPGroup r S ∧
      ∃ Y : Subgroup K, Y ≤ normalizer (S : Set K) ∧ ⁅Y, Y⁆ = Y ∧ Y.map ψ = ⊤ := by
  let N : Subgroup K := ψ.ker
  let R₀ : Subgroup ↥N := R.comap N.subtype
  have hR₀ : IsPGroup r R₀ := hR.comap_of_injective N.subtype N.subtype_injective
  obtain ⟨Q, hRQ⟩ := hR₀.exists_le_sylow
  let S : Subgroup K := (Q : Subgroup ↥N).map N.subtype
  have hRS : R ≤ S := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hRN hx⟩, hRQ (Subgroup.mem_comap.mpr hx), rfl⟩
  have hSN : S ≤ N := Subgroup.map_subtype_le _
  have hSp : IsPGroup r S := Q.isPGroup'.map N.subtype
  have hfr : normalizer (S : Set K) ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top (N := N) Q
  have hNbot : N.map ψ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
  have hHmap : (normalizer (S : Set K)).map ψ = ⊤ := by
    have h := congrArg (Subgroup.map ψ) hfr
    rw [Subgroup.map_sup, Subgroup.map_top, MonoidHom.range_eq_top.mpr hψ, hNbot,
      sup_bot_eq] at h
    exact h
  obtain ⟨Y, hYle, hYperf, hYmap⟩ :=
    exists_le_commutator_eq_map_eq_top (G := G) ψ
      (H := normalizer (S : Set K)) hHmap
  exact ⟨S, hRS, hSN, hSp, Y, hYle, hYperf, hYmap⟩
