module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHardDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open

variable {p : ℕ}

@[expose] def ModelSelQ2 (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  ∀ r : T, r ^ p = 1 → r ≠ 1 → ∀ P : Subgroup T, P ≤ Subgroup.centralizer ({r} : Set T) →
    IsPGroup 2 ↥P → P ≠ ⊥ →
    ∃ R : Subgroup T, ⁅P, R⁆ ≠ ⊥ ∧
      P ≤ R ⊔ (Subgroup.centralizer ({r} : Set T) ⊓ Subgroup.centralizer (R : Set T)) ∧
      (IsComponentOf R (Subgroup.centralizer ({r} : Set T)) ∨
        ∀ w ∈ Subgroup.centralizer ({r} : Set T), w ^ p = 1 →
          w ∈ Subgroup.centralizer (R : Set T))

theorem modelSelH_of_q2 {T : Type} [Group T] [Finite T] (hQ : ModelSelQ2 p T)
    (hT : CompTriv p T) : ModelSelH p T := by
  intro r hrp hr1 A Q hrA hAp hAab hQC hQ2 hAN hne
  have hPQ : (⁅A, Q⁆ : Subgroup T) ≤ Q := Subgroup.le_normalizer_iff_commutator_le_right.1 hAN
  obtain ⟨R, hRa, hRP, hRc | hRw⟩ := hQ r hrp hr1 _ (hPQ.trans hQC) (hQ2.to_le hPQ) hne
  ·
    exact ⟨R, hRc, dvd_of_component_of_triv hT hrp hr1 hrA hAp hAab hQC hRc hRa, hRa, hRP⟩
  ·
    exfalso
    refine hRa ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro a ha t ht
    have haC : a ∈ Subgroup.centralizer ({r} : Set T) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hAab a ha r hrA)
    have htC : t ∈ Subgroup.centralizer ({r} : Set T) := hQC ht
    have htat : t * a * t⁻¹ ∈ Subgroup.centralizer (R : Set T) := by
      refine hRw _ (mul_mem (mul_mem htC haC) (inv_mem htC)) ?_
      rw [conj_pow, hAp a ha, mul_one, mul_inv_cancel]
    rw [commutatorElement_def, show a * t * a⁻¹ * t⁻¹ = a * (t * a * t⁻¹)⁻¹ by group]
    exact Subgroup.mul_mem _ (hRw a haC (hAp a ha)) (Subgroup.inv_mem _ htat)

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
