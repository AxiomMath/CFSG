module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Eight

variable {X : Type} [Group X]

@[expose] def JeN (n : ℕ) (H : Subgroup X) : Subgroup X :=
  ⨆ (E : Subgroup X) (_ : E ≤ H ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = n), E

theorem le_JeN {n : ℕ} {H E : Subgroup X} (hEH : E ≤ H) (hE : ∀ x ∈ E, x * x = 1)
    (hn : Nat.card E = n) : E ≤ JeN n H :=
  le_iSup₂_of_le E ⟨hEH, hE, hn⟩ le_rfl

theorem JeN_le (n : ℕ) (H : Subgroup X) : JeN n H ≤ H :=
  iSup₂_le fun _ h => h.1

theorem JeN_le_of {n : ℕ} {H K : Subgroup X}
    (hK : ∀ E : Subgroup X, E ≤ H → (∀ x ∈ E, x * x = 1) → Nat.card E = n → E ≤ K) :
    JeN n H ≤ K :=
  iSup₂_le fun E h => hK E h.1 h.2.1 h.2.2

theorem conjugate_mul_self_eq_one {E : Subgroup X} (hE : ∀ x ∈ E, x * x = 1) (g : X) :
    ∀ x ∈ conjugate E g, x * x = 1 := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have h1 := hE _ hx
  calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
    _ = 1 := by rw [h1]; group

variable [Finite X]

omit [Finite X] in
theorem card_conjugate' (E : Subgroup X) (g : X) : Nat.card (conjugate E g) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_JeN_eq {n : ℕ} {H : Subgroup X} {g : X} (hg : conjugate (JeN n H) g ≤ H) :
    conjugate (JeN n H) g = JeN n H := by
  refine eq_of_le_of_card_ge ?_ (card_conjugate' _ _).ge
  change (JeN n H).map (MulAut.conj g⁻¹).toMonoidHom ≤ JeN n H
  rw [map_le_iff_le_comap]
  refine JeN_le_of fun E hEH hE hn => ?_
  rw [← map_le_iff_le_comap]
  have hle : conjugate E g ≤ conjugate (JeN n H) g := map_mono (le_JeN hEH hE hn)
  exact le_JeN (hle.trans hg) (conjugate_mul_self_eq_one hE g) ((card_conjugate' E g).trans hn)

theorem normalizer_le_normalizer_JeN (n : ℕ) (H : Subgroup X) :
    normalizer (H : Set X) ≤ normalizer (JeN n H : Set X) := by
  intro g hg
  have h1 : conjugate (JeN n H) g ≤ H := by
    change (JeN n H).map (MulAut.conj g⁻¹).toMonoidHom ≤ H
    refine (map_mono (JeN_le n H)).trans ?_
    intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hy
    have := (mem_normalizer_iff.mp (inv_mem hg) w).mp hw
    simpa [MulAut.conj_apply] using this
  have h2 := conjugate_JeN_eq h1
  rw [mem_normalizer_iff]
  intro y
  rw [← mem_conjugate_iff (x := y), h2]

end Eight

end CFSG.ComponentClassification.GSThmB
