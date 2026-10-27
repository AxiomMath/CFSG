module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutCount
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsClassLemmas

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.Blueprint

variable {L : Type} [Group L]

private lemma conj_inner_iff (g φ : MulAut L) :
    (∃ a : L, ∀ u : L, (g * φ * g⁻¹) u = a * u * a⁻¹) ↔
      ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨g⁻¹ a, fun u => ?_⟩
    have h := ha (g u)
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h
    calc φ u = g⁻¹ (g (φ u)) := by simp
      _ = g⁻¹ (a * g u * a⁻¹) := by rw [h]
      _ = g⁻¹ a * u * (g⁻¹ a)⁻¹ := by
        simp [map_mul, map_inv, MulAut.inv_apply_self]
  · rintro ⟨a, ha⟩
    refine ⟨g a, fun u => ?_⟩
    simp only [MulAut.mul_apply]
    rw [ha]
    simp [map_mul, map_inv, MulAut.apply_inv_self]

theorem l33_outer_involutions_conj
    (hL : LieModel L .PSL 3 3 1)
    {φ ψ : MulAut L} (hφ : φ ^ 2 = 1) (hφo : ¬ ∃ a : L, ∀ u : L, φ u = a * u * a⁻¹)
    (hψ : ψ ^ 2 = 1) (hψo : ¬ ∃ a : L, ∀ u : L, ψ u = a * u * a⁻¹) : IsConj φ ψ := by
  obtain ⟨F⟩ := l33_nonempty_fritzData hL
  have hcardAut : Nat.card (MulAut L) = 11232 := l33_card_mulAut hL
  haveI : Finite (MulAut L) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; norm_num)
  let S : Set (MulAut L) := {θ | θ ^ 2 = 1 ∧ ¬ ∃ a : L, ∀ u : L, θ u = a * u * a⁻¹}
  have hScard : Nat.card S = 234 := by
    change Nat.card {θ : MulAut L // θ ^ 2 = 1 ∧
      ¬ ∃ a : L, ∀ u : L, θ u = a * u * a⁻¹} = 234
    exact l33_card_outer_involutions hL
  have hSclosed : ∀ g s, s ∈ S → g * s * g⁻¹ ∈ S := by
    intro g s hs
    dsimp only [S] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [conj_pow, hs.1]
      simp
    · rintro ⟨a, ha⟩
      exact hs.2 ((conj_inner_iff g s).1 ⟨a, ha⟩)
  have hkS : F.k ∈ S := by
    dsimp only [S]
    exact ⟨F.k_sq, F.k_outer⟩
  have hφS : φ ∈ S := by
    dsimp only [S]
    exact ⟨hφ, hφo⟩
  have hψS : ψ ∈ S := by
    dsimp only [S]
    exact ⟨hψ, hψo⟩
  have hcard : Nat.card S *
      Nat.card (Subgroup.centralizer ({F.k} : Set (MulAut L))) = Nat.card (MulAut L) := by
    rw [hScard, F.card_centralizer_k, hcardAut]
  have hkφ : IsConj F.k φ :=
    isConj_of_card_mul_card_centralizer S hSclosed hkS hcard hφS
  have hkψ : IsConj F.k ψ :=
    isConj_of_card_mul_card_centralizer S hSclosed hkS hcard hψS
  exact hkφ.symm.trans hkψ

end CFSG.OddStandard.SmallF3.L33
