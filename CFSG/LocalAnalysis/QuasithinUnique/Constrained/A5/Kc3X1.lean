module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3X0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc2

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3J
  CFSG.QuasithinUnique.A5.Kc3NSC

section Classify

variable {K : Type} [Group K]

theorem card_of_beta {E : Subgroup K}
    (β : ↥E ≃* Multiplicative ↥(evenWeight 5)) : Nat.card E = 16 := by
  rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
  exact CFSG.QuasithinUnique.AppC.card_evenWeight

theorem eq_map_conj_inv {E F : Subgroup K} {c : K}
    (h : E.map (MulAut.conj c).toMonoidHom = F) :
    E = F.map (MulAut.conj c⁻¹).toMonoidHom := by
  rw [← h, Subgroup.map_map]
  have : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id K := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem classify_of_x0 [Finite K] (x₀ : K) (hx₀ : orderOf x₀ = 5) (h25 : ¬ 25 ∣ Nat.card K)
    (I : Set K) (hI : ∀ t : K, t * t = 1 → t ≠ 1 → t ∈ I) (Es : List (Subgroup K))
    (hcard : ∀ F ∈ Es, Nat.card F = 16)
    (hN : ∀ F ∈ Es, x₀ ∈ Subgroup.normalizer (F : Set K))
    (hchk : ∀ y ∈ I, (∃ F ∈ Es, y ∈ F) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧
        y * (x₀ ^ k * y * (x₀ ^ k)⁻¹) ≠ (x₀ ^ k * y * (x₀ ^ k)⁻¹) * y) ∨
      y * (x₀ ^ 1 * y * (x₀ ^ 1)⁻¹) * (x₀ ^ 2 * y * (x₀ ^ 2)⁻¹) * (x₀ ^ 3 * y * (x₀ ^ 3)⁻¹) *
        (x₀ ^ 4 * y * (x₀ ^ 4)⁻¹) ≠ 1)
    {E : Subgroup K} (β : ↥E ≃* Multiplicative ↥(evenWeight 5)) (hact : Delta5Norm E β) :
    ∃ F ∈ Es, ∃ c : K, E = F.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c, y, hyI, hcl, hcomm, hprod⟩ := exists_conj_closure β x₀ hx₀ h25 I hI hact
  rcases hchk y hyI with ⟨F, hF, hyF⟩ | ⟨k, hk1, hk4, hne⟩ | hne
  · refine ⟨F, hF, c⁻¹, eq_map_conj_inv ?_⟩
    have hle : E.map (MulAut.conj c).toMonoidHom ≤ F := by
      rw [hcl, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ (hN F hF) k) y).1 hyF
    refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
    rw [hcard F hF, Subgroup.card_map_of_injective (MulAut.conj c).injective, card_of_beta β]
  · exfalso
    apply hne
    have := hcomm 0 k
    simpa using this
  · exfalso
    apply hne
    simpa using hprod

theorem locClass2_of_x0 [Finite K] (x₀ : K) (hx₀ : orderOf x₀ = 5) (h25 : ¬ 25 ∣ Nat.card K)
    (I : Set K) (hI : ∀ t : K, t * t = 1 → t ≠ 1 → t ∈ I) (Es : List (Subgroup K))
    (hcard : ∀ F ∈ Es, Nat.card F = 16)
    (hN : ∀ F ∈ Es, x₀ ∈ Subgroup.normalizer (F : Set K))
    (hchk : ∀ y ∈ I, (∃ F ∈ Es, y ∈ F) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧
        y * (x₀ ^ k * y * (x₀ ^ k)⁻¹) ≠ (x₀ ^ k * y * (x₀ ^ k)⁻¹) * y) ∨
      y * (x₀ ^ 1 * y * (x₀ ^ 1)⁻¹) * (x₀ ^ 2 * y * (x₀ ^ 2)⁻¹) * (x₀ ^ 3 * y * (x₀ ^ 3)⁻¹) *
        (x₀ ^ 4 * y * (x₀ ^ 4)⁻¹) ≠ 1)
    (hEs : ∀ F ∈ Es, LocHypA F ∨ LocHypD F ∨ LocHypV F) : LocClass2 K := by
  intro E β hact
  obtain ⟨F, hF, c, hEF⟩ := classify_of_x0 x₀ hx₀ h25 I hI Es hcard hN hchk β hact
  exact ⟨F, c, hEs F hF, hEF⟩

end Classify

end CFSG.QuasithinUnique.A5
