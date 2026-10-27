module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54E7Iso

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3.E7Three

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.CentralExt
  CFSG.ClassicalInvolution.ModelFacts

theorem nonempty_mulEquiv_E7sc_three {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y)
    (hZ : IsPGroup 2 (center Y)) {n : ℕ} (hL : LieModel (Y ⧸ center Y) .E7 n 3 1) {t : Y}
    (ht2 : orderOf t = 2) (ht : t ∈ center Y) : Nonempty (E7sc 3 1 ≃* Y) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYm : UntwistedChevalleyModel (Y ⧸ center Y) .E7 (3 ^ 1) := by
    rcases hL with ⟨ht, -⟩ | ⟨-, -, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by simp [classicalTags])
    · exact hm
    · exact absurd ht (by simp [reeTitsTags])
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := hYm
  obtain ⟨-, ⟨eM⟩⟩ := FieldThree.e7_three_hopfMultiplier (K := K) (by rw [hK, pow_one])
  have hM : Nat.card (Open.griessHopfMultiplier (AdjointQuotient .E7 K)) = 2 := by
    rw [Nat.card_congr eM.toEquiv, hK, E7Row.gcd_two_pow_sub_one hp2]
    simp
  obtain ⟨-, h2, h3⟩ := GriessCentralCovers.central_covers_of_card_two hM
  have hcY : Nat.card (center Y) = 2 := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 (center Y)) := inferInstance
    have hS : (S : Subgroup (center Y)) = ⊤ := (S.is_maximal' (hZ.to_subgroup ⊤) le_top).symm
    have hle : Nat.card (center Y) ≤ 2 := by
      have := h2 Y hY ⟨e₁⟩ S
      rwa [hS, Subgroup.card_top] at this
    have hdvd : 2 ∣ Nat.card (center Y) := by
      rw [← ht2, ← Subgroup.orderOf_mk t ht]
      exact orderOf_dvd_natCard _
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  have hQ7 : IsQuasisimple (E7sc 3 1) := isQuasisimple_e7 (GaloisField 3 1)
  have : Finite (E7sc 3 1) := by
    have : Finite (Module.End (GaloisField 3 1) (Fin e7Data.d →₀ GaloisField 3 1)) :=
      Module.finite_of_finite (GaloisField 3 1)
    infer_instance
  have hX : UntwistedChevalleyModel (E7sc 3 1 ⧸ center (E7sc 3 1)) .E7 (3 ^ 1) :=
    untwistedChevalleyModel_of_surjective hQ7 (GaloisField.card 3 1 one_ne_zero)
      (e7Isogeny (GaloisField 3 1)) (e7Isogeny_surjective _)
      (exists_ne_one_of_surjective_adjointGroup (by decide) (e7Isogeny_surjective _))
      (MulEquiv.refl _)
  obtain ⟨e₂⟩ := ClassicalInvolution.Upgrade.untwistedChevalleyModel_unique hX
    ⟨K, inferInstance, inferInstance, hK, ⟨e₁⟩⟩
  exact h3 (E7sc 3 1) Y hQ7 hY (E7Row.card_center_E7sc hp2 one_ne_zero) hcY ⟨e₂.trans e₁⟩ ⟨e₁⟩

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3.E7Three
