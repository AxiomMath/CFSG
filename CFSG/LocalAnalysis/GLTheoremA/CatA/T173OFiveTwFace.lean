module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFaceD4Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction.TwistedE6Pilot

local notation "Γ₂" F => ModGL TwistTag.E6.tag F


private theorem false_of_le_levi_sup_diag_D4 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJ : J ⊆ twE6MaxD4)
    {A : Subgroup (Γ₂ F)} (hAel : IsElemAbelian 3 A) (hA4 : 3 ^ 4 ≤ Nat.card A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔
      twistedE6DiagGL F σ)
    {d : Γ₂ F} (hdA : d ∈ A)
    (hKL : stdLayerD (twistedE6RootGroup F σ) d ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J)
    (hcent : A ⊓ Subgroup.centralizer
      (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) = Subgroup.zpowers d) :
    False := by
  haveI : Finite (Γ₂ F) := CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨z, hz1, hzC, hzE, X, hXG, hXz, hXp, hXL⟩ :=
    exists_central_witness_D4 hF σ hσ h3
  have hzA : z ∈ A :=
    hzE A (hAL.trans (sup_le_sup_right (graphFixedParabolicLevi_mono hJ) _)) hAel hA4
  have hKD : stdLayerD (twistedE6RootGroup F σ) d ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4 :=
    hKL.trans (graphFixedParabolicLevi_mono hJ)
  have hzK : z ∈ Subgroup.centralizer
      (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) :=
    Subgroup.centralizer_le hKD hzC
  have hzd : z ∈ Subgroup.zpowers d := by
    rw [← hcent]
    exact ⟨hzA, hzK⟩
  have hd3 : d ^ 3 = 1 := hAel.2 d hdA
  have hz3 : z ^ 3 = 1 := hAel.2 z hzA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have heq : Subgroup.zpowers z = Subgroup.zpowers d := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hzd) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hoz]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
  have hdz : d ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers d
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdz
  have hXd : X ≤ Subgroup.centralizer ({d} : Set (Γ₂ F)) := by
    intro x hx
    have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.1 (hXz hx)) z rfl
    rw [Subgroup.mem_centralizer_iff]
    rintro y rfl
    rw [← hk]
    exact (Commute.zpow_left hzx k).eq
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hz1 (by simpa using hzd)
  have hdG : d ∈ twistedE6InndiagGL F σ :=
    (sup_le_sup_right (graphFixedParabolicLevi_le (t := TwistTag.E6) (K := F)
      (σ := σ.toRingHom) (J := J)) _) (hAL hdA)
  exact hXL ((le_stdLayerD_twE6_of_perfect hn hF σ hσ hdG hd1 hd3 hXG hXd hXp).trans hKD)

theorem subset_twE6MaxA5_of_stdD_of_faces
    (hA2A1 : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = (2 ^ n) ^ 2 →
      ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ 2 ^ n) → 3 ∣ 2 ^ n + 1 →
      ∀ {E : Subgroup (Γ₂ F)},
        E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1 ⊔
          twistedE6DiagGL F σ →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3)
    (hA1A2 : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = (2 ^ n) ^ 2 →
      ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ 2 ^ n) → 3 ∣ 2 ^ n + 1 →
      ∀ {E : Subgroup (Γ₂ F)},
        E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
          twistedE6DiagGL F σ →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {A : Subgroup (Γ₂ F)} (hAel : IsElemAbelian 3 A) (hA4 : 3 ^ 4 ≤ Nat.card A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔
      twistedE6DiagGL F σ)
    {d : Γ₂ F} (hdA : d ∈ A)
    (hKL : stdLayerD (twistedE6RootGroup F σ) d ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J)
    (hcomp : IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d)
      (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F))))
    (hcent : A ⊓ Subgroup.centralizer
      (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) = Subgroup.zpowers d) :
    J ⊆ twE6MaxA5 := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have h1 : Nat.card F = 1 := by simpa using hF
      exact absurd h1 (Finite.one_lt_card (α := F)).ne'
    · exact h0
  rcases subset_maximalSet_of_ne_univ hJ with h | h | h | h
  · exact h
  · have hle := hA2A1 hF σ hσ h3
      (hAL.trans (sup_le_sup_right (graphFixedParabolicLevi_mono h) _)) hAel
    exact absurd (hA4.trans hle) (by norm_num)
  · have hle := hA1A2 hF σ hσ h3
      (hAL.trans (sup_le_sup_right (graphFixedParabolicLevi_mono h) _)) hAel
    exact absurd (hA4.trans hle) (by norm_num)
  · exact (false_of_le_levi_sup_diag_D4 hn hF σ hσ h3 h hAel hA4 hAL hdA hKL hcent).elim

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
