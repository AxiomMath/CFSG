module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLTwistedBase
public import CFSG.Quasithin.Vol2.F134LieD4Cells

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HTD42Seven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
open CFSG.Timmesfeld.ExceptionalOrders
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFAE.OLTwisted

theorem not_seven_dvd_two_pow (N : ℕ) : ¬ 7 ∣ (2 ^ 1) ^ N := by
  intro h
  have h2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h
  norm_num at h2

theorem not_seven_dvd_mul {Y Z : ℕ} (hY : ¬ 7 ∣ Y) (hZ : Z = 3 ∨ Z = 9) : ¬ 7 ∣ Y * Z := by
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h with h1 | h1
  · exact hY h1
  · omega

theorem seven_dvd_of_sq_dvd {X W : ℕ} (hX : X ∣ 7) (h : 49 ∣ X * W) : 7 ∣ W := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hX with rfl | rfl <;> omega

section Graph


theorem card_torus_dvd_seven {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hF : Nat.card F = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1)) :
    Nat.card (graphFixedRootTorus TwistTag.D4 F σ.toRingHom) ∣ 7 := by
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  have hqorb := card_orbitField (t := TwistTag.D4) Nat.prime_two (Nat.le_refl 1) hF
    (σ := σ.toRingHom) hσ
  rw [graphFixedRootTorus_eq_compatTorus hσs]
  have h2 : Nat.card (compatTorus (t := TwistTag.D4) σ.toRingHom) ∣
      Nat.card (compatSubgroup (t := TwistTag.D4) σ.toRingHom) :=
    Dvd.intro _ (card_compatTorus_mul (t := TwistTag.D4) σ.toRingHom)
  rw [card_compatSubgroup] at h2
  refine h2.trans (dvd_of_eq ?_)
  simp only [hqorb]
  decide

theorem not_dvd_sq_seven_card_normalizer_graphFixed_D4 {F : Type} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) (hF : Nat.card F = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (hH : Holds (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) 2)
    {U : Subgroup (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) :
    ¬ 49 ∣ Nat.card (Subgroup.normalizer (U : Set (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))) := by
  classical
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  have hqorb := card_orbitField (t := TwistTag.D4) Nat.prime_two (Nat.le_refl 1) hF
    (σ := σ.toRingHom) hσ
  obtain ⟨a, ha⟩ := exists_card_normalizer_dvd_card_maximal_parabolic TwistTag.D4 σ hH hU hU2
  have hex : ∀ i : Fin TwistTag.D4.foldedTag.rank, ∃ j : Fin TwistTag.D4.foldedTag.rank,
      ∀ k, k ≠ i → k = j := by decide
  obtain ⟨a', ha'⟩ := hex a
  have hle : graphFixedParabolic TwistTag.D4 F σ.toRingHom {b | b ≠ a} ≤
      graphFixedParabolic TwistTag.D4 F σ.toRingHom {a'} :=
    ((fixed_standard_parabolic_cells TwistTag.D4 F σ).2.2.2.1 _ _).2 (fun k hk => ha' k hk)
  have hfin : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  have h1 := ha.trans (Subgroup.card_dvd_of_le hle)
  rw [CFSG.Quasithin.F134.LieD4.card_graphFixedParabolic_singleton σ.surjective a',
    CFSG.Quasithin.F134.LieD4.card_graphFixedInversionUnipotent_D4 σ (Nat.le_refl 1) hF hσ a',
    card_graphFixedRootBorel hσs, card_graphFixedPosUnipotent hσs hqorb] at h1
  have hk : ∀ c : Fin TwistTag.D4.foldedTag.rank,
      (TwistTag.D4.orbit c).card = 1 ∨ (TwistTag.D4.orbit c).card = 3 := by decide
  have hZ : 1 + (2 ^ 1) ^ (TwistTag.D4.orbit a').card = 3 ∨
      1 + (2 ^ 1) ^ (TwistTag.D4.orbit a').card = 9 := by
    rcases hk a' with h | h <;> rw [h] <;> norm_num
  intro h49
  have h := h49.trans h1
  rw [mul_assoc] at h
  exact not_seven_dvd_mul (not_seven_dvd_two_pow _) hZ
    (seven_dvd_of_sq_dvd (card_torus_dvd_seven σ hF hσ) h)

end Graph

end CFSG.LocalAnalysis.GLTheoremA.HTD42Seven
