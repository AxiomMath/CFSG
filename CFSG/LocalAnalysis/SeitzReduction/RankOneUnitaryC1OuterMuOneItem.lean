module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterStepLevel

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

theorem U3C1OuterStepHyp.exists_coords {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ D : Subgroup G} {d : G} {V : Subgroup G}
    {k : ℕ} (hS : U3C1OuterStepHyp G L f t T R₂ D d V k) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (v : G → K) (μ : K),
      Fintype.card K = 2 ^ f ∧ U3A₁Coords (szA₁ (szT₁ L T)) d v μ ∧
        ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w := by
  obtain ⟨-, hA₁card, -, -, -, hA₁2, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have hdT : d ∈ normalizer (szT₁ L T : Set G) := hS.cartan.le_normalizer hS.cartan.mem
  have hdA : ∀ b ∈ szA₁ (szT₁ L T), d⁻¹ * b * d ∈ szA₁ (szT₁ L T) := by
    intro b hb
    obtain ⟨hbT, hbC⟩ := mem_szA₁.mp hb
    refine mem_szA₁.mpr ⟨by simpa using (mem_normalizer_iff.mp (inv_mem hdT) b).mp hbT,
      mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : d * y * d⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hdT y).mp hy
    have e := mem_centralizer_iff.mp hbC _ hy'
    calc y * (d⁻¹ * b * d) = d⁻¹ * ((d * y * d⁻¹) * b) * d := by group
      _ = d⁻¹ * (b * (d * y * d⁻¹)) * d := by rw [e]
      _ = d⁻¹ * b * d * y := by group
  have hne : ∃ b ∈ szA₁ (szT₁ L T), b ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : szA₁ (szT₁ L T) = ⊥ := eq_bot_iff.mpr fun b hb => hne b hb
    rw [hbot, card_bot] at hA₁card
    have := Nat.one_lt_two_pow (n := f) (by have := hS.start.two_le; omega)
    omega
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := U3C1.exists_u3A₁Coords_of_trans
    (fun b hb b' hb' => mem_centralizer_iff.mp (mem_szA₁.mp hb').2 b (mem_szA₁.mp hb).1)
    hA₁2 hdA hS.cartan.trans hne
  exact ⟨K, inferInstance, inferInstance, inferInstance, v, μ, by rw [hK, hA₁card], hc, hμ⟩

end CFSG.SeitzReduction.RankOne
