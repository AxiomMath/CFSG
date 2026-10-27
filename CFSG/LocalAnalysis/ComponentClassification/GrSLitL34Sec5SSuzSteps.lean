module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34SuzSignalizerGluing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P : Subgroup G),
    L34NormalSettingAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P →
    ∃ W : Subgroup G, Odd (Nat.card W) ∧ normalizer (P : Set G) ≤ normalizer (W : Set G) ∧
      (∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
        8 ≤ Nat.card E → GrSLit.wGroup E = W) ∧
      (center (↥P ⧸ pPrimeCore 2 ↥P) = ⊥ → ⁅oddIn P, P⁆ ≤ W)

@[expose] def L34SuzSignalizerExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P W : Subgroup G),
    L34NormalSettingAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P →
    Odd (Nat.card W) → W ≠ ⊥ → normalizer (P : Set G) ≤ normalizer (W : Set G) →
    (∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = W) → False

@[expose] def L34TwoSuzCoreOfSignalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P : Subgroup G),
    L34NormalSettingAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P →
    center (↥P ⧸ pPrimeCore 2 ↥P) ≠ ⊥ →
    (∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = ⊥) →
    ⁅oddIn P, P⁆ = ⊥

theorem l34SuzSignalizerVanishing_of_steps (hG : L34SuzSignalizerGluing)
    (hV : L34SuzSignalizerExclusion) : L34SuzSignalizerVanishing := by
  intro G _ _ t P hset E hEt hE hE8
  obtain ⟨W, hWo, hPW, hWE, -⟩ := hG G t P hset
  by_cases hW : W = ⊥
  · rw [hWE E hEt hE hE8, hW]
  · exact (hV G t P W hset hWo hW hPW hWE).elim

section Certified


theorem l34SuzCoreOfSignalizer_of_steps (hG : L34SuzSignalizerGluing)
    (hD : L34TwoSuzCoreOfSignalizer) : L34SuzCoreOfSignalizer := by
  intro G _ _ t P hset hvan
  by_cases hZ : center (↥P ⧸ pPrimeCore 2 ↥P) = ⊥
  · obtain ⟨W, -, -, hWE, hD0⟩ := hG G t P hset
    have hP8 : ∃ E : Subgroup G, E ≤ centralizer ({t} : Set G) ∧ Open.IsElemAbelian 2 E ∧
        8 ≤ Nat.card E := by
      have hPt := hset.2.2.1
      have hr := three_le_pRank_of_sporadic_suz_fusionZStar hset.2.2.2.2.2.2
      rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at hr
      obtain ⟨E, hEP, hE, hEc⟩ := SectionRank.exists_pRank (p := 2) one_lt_two P
      refine ⟨E, hEP.trans hPt, hE, ?_⟩
      rw [hEc]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ CFSG.Open.pRank 2 P := Nat.pow_le_pow_right (by norm_num) hr
    obtain ⟨E, hEt, hE, hE8⟩ := hP8
    have hW : W = ⊥ := by rw [← hWE E hEt hE hE8, hvan E hEt hE hE8]
    rw [hW] at hD0
    exact eq_bot_iff.mpr (hD0 hZ)
  · exact hD G t P hset hZ hvan

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S
