module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCDeltaConjugation
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem delta_failure_invariant_two_witness [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfail : ¬ GLADeltaZero G p) :
    ∃ B : Subgroup G, GLAIsBmax p B ∧ ∃ D : Subgroup G, D ≤ B ∧ IsElemAbelian p D ∧
      Nat.card D = p ^ 2 ∧ ∃ S K : Subgroup G, (5 ≤ p → K = GLADelta p D) ∧
        (p = 3 → K = ⁅GLADelta p D, B⁆) ∧ Even (Nat.card K) ∧
        (∃ Q : Sylow 2 K, (Q : Subgroup K).map K.subtype = S) ∧ S ≠ ⊥ ∧
        S ≤ GLADelta p D ∧ B ≤ normalizer (S : Set G) ∧ D ≤ centralizer (S : Set G) ∧
        IsPLocal 2 (normalizer (S : Set G)) ∧ (p = 3 → S ≤ ⁅GLADelta p D, B⁆) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  simp only [GLADeltaZero, not_forall, exists_prop] at hfail
  obtain ⟨B, hB, D, hDB, hD, hDcard, hbad⟩ := hfail
  have hp35 : p = 3 ∨ 5 ≤ p := by
    by_contra h
    push Not at h
    have h4 : p = 4 := by have := hp.two_le; omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  obtain ⟨K, hK5, hK3, hKeven⟩ : ∃ K : Subgroup G, (5 ≤ p → K = GLADelta p D) ∧
      (p = 3 → K = ⁅GLADelta p D, B⁆) ∧ Even (Nat.card K) := by
    rcases hp35 with h3 | h5
    · refine ⟨⁅GLADelta p D, B⁆, fun h => absurd h (by omega), fun _ => rfl, ?_⟩
      exact Nat.not_odd_iff_even.mp fun hodd => hbad ⟨fun h => absurd h (by omega), fun _ => hodd⟩
    · refine ⟨GLADelta p D, fun _ => rfl, fun h => absurd h (by omega), ?_⟩
      exact Nat.not_odd_iff_even.mp fun hodd => hbad ⟨fun _ => hodd, fun h => absurd h (by omega)⟩
  obtain ⟨hΔC, hΔp, -, -, hBact⟩ := delta_conjugation_and_coprime_action hp hp2 hD hDcard
  obtain ⟨hBN, hcommle, hBN', hcp⟩ := hBact B hB.1 hDB
  have hKΔ : K ≤ GLADelta p D := by
    rcases hp35 with h3 | h5
    · rw [hK3 h3]; exact hcommle
    · rw [hK5 h5]
  have hBK : B ≤ normalizer (K : Set G) := by
    rcases hp35 with h3 | h5
    · rw [hK3 h3]; exact hBN'
    · rw [hK5 h5]; exact hBN
  have hKp : Nat.Coprime p (Nat.card K) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rcases hp35 with h3 | h5
    · rw [hK3 h3]; exact hcp
    · rw [hK5 h5]; exact hΔp
  have hBp : IsPGroup p B := fun b => ⟨1, Subtype.ext (by simpa using hB.1.2 b b.2)⟩
  obtain ⟨Q, hQ⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow p 2 hp
    Nat.prime_two B K hBp hBK hKp
  have hSK : (Q : Subgroup K).map K.subtype ≤ K := map_subtype_le _
  have hSne : (Q : Subgroup K).map K.subtype ≠ ⊥ := by
    rw [Ne, map_eq_bot_iff_of_injective _ K.subtype_injective]
    exact Q.ne_bot_of_dvd_card (even_iff_two_dvd.mp hKeven)
  have hSp : IsPGroup 2 ((Q : Subgroup K).map K.subtype) := Q.isPGroup'.map K.subtype
  refine ⟨B, hB, D, hDB, hD, hDcard, (Q : Subgroup K).map K.subtype, K, hK5, hK3, hKeven,
    ⟨Q, rfl⟩, hSne, hSK.trans hKΔ, hQ, ?_, ⟨_, hSne, hSp, rfl⟩, fun h3 => ?_⟩
  · exact le_centralizer_iff.mp ((hSK.trans hKΔ).trans hΔC)
  · rw [← hK3 h3]
    exact hSK

end CFSG.LocalAnalysis.GorensteinLyons
