module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4ClassBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

theorem noNonHBlockAt_of_conj_fixed {Y : Type} [Group Y] [Finite Y] (hY : ¬ 5 ^ 2 ∣ Nat.card Y)
    (Hy : Subgroup Y) {V : Subgroup Y} {x₀ : Y} (g : Y)
    (hx₀ : x₀ ∈ Subgroup.normalizer (V : Set Y)) (hx₀5 : orderOf x₀ = 5)
    (hfix : ∀ m ∈ Subgroup.normalizer (V : Set Y), m * x₀ * m⁻¹ ∈ Hy.map (cm g)) :
    NoNonHBlockAt Hy V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro L hL hLp hP
  refine Or.inl ⟨g, ?_⟩
  obtain ⟨V₀, Q, -, hQL, hQ2, hLQ, -, -, α, hα, hαQ, -⟩ := hL
  have hLN : L ≤ Subgroup.normalizer (V : Set Y) := by
    rw [← hP]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hP' : ¬ 5 ^ 2 ∣ Nat.card (Subgroup.normalizer (V : Set Y)) := fun hd =>
    hY (hd.trans (Subgroup.card_subgroup_dvd_card _))
  refine le_of_five_elements hQ2 hQL α hα hαQ hLp (N := Hy.map (cm g)) ?_
  intro y hyL hy5
  obtain ⟨m, hm, k, hk⟩ := Kc3J4.exists_conj_of_orderOf_prime (p := 5) hP' hx₀ (hLN hyL) hx₀5 hy5
  have hy : y = (m * x₀ * m⁻¹) ^ k := by
    rw [hk, conj_zpow]
  rw [hy]
  exact zpow_mem (hfix m hm) k

end CFSG.QuasithinUnique.A5
