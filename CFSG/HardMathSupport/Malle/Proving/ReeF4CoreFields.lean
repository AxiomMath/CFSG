module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Malle.Proving

open CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def centreOfSub (T : Subgroup Y) : Subgroup Y := T ⊓ Subgroup.centralizer (T : Set Y)

omit [Finite Y] in
theorem mem_centreOfSub {T : Subgroup Y} {z : Y} :
    z ∈ centreOfSub T ↔ z ∈ T ∧ ∀ t ∈ T, t * z = z * t := by
  simp [centreOfSub, Subgroup.mem_centralizer_iff]

omit [Finite Y] in
theorem conj_mem_centreOfSub {T : Subgroup Y} {g z : Y}
    (hg : g ∈ Subgroup.normalizer (T : Set Y)) (hz : z ∈ centreOfSub T) :
    g * z * g⁻¹ ∈ centreOfSub T := by
  obtain ⟨hzT, hzc⟩ := mem_centreOfSub.1 hz
  rw [mem_centreOfSub]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzT, ?_⟩
  intro s hs
  have hu : g⁻¹ * s * g⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) s).mp hs
  rw [inv_inv] at hu
  have h1 := hzc _ hu
  calc s * (g * z * g⁻¹) = g * (g⁻¹ * s * g * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * s := by group

omit [Finite Y] in
theorem le_normalizer_centreOfSub_of_le {T Y₀ : Subgroup Y}
    (hle : Y₀ ≤ Subgroup.normalizer (T : Set Y)) :
    Y₀ ≤ Subgroup.normalizer ((centreOfSub T : Subgroup Y) : Set Y) := by
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (T : Set Y) := hle hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hz => conj_mem_centreOfSub hgN hz, fun hz => ?_⟩
  have := conj_mem_centreOfSub (inv_mem hgN) hz
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem natCard_sylow_eq_pow (P : Sylow 5 Y) : ∃ k : ℕ, Nat.card (P : Subgroup Y) = 5 ^ k := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact IsPGroup.iff_card.mp P.isPGroup'

end CFSG.HardMathSupport.Malle.Proving
