module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisFrobenius

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Field

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem pow_four_eq (hK : Nat.card K = 4) (x : K) : x ^ 4 = x := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem exists_add_sq_eq (hK : Nat.card K = 4) {t : K} (ht : t ^ 2 = t) :
    ∃ s : K, s + s ^ 2 = t := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases ht0 : t = 0
  · exact ⟨0, by simp [ht0]⟩
  · have ht1 : t = 1 := by
      have : t * (t - 1) = 0 := by linear_combination ht
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h ht0
      · linear_combination h
    by_contra hcon
    push Not at hcon
    have hall : ∀ s : K, s = 0 ∨ s = 1 := by
      intro s
      have hsq : (s + s ^ 2) ^ 2 = s + s ^ 2 := by
        have h4 := pow_four_eq hK s
        linear_combination (s ^ 3) * h2 + h4
      have : (s + s ^ 2) * (s + s ^ 2 - 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.1 this with h | h
      · have : s * (s - 1) = 0 := by linear_combination h - s * h2
        rcases mul_eq_zero.1 this with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by linear_combination h')
      · exact absurd (by linear_combination h - ht1 : s + s ^ 2 = t) (hcon s)
    have : Nat.card K ≤ 2 := by
      have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
        intro s
        rcases hall s with h | h
        · exact ⟨false, by simp [h]⟩
        · exact ⟨true, by simp [h]⟩
      have := Nat.card_le_card_of_surjective _ hsurj
      simpa using this
    omega

theorem h90_solve (hK : Nat.card K = 4) {a b c d : K} (h1 : a + a ^ 2 = 0) (h2 : d + d ^ 2 = 0)
    (h3 : b + b ^ 2 + a * d ^ 2 = 0)
    (h4 : c + c ^ 2 + a * b ^ 2 + a * a ^ 2 * d ^ 2 + b * a ^ 2 = 0) :
    ∃ α β γ δ : K, α + α ^ 2 = a ∧ δ + δ ^ 2 = d ∧ (β + α * δ) + β ^ 2 + α * δ ^ 2 = b ∧
      γ + γ ^ 2 + α * β ^ 2 + α * α ^ 2 * δ ^ 2 + (β + α * δ) * α ^ 2 = c := by
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha2 : a ^ 2 = a := by linear_combination h1 - a * h2'
  have hd2 : d ^ 2 = d := by linear_combination h2 - d * h2'
  obtain ⟨α, hα⟩ := exists_add_sq_eq hK ha2
  obtain ⟨δ, hδ⟩ := exists_add_sq_eq hK hd2
  have hb' : (b + α * d) ^ 2 = b + α * d := by
    linear_combination h3 + d ^ 2 * hα - α * hd2 + (-b + α * b * d - α * d) * h2'
  obtain ⟨β, hβ⟩ := exists_add_sq_eq hK hb'
  have hc2 : c ^ 2 = c := by
    linear_combination h4 - c * h2' - a * h3 - (a * d ^ 2 + b) * ha2
  have hα4 := pow_four_eq hK α
  have hβ4 := pow_four_eq hK β
  have hδ4 := pow_four_eq hK δ
  set Y : K := α * β ^ 2 + α * α ^ 2 * δ ^ 2 + (β + α * δ) * α ^ 2 with hY
  have ht : (c + Y) ^ 2 = c + Y := by
    rw [hY]
    linear_combination (c * (α * β ^ 2) + c * (α * α ^ 2 * δ ^ 2) + c * (β * α ^ 2) +
      c * (α * α ^ 2 * δ) + (α * β ^ 2) * (α * α ^ 2 * δ ^ 2) + (α * β ^ 2) * (β * α ^ 2) +
      (α * β ^ 2) * (α * α ^ 2 * δ) + (α * α ^ 2 * δ ^ 2) * (β * α ^ 2) +
      (α * α ^ 2 * δ ^ 2) * (α * α ^ 2 * δ) + (β * α ^ 2) * (α * α ^ 2 * δ)) * h2' + hc2 +
      α ^ 2 * hβ4 + α ^ 6 * hδ4 + (δ * α ^ 2 + β ^ 2 + δ ^ 2 * α ^ 2) * hα4
  obtain ⟨γ, hγ⟩ := exists_add_sq_eq hK ht
  refine ⟨α, β, γ, δ, hα, hδ, ?_, ?_⟩
  · linear_combination hβ + α * hδ + (α * d) * h2'
  · linear_combination hγ + Y * h2'

end Field

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem antiUnipotent_h90 (hK : Nat.card K = 4) {u : antiSp K} (hu : u ∈ antiUnipotent K)
    (hc : u * frobAut K u = 1) : ∃ v ∈ antiUnipotent K, u = v⁻¹ * frobAut K v := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  rw [frobAut_uElt, uElt_mul, ← uElt_zero_eq_one] at hc
  obtain ⟨e1, e2, e3, e4⟩ := uElt_inj hc
  obtain ⟨α, β, γ, δ, hα, hδ, hb, hcc⟩ := h90_solve hK e1 e4 e2 e3
  refine ⟨uElt α β γ δ, uElt_mem_antiUnipotent _ _ _ _, ?_⟩
  rw [frobAut_uElt, uElt_inv, uElt_mul, hα, hb, hcc, hδ]

theorem frobAut_mem_antiUnipotent {u : antiSp K} (hu : u ∈ antiUnipotent K) :
    frobAut K u ∈ antiUnipotent K := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  rw [frobAut_uElt]
  exact uElt_mem_antiUnipotent _ _ _ _

end Group

end CFSG.EvenSporadicStandard.M22Std
