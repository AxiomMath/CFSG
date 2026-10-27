module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Factor81
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.SylowPermute

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type*} [Group G] [Finite G]

theorem card_mul_card_le_card_mul_card_inf {W E U : Subgroup G} (hEW : E ≤ W) (hUW : U ≤ W) :
    Nat.card E * Nat.card U ≤ Nat.card W * Nat.card (E ⊓ U : Subgroup G) := by
  have hIW : E ⊓ U ≤ W := inf_le_left.trans hEW
  have key : ∀ {K : Subgroup G}, K ≤ W → Nat.card K * K.relIndex W = Nat.card W := by
    intro K hKW
    have h1 := Subgroup.relIndex_mul_index hKW
    have h2 := Subgroup.card_mul_index K
    have h3 := Subgroup.card_mul_index W
    have hpos : 0 < W.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card K * K.relIndex W * W.index = Nat.card K * (K.relIndex W * W.index) := by ring
      _ = Nat.card K * K.index := by rw [h1]
      _ = Nat.card G := h2
      _ = Nat.card W * W.index := h3.symm
  have hE := key hEW
  have hU := key hUW
  have hI := key hIW
  have hle : (E ⊓ U).relIndex W ≤ E.relIndex W * U.relIndex W := Subgroup.relIndex_inf_le
  have hEpos : 0 < E.relIndex W := by
    rcases Nat.eq_zero_or_pos (E.relIndex W) with h | h
    · rw [h, mul_zero] at hE; exact absurd hE.symm Nat.card_pos.ne'
    · exact h
  have hUpos : 0 < U.relIndex W := by
    rcases Nat.eq_zero_or_pos (U.relIndex W) with h | h
    · rw [h, mul_zero] at hU; exact absurd hU.symm Nat.card_pos.ne'
    · exact h
  have hprod : 0 < E.relIndex W * U.relIndex W := Nat.mul_pos hEpos hUpos
  apply Nat.le_of_mul_le_mul_right _ hprod
  calc Nat.card E * Nat.card U * (E.relIndex W * U.relIndex W)
      = (Nat.card E * E.relIndex W) * (Nat.card U * U.relIndex W) := by ring
    _ = Nat.card W * Nat.card W := by rw [hE, hU]
    _ = Nat.card W * (Nat.card (E ⊓ U : Subgroup G) * (E ⊓ U).relIndex W) := by rw [hI]
    _ ≤ Nat.card W * (Nat.card (E ⊓ U : Subgroup G) * (E.relIndex W * U.relIndex W)) := by
        gcongr
    _ = Nat.card W * Nat.card (E ⊓ U : Subgroup G) * (E.relIndex W * U.relIndex W) := by ring

theorem false_of_E81_small_factor {W E A' U : Subgroup G} (hEW : E ≤ W)
    (hEel : IsElemAbelian 3 E) (hEc : Nat.card E = 81) (hA'W : A' ≤ W) (hUW : U ≤ W)
    (hA3 : Nat.card A' ≤ 3) (hU9 : ¬ IsCyclic U → Nat.card U ≤ 9)
    (hfac : ∀ w ∈ W, ∃ a ∈ A', ∃ u ∈ U, w = a * u) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWle : Nat.card W ≤ Nat.card A' * Nat.card U := by
    let f : A' × U → W := fun p => ⟨(p.1 : G) * (p.2 : G), W.mul_mem (hA'W p.1.2) (hUW p.2.2)⟩
    have hsurj : Function.Surjective f := by
      intro w
      obtain ⟨a, ha, u, hu, hw⟩ := hfac w w.2
      exact ⟨(⟨a, ha⟩, ⟨u, hu⟩), Subtype.ext hw.symm⟩
    have := Nat.card_le_card_of_surjective f hsurj
    simpa [Nat.card_prod] using this
  have hEWle : Nat.card E ≤ Nat.card W := Subgroup.card_le_of_le hEW
  have hUpos : 0 < Nat.card U := Nat.card_pos
  by_cases hcyc : IsCyclic U
  · have hEU : Nat.card (E ⊓ U : Subgroup G) ≤ 3 := by
      have hcyc' : IsCyclic (E ⊓ U : Subgroup G) := Subgroup.isCyclic_of_le inf_le_right
      exact card_le_of_isElemAbelian_of_isCyclic (isElemAbelian_of_le hEel inf_le_left) hcyc'
    have hP := card_mul_card_le_card_mul_card_inf hEW hUW
    rw [hEc] at hP
    have h1 : Nat.card W * Nat.card (E ⊓ U : Subgroup G) ≤ Nat.card W * 3 :=
      Nat.mul_le_mul_left _ hEU
    have h2 : Nat.card W ≤ 3 * Nat.card U := hWle.trans (Nat.mul_le_mul_right _ hA3)
    nlinarith
  · have hU9' := hU9 hcyc
    have : Nat.card W ≤ 3 * 9 := hWle.trans (Nat.mul_le_mul hA3 hU9')
    omega

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
