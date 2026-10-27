module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3OuterCentralizer

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic

section Main


set_option linter.unusedSectionVars false

theorem R_key {W E' : Subgroup (Equiv.Perm (Fin 6156))} (hW : W ≤ j3R) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hW4 : Nat.card W ≤ 4) (hE'P : E' ≤ j3P) (hE'3 : ∀ x ∈ E', x ^ 3 = 1)
    (hE'9 : 9 ≤ Nat.card E')
    (hodd : ∀ b ∈ E', b ≠ 1 →
      Odd (Nat.card (centralizer ({b} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156)))))
    (hN : ∀ b ∈ E', ∀ w ∈ W, b * w * b⁻¹ ∈ W) : W = ⊥ := by
  obtain ⟨hU2, -, hUP, hmapu, -, hRmem, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  by_contra hne
  obtain ⟨w₀, hw₀W, hw₀1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hno
    push_neg at hno
    exact hne (Subgroup.eq_bot_iff_forall W |>.2 hno)
  have h1 : ∀ w ∈ W, w ≠ 1 → w ∉ j3P := by
    intro w hwW hw1 hwP
    have hw2o : orderOf w = 2 := orderOf_eq_prime (hW2 w hwW) hw1
    let f : E' → W := fun b => ⟨(b : Equiv.Perm (Fin 6156)) * w * (b : Equiv.Perm (Fin 6156))⁻¹,
      hN b b.2 w hwW⟩
    classical
    haveI : Fintype E' := Fintype.ofFinite _
    haveI : Fintype W := Fintype.ofFinite _
    have hlt : Fintype.card W < Fintype.card E' := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; omega
    obtain ⟨b1, b2, hb12, hfb⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
    set b₀ : Equiv.Perm (Fin 6156) := (b1 : Equiv.Perm (Fin 6156))⁻¹ * (b2 : Equiv.Perm (Fin 6156))
      with hb₀
    have hb₀E : b₀ ∈ E' := E'.mul_mem (E'.inv_mem b1.2) b2.2
    have hb₀1 : b₀ ≠ 1 := by
      intro h
      apply hb12
      apply Subtype.ext
      have : (b1 : Equiv.Perm (Fin 6156)) = b2 := by
        have := congrArg (fun x => (b1 : Equiv.Perm (Fin 6156)) * x) h
        simpa [hb₀] using this.symm
      exact this
    have hcomm : w * b₀ = b₀ * w := by
      have h' := congrArg Subtype.val hfb
      simp only [f] at h'
      rw [hb₀]
      calc w * ((b1 : Equiv.Perm (Fin 6156))⁻¹ * b2)
          = (b1 : Equiv.Perm (Fin 6156))⁻¹ * ((b1 : Equiv.Perm (Fin 6156)) * w *
              (b1 : Equiv.Perm (Fin 6156))⁻¹) * b2 := by group
        _ = (b1 : Equiv.Perm (Fin 6156))⁻¹ * ((b2 : Equiv.Perm (Fin 6156)) * w *
              (b2 : Equiv.Perm (Fin 6156))⁻¹) * b2 := by rw [h']
        _ = ((b1 : Equiv.Perm (Fin 6156))⁻¹ * b2) * w := by group
    have hmem : w ∈ (centralizer ({b₀} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) :=
      ⟨mem_centralizer_singleton_iff.2 hcomm, hwP⟩
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hw2o] at hdvd
    exact (Nat.not_even_iff_odd.2 (hodd b₀ hb₀E hb₀1)) (even_iff_two_dvd.2 hdvd)
  have hpar : ∀ w1 ∈ j3R, w1 ∉ j3P → ∀ w2 ∈ j3R, w2 ∉ j3P → w1 * w2 ∈ j3P := by
    intro w1 hw1 hw1P w2 hw2 hw2P
    have h1' : w1 * j3u ∈ j3P := ((hRmem w1).1 hw1).resolve_left hw1P
    have h2' : w2 * j3u ∈ j3P := ((hRmem w2).1 hw2).resolve_left hw2P
    have hu : j3u * (w2 * j3u) * j3u⁻¹ ∈ j3P := by
      rw [← hmapu]
      exact ⟨w2 * j3u, h2', rfl⟩
    have hUU : j3u * j3u = 1 := by rw [← sq, hU2]
    have : w1 * w2 = (w1 * j3u) * (j3u * (w2 * j3u) * j3u⁻¹) := by
      calc w1 * w2 = w1 * (j3u * j3u) * w2 := by rw [hUU]; group
        _ = (w1 * j3u) * (j3u * (w2 * j3u) * j3u⁻¹) := by group
    rw [this]
    exact j3P.mul_mem h1' hu
  have h2 : ∀ w1 ∈ W, w1 ≠ 1 → ∀ w2 ∈ W, w2 ≠ 1 → w1 = w2 := by
    intro w1 hw1W hw11 w2 hw2W hw21
    by_contra hne12
    have hp := hpar w1 (hW hw1W) (h1 w1 hw1W hw11) w2 (hW hw2W) (h1 w2 hw2W hw21)
    have hne : w1 * w2 ≠ 1 := by
      intro h
      apply hne12
      have hsq := hW2 w1 hw1W
      calc w1 = w1 * (w1 * w2) := by rw [h, mul_one]
        _ = w1 ^ 2 * w2 := by rw [← mul_assoc, ← sq]
        _ = w2 := by rw [hsq, one_mul]
    exact h1 (w1 * w2) (W.mul_mem hw1W hw2W) hne hp
  have hcent : E' ≤ centralizer ({w₀} : Set (Equiv.Perm (Fin 6156))) := by
    intro b hb
    rw [mem_centralizer_singleton_iff]
    have hmem := hN b hb w₀ hw₀W
    have hne1 : b * w₀ * b⁻¹ ≠ 1 := by
      intro h
      apply hw₀1
      have : w₀ = b⁻¹ * (b * w₀ * b⁻¹) * b := by group
      rw [this, h]; group
    have := h2 _ hmem hne1 w₀ hw₀W hw₀1
    calc b * w₀ = (b * w₀ * b⁻¹) * b := by group
      _ = w₀ * b := by rw [this]
  exact j3_outer_centralizer_no_elementary_abelian_nine (hW hw₀W)
    (orderOf_eq_prime (hW2 w₀ hw₀W) hw₀1) (h1 w₀ hw₀W hw₀1) hE'P hcent hE'3 hE'9

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
