module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndBlk

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.extremal_type
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B) {g : G}
    (hR : 2 * Nat.card S ≤ Nat.card ↥((S ⊔ Bp A t) ⊓ centralizer ({g⁻¹ * t * g} : Set G)))
    (huP : g⁻¹ * t * g ∈ S ⊔ Bp A t) :
    (∃ d₁ ∈ D, g⁻¹ * t * g = d₁ * t ∧ d₁ ^ 2 = theta t d₁ ∧
        ∀ s ∈ S, d₁ * s * d₁⁻¹ * s⁻¹ ∈ A) ∨
      (∃ d₁ ∈ Aa, g⁻¹ * t * g = d₁ * (b * t) ∧
        ∀ s ∈ S, (d₁ * b) * s * (d₁ * b)⁻¹ * s⁻¹ ∈ A) := by
  have hBLK := H.blk_extremal W W2 hD hAb hZ hR huP
  obtain ⟨-, hcard, -, -, d₁, hd₁, hu⟩ := H.ext_extremal_of_card W W2 hD hAb hZ
    (H.isPGroup_S_sup_Bp W)
    (sup_le le_sup_left (zpowers_le.2 (mem_sup_right (H.t_mem_Bp W W2)))) le_sup_right
    (H.S_sup_Bp_le_normalizer W) hR huP
  rcases hu with h | h | h
  · obtain ⟨h1, h2⟩ := H.blk_cons_t W W2 hD hd₁ h hBLK
    exact Or.inl ⟨d₁, hd₁, h, h1, h2⟩
  · exact (H.not_extremal_Db W W2 hD hAb hEl hZ hd₁ h hR huP).elim
  · have hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹ := by
      rcases H.D_cases W W2 hD hEl with ⟨-, -, h2⟩ | ⟨-, hb, -, -⟩
      · exfalso
        rw [h, inf_centralizer_mul_eq hD.comm hd₁, h2, W.A_card] at hcard
        norm_num at hcard
      · exact hb
    obtain ⟨h1, h2⟩ := H.blk_cons_bt W W2 hD hb hd₁ h hBLK
    exact Or.inr ⟨d₁, h1, h, h2⟩

end

end CFSG.EvenSporadicStandard.ThStd
