module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourFour
public import CFSG.LocalAnalysis.EvenBN.G2.LocalYThirtyOne

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup

namespace LocalQFourUniformAux

theorem eight_le_or_eq_four {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
    (h : Setup G L f t) {K : Type} (hK : Nat.card K = 2 ^ f) :
    8 ≤ Nat.card K ∨ Nat.card K = 4 := by
  by_cases h8 : 8 ≤ Nat.card K
  · exact Or.inl h8
  refine Or.inr ?_
  have hf3 : f < 3 := by
    by_contra hf
    exact h8 (hK ▸ (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ 3 ≤ 2 ^ f))
  have hf2 : 2 ≤ f := h.two_le
  rw [hK, show f = 2 by omega]
  norm_num

end LocalQFourUniformAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaM₃_le_centralizer_yamadaY₂_four (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hK4 : Nat.card K = 4) : yamadaM₃ d t ≤ centralizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, -, -, ⟨hL, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  exact h.le_centralizer_yamadaY₂_four hW d hK hD hK4 (le_sup_left.trans hL.le)
    (h.yamadaM₃_inf_yamadaL₂ hW d hK hD).le fun j hj =>
      h.yamada_5_30_3 hW d hK hD (Subgroup.mem_inf.2 ⟨d.image_le _ hj,
        (h.centralizer_inf_normalizer_S_le d hK hD).2.2 (hJC (hJ₁J hj))⟩)

theorem yamadaX₄_le_centralizer_yamadaY₂_four (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hK4 : Nat.card K = 4) : yamadaX₄ d t ≤ centralizer (yamadaY₂ d t : Set G) := by
  obtain ⟨hX₄R₄, hX₄R₂, hJX₄⟩ := h.yamadaX₄_le_yamadaR₄ hW d hK hD
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  exact h.le_centralizer_yamadaY₂_four_of_le_yamadaR₄ hW d hK hD hK4 hX₄R₄ hX₄R₂.le
    fun j hj => hJX₄ (hJ₁J hj)

theorem yamadaM₃_le_centralizer_yamadaY₂_uniform (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaM₃ d t ≤ centralizer (yamadaY₂ d t : Set G) := by
  rcases LocalQFourUniformAux.eight_le_or_eq_four h hK with h8 | hK4
  · exact h.yamadaM₃_le_centralizer_yamadaY₂ hW d hK h8
  · exact h.yamadaM₃_le_centralizer_yamadaY₂_four hW d hK hD hK4

theorem yamada_5_33_3_uniform (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    CFSG.IsElementaryAbelian 2 (yamadaW₃ d t) ∧ Nat.card (yamadaW₃ d t) = Nat.card K ^ 6 ∧
      yamadaL₃ d t ⊓ centralizer (yamadaW₂ d t : Set G) = yamadaW₃ d t ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) ≤
        normalizer (yamadaW₃ d t : Set G) :=
  h.yamadaW₃_core hW d hK hD
    ((le_sup_left : yamadaW₃ d t ≤ yamadaM₃ d t).trans
      (h.yamadaM₃_le_centralizer_yamadaY₂_uniform hW d hK hD))

theorem yamada_5_33_1_S₃_uniform (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaS₃ d t ⊓ centralizer (yamadaS₃ d t : Set G) = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₃ d t) 1).map (yamadaS₃ d t).subtype =
        yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₃ d t) 2).map (yamadaS₃ d t).subtype =
        yamadaY₂ d t := by
  have hYW : yamadaW₃ d t ≤ centralizer (yamadaY₂ d t : Set G) :=
    (le_sup_left : yamadaW₃ d t ≤ yamadaM₃ d t).trans
      (h.yamadaM₃_le_centralizer_yamadaY₂_uniform hW d hK hD)
  refine h.yamadaS₃_center hW d hK hD
    (hYW.trans (Subgroup.centralizer_le (yamadaU₁_le_yamadaY₂ d t))) fun w hw y hy => ?_
  rw [show w * y * w⁻¹ * y⁻¹ = 1 by
    rw [← mem_centralizer_iff.1 (hYW hw) y hy]
    group]
  exact one_mem _

theorem yamada_5_33_1_S₄_uniform (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaS₄ d t ⊓ centralizer (yamadaS₄ d t : Set G) = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₄ d t) 1).map (yamadaS₄ d t).subtype =
        yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₄ d t) 2).map (yamadaS₄ d t).subtype =
        yamadaY₂ d t := by
  rcases LocalQFourUniformAux.eight_le_or_eq_four h hK with h8 | hK4
  · exact h.yamada_5_33_1_S₄ hW d hK h8
  · have hYX := h.yamadaX₄_le_centralizer_yamadaY₂_four hW d hK hD hK4
    refine h.yamadaS₄_center hW d hK hD
      (hYX.trans (Subgroup.centralizer_le (yamadaU₁_le_yamadaY₂ d t))) fun w hw y hy => ?_
    rw [show w * y * w⁻¹ * y⁻¹ = 1 by
      rw [← mem_centralizer_iff.1 (hYX hw) y hy]
      group]
    exact one_mem _

theorem yamadaS₃_le_centralizer_yamadaU₁_uniform (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaS₃ d t ≤ centralizer (yamadaU₁ d t : Set G) := by
  rw [← Subgroup.le_centralizer_iff]
  exact (h.yamada_5_33_1_S₃_uniform hW d hK hD).1.ge.trans inf_le_right

theorem yamadaS₄_le_centralizer_yamadaU₁_uniform (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaS₄ d t ≤ centralizer (yamadaU₁ d t : Set G) := by
  rw [← Subgroup.le_centralizer_iff]
  exact (h.yamada_5_33_1_S₄_uniform hW d hK hD).1.ge.trans inf_le_right

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
