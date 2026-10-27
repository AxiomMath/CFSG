module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec26
public import CFSG.LocalAnalysis.OddStandard.Seitz77WData
public import CFSG.CGT.Timmesfeld75.StronglyClosedSimple

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.CGT.Timmesfeld75

theorem seitz26 (hG : Goldschmidt1974) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {S W V₁ : Subgroup G} {t : G}
    (hS : IsSylowOf 2 S (normalizer (W : Set G))) (hWS : W ≤ S) (hW : IsElemAbelian 2 W)
    (hcardW : Nat.card W = 2 ^ 8) (htS : t ∈ S) (ht2 : t * t = 1) (htW : t ∉ W)
    (hCt : W ⊓ centralizer ({t} : Set G) = V₁) (hcardV₁ : Nat.card V₁ = 16)
    (hR2 : ∀ s ∈ S, s ∉ W ⊔ zpowers t → Nat.card ↥(W ⊓ centralizer ({s} : Set G)) ≤ 16)
    (hR1 : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B → W.relIndex B ≤ 8) : False :=
  Sec26.seitz26_core hS hWS hW hcardW htS ht2 htW hCt hcardV₁ hR2 hR1
    (fun T _ hA1 hAT hAab hcl x hx hx2 =>
      stronglyClosed_contains_involutions hG hnab T hA1 hAT
        ⟨⟨fun a b => Subtype.ext (hAab a.1 a.2 b.1 b.2)⟩⟩ hcl x hx hx2)

theorem WData.not_isSylowOf {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}
    {V₁ : Subgroup G} (hG : Goldschmidt1974) (h : Hyp G A) (w : WData d V₁) :
    ¬ IsSylowOf 2 w.S (normalizer (w.W : Set G)) := fun hsyl => by
  have := h.simple
  have ht2 : d.t * d.t = 1 := by
    have h2 := pow_orderOf_eq_one d.t
    rw [d.sector.t_order, sq] at h2
    exact h2
  exact seitz26 hG h.nonab hsyl w.hWS w.hW_elem w.hW_card w.ht_mem ht2 w.ht_not_mem w.hCt
    w.hV₁_card w.hR2 w.hR1

end CFSG.OddStandard.Seitz77
