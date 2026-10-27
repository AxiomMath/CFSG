module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Fus

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CF23L4U4O8Comp : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    (Blueprint.LieModel N .PSL 4 p f ∨ Blueprint.LieModel N .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel N .POmegaMinus 4 p e) →
    ∀ G : Subgroup (MulAut N), (MulAut.conj : N →* MulAut N).range ≤ G →
    ∀ (α : G) (J : Subgroup G), orderOf α = 2 →
      J ≤ (MulAut.conj : N →* MulAut N).range.subgroupOf G →
      J ≤ centralizer ({α} : Set G) → IsComponent (J.subgroupOf (centralizer ({α} : Set G))) →
      IsStandardSubgroup J → Odd (Nat.card (center J)) →
      (Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 7)) ∨
        ∃ s t : ℕ, s.Prime ∧ s ≠ 2 ∧ 1 ≤ t ∧ 5 ≤ s ^ t ∧
          Blueprint.LieModel (J ⧸ center J) .PSL 2 s t) →
      Blueprint.LieModel (J ⧸ center J) .PSL 2 p (2 * f)

namespace Cov

open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.GSThmB.Fus23

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

include hKa in
theorem table54_of_l4u4 (hL4 : CF23L4U4O8Comp) (hZJ : center (OddBar h.J) = ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hN : Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
      Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p e) :
    h.Table54 := by
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  obtain ⟨eJ⟩ := nonempty_Jhat_equiv hKa hZJ
  have hNL : Blueprint.LieModel (LK h) .PSL 4 p f ∨ Blueprint.LieModel (LK h) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (LK h) .POmegaMinus 4 p e := by
    rcases hN with hm | hm | ⟨e, he, hm⟩
    · exact Or.inl (OddQuot.lieModel_of_equiv eZ.symm hm)
    · exact Or.inr (Or.inl (OddQuot.lieModel_of_equiv eZ.symm hm))
    · exact Or.inr (Or.inr ⟨e, he, OddQuot.lieModel_of_equiv eZ.symm hm⟩)
  have hJt : Nonempty (↥(Jhat hKa) ⧸ center ↥(Jhat hKa) ≃* alternatingGroup (Fin 7)) ∨
      ∃ s t : ℕ, s.Prime ∧ s ≠ 2 ∧ 1 ≤ t ∧ 5 ≤ s ^ t ∧
        Blueprint.LieModel (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) .PSL 2 s t := by
    rcases hJ with ⟨⟨e7⟩⟩ | ⟨s, t, hs, hs2, ht, hst, hm⟩
    · exact Or.inl ⟨eJ.trans e7⟩
    · exact Or.inr ⟨s, t, hs, hs2, ht, hst, OddQuot.lieModel_of_equiv eJ.symm hm⟩
  have hmJ := OddQuot.lieModel_of_equiv eJ
    (hL4 (LK h) p f hp hp2 hf hNL (GAut hKa) (inn_le_GAut hKa) (phi hKa (abar h)) (Jhat hKa)
      (orderOf_phi_abar' hKa) (Jhat_le_NL hKa) (Jhat_component hKa).1 (Jhat_component hKa).2
      (Jhat_standard hKa) (odd_card_center_Jhat hKa hZJ) hJt)
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hmJ, hKa, hN⟩)))

end Cov

end CFSG.ComponentClassification.GSThmB
