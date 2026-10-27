module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RB
public import CFSG.ClassicalInvolution.Asc77.WP3Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected

namespace T7P

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


@[expose] def SpinTag (t : StatedLieTag) (k : ℕ) : Prop :=
  (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)

@[expose] def SpinSection (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (u : G) : Prop :=
  ∃ D : CFSG.ClassicalInvolution.Balance.LocalLieSystemAt p f
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.exactFamily Ω u) u,
    D.card = 1 ∧ ∃ j : Fin D.card, SpinTag (D.tag j) (D.rank j)

section Components

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem OmegaLie.dAdj_of_comp_ne (D : OmegaLie p f Φ) (hΦ : HypOmegaMod p f Φ)
    {K J : Subgroup X} (hK : K ∈ Φ) (hJ : J ∈ Φ) {i j : Fin D.card} (hij : i ≠ j)
    (hKi : K ≤ D.comp i) (hJj : J ≤ D.comp j) : dAdj Φ K J := by
  have hcomm : Commutes K J := fun x hx y hy => D.comp_commute hij x (hKi hx) y (hJj hy)
  have hne : K ≠ J := by
    intro h
    obtain ⟨z, hz⟩ := hΦ.classical K hK
    obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hz
    exact hxy (hcomm x hx y (h ▸ hy))
  exact dAdj_of_commutes hJ hne hcomm

theorem OmegaLie.dConnected_of_two_le_card (D : OmegaLie p f Φ) (hΦ : HypOmegaMod p f Φ)
    (h2 : 2 ≤ D.card) : DConnected Φ := by
  intro K hK J hJ
  obtain ⟨i, hKi⟩ := D.exists_comp_of_mem hK
  obtain ⟨j, hJj⟩ := D.exists_comp_of_mem hJ
  by_cases hij : i = j
  · subst hij
    obtain ⟨k, hki⟩ : ∃ k : Fin D.card, k ≠ i := by
      by_cases h0 : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by
          have := congrArg Fin.val h
          simp at this
          omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => by
          have := congrArg Fin.val h
          simp at this
          omega⟩
    obtain ⟨R, -, hRΦ⟩ := D.meets k
    have hRk : R.map (D.hom k) ≤ D.comp k := Subgroup.map_le_range _ _
    exact (Relation.ReflTransGen.single
      ⟨hRΦ, OmegaLie.dAdj_of_comp_ne D hΦ hK hRΦ hki.symm hKi hRk⟩).tail
      ⟨hJ, OmegaLie.dAdj_of_comp_ne D hΦ hRΦ hJ hki hRk hJj⟩
  · exact Relation.ReflTransGen.single ⟨hJ, OmegaLie.dAdj_of_comp_ne D hΦ hK hJ hij hKi hJj⟩

theorem OmegaLie.card_eq_one_of_not_dConnected (D : OmegaLie p f Φ) (hΦ : HypOmegaMod p f Φ)
    (hne : Φ.Nonempty) (hdisc : ¬ DConnected Φ) : D.card = 1 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨i, -⟩ := D.exists_comp_of_mem hK
  have hpos : 0 < D.card := i.pos
  by_contra h1
  exact hdisc (OmegaLie.dConnected_of_two_le_card D hΦ (by omega))

end Components

section Tag

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem tag_of_twinShape_dDisc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Φ.Nonempty)
    {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Φ t k e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hshape : TwinShape t k)
    (hdisc : ¬ DConnected Φ) :
    (t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨ SpinTag t k := by
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4 with hc | hsmall
  · exact absurd (M.dConnected_of_connected hp2 hq hne hG2 hD4 hc) hdisc
  rcases hshape with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hk : k = 3 := T7S2R.smallModel_odd hsmall
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hk⟩)))
  · have hk : k = 4 := T7S2R.smallModel_plus hsmall
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hk⟩))))
  · have hk : k = 4 := T7S2R.smallModel_minus hsmall
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hk⟩))))
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

end Tag

end T7P

end CFSG.ClassicalInvolution.Asc77
