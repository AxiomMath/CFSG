module

public import CFSG.GH74.Uniqueness.SU.KI6Simple
public import CFSG.GH74.Uniqueness.Bender.OuterFinal
public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.Monster.B.GSide.GenericStrongEmbedding

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup

theorem bender34c : Bender34c := by
  intro L _ _ hB α hα D hD hfix
  by_contra hnot
  obtain ⟨hDne, -, -, S, hS⟩ := (CFSG.Monster.B.GSide.isStronglyEmbeddedOrder_iff).mp hD
  obtain ⟨n, i, e, hT⟩ := CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp hB
  have hSD : (S : Subgroup L) ≤ D := Subgroup.le_normalizer.trans hS
  have hDS : D ≤ normalizer (S : Set L) := hT.le_borel_of_sylow_le S hSD hDne
  have hα' : α * α = 1 := by rw [← pow_two]; exact hα
  obtain ⟨-, hx⟩ := CFSG.GH74.Uniqueness.Bender.bender_outer_involution hB α hα' hnot
  obtain ⟨x, hxα, hxn⟩ := hx S
  exact hxn (hDS (hfix x hxα))

end CFSG.GH74.Uniqueness.SU.K.R6
