module

public import CFSG.CGT.PushingUpLit.EightOneBlocksConj

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open EightOneBlocks
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_closed_of_conjugate {X L : Subgroup G} (hX : InClassX ↥X) (hL : InClassX ↥L)
    (hXL : X ≤ L) (hne : X ≠ L) (harrow : Arrow X L) {C : Set G} (h1 : (1 : G) ∈ C)
    (hCL : C ⊆ L) (hC : ∀ a ∈ C, ∀ b ∈ L, ⁅conjugate X a, conjugate X b⁆ ≠ ⊥ → b ∈ C) :
    ∀ l ∈ L, l ∈ C := by
  intro b₀ hb₀L
  by_contra hb₀C
  set L₁ : Subgroup G := ⨆ a ∈ C, conjugate X a
  have hconjL₁ : ∀ a ∈ C, conjugate X a ≤ L₁ := fun a ha =>
    le_iSup₂ (f := fun a (_ : a ∈ C) => conjugate X a) a ha
  have hL₁L : L₁ ≤ L := iSup₂_le fun a ha =>
    CFSG.GroupTheory.conjugate_le_of_mem hXL (hCL ha)
  have hXL₁ : X ≤ L₁ := by
    have h := hconjL₁ 1 h1
    rwa [ThreeFromEight.conjugate_one] at h
  have hcent : ∀ b ∈ L, b ∉ C → conjugate X b ≤ Subgroup.centralizer (L₁ : Set G) := by
    intro b hb hbC
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine iSup₂_le fun a ha => ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    by_contra hne'
    exact hbC (hC a ha b hb hne')
  have hnorm : L ≤ Subgroup.normalizer (L₁ : Set G) := by
    calc L = ⨆ l ∈ L, conjugate X l := (conjClosure_eq hX hL hXL hne harrow).symm
      _ ≤ Subgroup.normalizer (L₁ : Set G) := by
        refine iSup₂_le fun l hl => ?_
        by_cases hlC : l ∈ C
        · exact (hconjL₁ l hlC).trans Subgroup.le_normalizer
        · exact (hcent l hl hlC).trans (Subgroup.centralizer_le_normalizer _)
  have hL₁eq : L₁ = L :=
    eq_of_le_normalizer_of_not_le_oTwoIn hL.1 (arrow_top_simple hX hL hXL hne harrow).1 hL₁L hnorm
      (not_le_oTwoIn_of_inClassX hX hXL₁)
  have hYL₁ : conjugate X b₀ ≤ L₁ := hL₁eq ▸ CFSG.GroupTheory.conjugate_le_of_mem hXL hb₀L
  refine InClassX.commutator_ne_bot (inClassX_conjugate hX b₀) ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact (hcent b₀ hb₀L hb₀C).trans (Subgroup.centralizer_le hYL₁)

theorem le_of_arrow_block {N X L L' : Subgroup G} (hN : IsCharacteristicP 2 ↥N)
    (hX : InClassX ↥X) (hL : InClassX ↥L) (hXL : X ≤ L) (hLN : L ≤ N) (hne : X ≠ L)
    (harrow : Arrow X L) (hL' : IsBlockOfInX N L') (hXL' : X ≤ L') : L ≤ L' := by
  have hlabel : ∀ a ∈ L, ∀ b ∈ L, ⁅conjugate X a, conjugate X b⁆ ≠ ⊥ →
      conjugate L' a = conjugate L' b := by
    intro a ha b hb hcomm
    by_contra hne'
    refine hcomm (le_bot_iff.1 ?_)
    calc ⁅conjugate X a, conjugate X b⁆ ≤ ⁅conjugate L' a, conjugate L' b⁆ :=
          Subgroup.commutator_mono (CFSG.GroupTheory.conjugate_mono a hXL')
            (CFSG.GroupTheory.conjugate_mono b hXL')
      _ = ⊥ := distinct_blocks_commute_of_isBlockOfInX hN (isBlockOfInX_conjugate hL' (hLN ha))
          (isBlockOfInX_conjugate hL' (hLN hb)) hne'
  have hall : ∀ l ∈ L, conjugate L' l = L' := by
    intro l hl
    have h := mem_of_closed_of_conjugate hX hL hXL hne harrow
      (C := {a | a ∈ L ∧ conjugate L' a = L'}) ⟨one_mem L, ThreeFromEight.conjugate_one L'⟩
      (fun a ha => ha.1) (fun a ha b hb hab => ⟨hb, (hlabel b hb a ha.1 (by
        rwa [Subgroup.commutator_comm])).trans ha.2⟩) l hl
    exact h.2
  have hLnorm : L ≤ Subgroup.normalizer (L' : Set G) := fun l hl => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← ThreeFromEight.mem_conjugate_iff (H := L') (g := l), hall l hl]
  have hnorm : L ≤ Subgroup.normalizer ((L ⊓ L' : Subgroup G) : Set G) := fun l hl => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) x
    have h2 := Subgroup.mem_normalizer_iff.1 (hLnorm hl) x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  have hinf : L ⊓ L' = L :=
    eq_of_le_normalizer_of_not_le_oTwoIn hL.1 (arrow_top_simple hX hL hXL hne harrow).1 inf_le_left
      hnorm (not_le_oTwoIn_of_inClassX hX (le_inf hXL hXL'))
  exact inf_eq_left.1 hinf

end CFSG.CGT.PushingUpLit
