module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyHigh

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.LieEmbed

local instance e6PilotCoverFamilyNeighbourNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def nbLo : E6Neighbour → Fin 6 → Fin 6
  | .high => a5Lo
  | .six => ![3, 0, 2, 1, 0, 0]
  | .three => ![0, 4, 0, 0, 2, 1]

@[expose] def nbHi : E6Neighbour → Fin 6 → Fin 6
  | .high => a5Hi
  | .six => ![4, 1, 3, 2, 1, 1]
  | .three => ![1, 5, 1, 1, 3, 2]

@[expose] def nbFree : E6Neighbour → Fin 6
  | .high => 0
  | .six => 5
  | .three => 0

theorem nbLo_ne_nbHi (N : E6Neighbour) (j : Fin 6) : nbLo N j ≠ nbHi N j := by
  cases N <;> revert j <;> decide

theorem nbFree_check :
    (∀ j ∈ ({0, 1, 2, 3} : Finset (Fin 6)), nbLo .six j ≠ nbFree .six ∧
      nbHi .six j ≠ nbFree .six) ∧
    ∀ j ∈ ({1, 4, 5} : Finset (Fin 6)), nbLo .three j ≠ nbFree .three ∧
      nbHi .three j ≠ nbFree .three := by
  decide

theorem weyl_six_check :
    E6Neighbour.six.weyl • a5Root (nbLo .six 0) (nbHi .six 0) = Pi.single 0 1 ∧
    E6Neighbour.six.weyl • a5Root (nbLo .six 1) (nbHi .six 1) = Pi.single 1 1 ∧
    E6Neighbour.six.weyl • a5Root (nbLo .six 2) (nbHi .six 2) = Pi.single 2 1 ∧
    E6Neighbour.six.weyl • a5Root (nbLo .six 3) (nbHi .six 3) = Pi.single 3 1 := by
  simp only [E6Neighbour.weyl, E6Neighbour.word, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem weyl_three_check :
    E6Neighbour.three.weyl • a5Root (nbLo .three 1) (nbHi .three 1) = Pi.single 1 1 ∧
    E6Neighbour.three.weyl • a5Root (nbLo .three 4) (nbHi .three 4) = Pi.single 4 1 ∧
    E6Neighbour.three.weyl • a5Root (nbLo .three 5) (nbHi .three 5) = Pi.single 5 1 := by
  simp only [E6Neighbour.weyl, E6Neighbour.word, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
  refine ⟨?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem a5Root_swap_E6 (i j : Fin 6) : a5Root j i = -a5Root i j := by
  have h := a5Root_add i j i
  have h0 : a5Root i i = 0 := by
    have h2 := a5Root_add i i i
    have h3 : a5Root i i + a5Root i i = a5Root i i + 0 := by rw [add_zero]; exact h2
    exact add_left_cancel h3
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_right h

theorem nb_data {N : E6Neighbour} (hN : N = .six ∨ N = .three) {j : Fin (Tag.rank .E6)}
    (hj : j ∈ N.nodes) :
    N.weyl • a5Root (nbLo N j) (nbHi N j) = Pi.single j 1 ∧ nbLo N j ≠ nbFree N ∧
      nbHi N j ≠ nbFree N := by
  rcases hN with rfl | rfl
  · obtain ⟨h0, h1, h2, h3⟩ := weyl_six_check
    have hj' : (j : Fin 6) ∈ ({0, 1, 2, 3} : Finset (Fin 6)) := hj
    refine ⟨?_, (nbFree_check.1 j hj').1, (nbFree_check.1 j hj').2⟩
    have hj'' : j ∈ ({0, 1, 2, 3} : Finset (Fin (Tag.rank .E6))) := hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj''
    rcases hj'' with rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3]
  · obtain ⟨h1, h4, h5⟩ := weyl_three_check
    have hj' : (j : Fin 6) ∈ ({1, 4, 5} : Finset (Fin 6)) := hj
    refine ⟨?_, (nbFree_check.2 j hj').1, (nbFree_check.2 j hj').2⟩
    have hj'' : j ∈ ({1, 4, 5} : Finset (Fin (Tag.rank .E6))) := hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj''
    rcases hj'' with rfl | rfl | rfl
    exacts [h1, h4, h5]

section Sections


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem rootSpan_le_map_fixBasisSL {S : Set (Fin (Tag.rank .E6) → ℤ)} {x : Fin 6}
    (hS : ∀ γ ∈ S, ∃ a b : Fin 6, ∃ _ : a ≠ b, b ≠ x ∧ a5Root a b = γ) :
    rootSpan .E6 K S ≤
      ((fixBasisSL x).map (slToAdjointE6 K)).map (adjointGroup .E6 K).subtype := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨a, b, hab, hbx, rfl⟩ := hS γ hγ
  rw [rootSubgroup, closure_le]
  rintro _ ⟨c, rfl⟩
  exact ⟨_, ⟨_, transvection_mem_fixBasisSL hab c hbx, rfl⟩, coe_slToAdjointE6_transvection hab c⟩

theorem FieldNeighbourCover.exists_section_toNeighbour (h : FieldNeighbourCover σ e .high)
    (N : E6Neighbour) {H' : Subgroup (N.levi K)}
    (s : ↥(H'.map ((highLeviConjEquiv K N).symm : N.levi K →* E6Neighbour.high.levi K)) →*
      neighbourCore e .high)
    (hs : ∀ y, h.p (s y) = y) :
    ∃ s' : H' →* neighbourCore e N, ∀ y, (h.toNeighbour N).p (s' y) = y := by
  refine ⟨(neighbourCoreConjEquiv e N).toMonoidHom.comp
    (s.comp ((highLeviConjEquiv K N).symm.subgroupMap H').toMonoidHom), fun y => ?_⟩
  change highLeviConjEquiv K N (h.p ((neighbourCoreConjEquiv e N).symm
    (neighbourCoreConjEquiv e N (s ((highLeviConjEquiv K N).symm.subgroupMap H' y))))) = y
  rw [MulEquiv.symm_apply_apply, hs]
  exact MulEquiv.apply_symm_apply _ _

theorem FieldNeighbourCover.exists_section_toNeighbour_of_subset
    (h : FieldNeighbourCover σ e .high) (hK : 5 ≤ Nat.card K) {N : E6Neighbour}
    (hN : N = .six ∨ N = .three) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) :
    ∃ s : leviPiece K N J →* neighbourCore e N, ∀ y, (h.toNeighbour N).p (s y) = y := by
  set S : Set (Fin (Tag.rank .E6) → ℤ) := {γ | ∃ j ∈ J,
    γ = a5Root (nbLo N j) (nbHi N j) ∨ γ = a5Root (nbHi N j) (nbLo N j)} with hSdef
  have hSroot : ∀ γ ∈ S, IsRoot .E6 γ := by
    rintro γ ⟨j, -, rfl | rfl⟩
    exacts [isRoot_a5Root (nbLo_ne_nbHi N j), isRoot_a5Root (nbLo_ne_nbHi N j).symm]
  have himage : (fun α => N.weyl • α) '' S = amalgamRoots J := by
    ext γ
    constructor
    · rintro ⟨_, ⟨j, hj, rfl | rfl⟩, rfl⟩
      · exact ⟨j, hj, Or.inl (nb_data hN (hJ hj)).1⟩
      · refine ⟨j, hj, Or.inr ?_⟩
        change N.weyl • a5Root (nbHi N j) (nbLo N j) = _
        rw [a5Root_swap_E6, smul_neg, (nb_data hN (hJ hj)).1]
    · rintro ⟨j, hj, rfl | rfl⟩
      · exact ⟨_, ⟨j, hj, Or.inl rfl⟩, (nb_data hN (hJ hj)).1⟩
      · refine ⟨_, ⟨j, hj, Or.inr rfl⟩, ?_⟩
        change N.weyl • a5Root (nbHi N j) (nbLo N j) = _
        rw [a5Root_swap_E6, smul_neg, (nb_data hN (hJ hj)).1]
  have hSfix : ∀ γ ∈ S, ∃ a b : Fin 6, ∃ _ : a ≠ b, b ≠ nbFree N ∧ a5Root a b = γ := by
    rintro γ ⟨j, hj, rfl | rfl⟩
    · exact ⟨_, _, nbLo_ne_nbHi N j, (nb_data hN (hJ hj)).2.2, rfl⟩
    · exact ⟨_, _, (nbLo_ne_nbHi N j).symm, (nb_data hN (hJ hj)).2.1, rfl⟩
  have hmem : ∀ y ∈ (leviPiece K N J).map
      ((highLeviConjEquiv K N).symm : N.levi K →* E6Neighbour.high.levi K),
      ((y : E6Neighbour.high.levi K) : adjointGroup .E6 K) ∈
        (fixBasisSL (nbFree N)).map (slToAdjointE6 K) := by
    rintro _ ⟨y', hy', rfl⟩
    have hy'S : (((y' : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) ∈
        (rootSpan .E6 K S).map (MulAut.conj (N.rep K : ModGL .E6 K)).toMonoidHom := by
      rw [map_conj_rep_rootSpan N hSroot, himage]
      exact hy'
    obtain ⟨z, hz, hzy⟩ := hy'S
    have hcoe : ((((highLeviConjEquiv K N).symm y' : E6Neighbour.high.levi K) :
        adjointGroup .E6 K) : ModGL .E6 K) = z := by
      have h1 := coe_highLeviConjEquiv N ((highLeviConjEquiv K N).symm y')
      rw [MulEquiv.apply_symm_apply] at h1
      have h2 : (((y' : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
          (N.rep K : ModGL .E6 K) * z * (N.rep K : ModGL .E6 K)⁻¹ := hzy.symm
      have h3 := h1.symm.trans h2
      exact mul_left_cancel (mul_right_cancel h3)
    obtain ⟨w, hw, hwz⟩ := rootSpan_le_map_fixBasisSL hSfix hz
    rw [← hwz] at hcoe
    have hw' : ((highLeviConjEquiv K N).symm y' : adjointGroup .E6 K) = w :=
      Subtype.ext hcoe
    change (((highLeviConjEquiv K N).symm y' : E6Neighbour.high.levi K) : adjointGroup .E6 K) ∈ _
    rw [hw']
    exact hw
  obtain ⟨s, hs⟩ := h.exists_section_of_le_map hK hmem
  exact h.exists_section_toNeighbour N s hs

end Sections

end CFSG.SeitzReduction.E6Pilot
