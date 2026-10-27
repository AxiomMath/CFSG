module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyA3
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.LieEmbed

local instance e6PilotCoverFamilyHighNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Stab

variable {K : Type*} [Field K]

@[expose] def fixBasisSL (x : Fin 6) : Subgroup (SpecialLinearGroup (Fin 6) K) where
  carrier := {A | A.1 *ᵥ Pi.single x 1 = Pi.single x 1}
  one_mem' := by
    show (1 : Matrix (Fin 6) (Fin 6) K) *ᵥ Pi.single x 1 = _
    rw [Matrix.one_mulVec]
  mul_mem' := by
    intro A B hA hB
    have hA' : A.1 *ᵥ Pi.single x 1 = Pi.single x 1 := hA
    have hB' : B.1 *ᵥ Pi.single x 1 = Pi.single x 1 := hB
    show (A.1 * B.1) *ᵥ Pi.single x 1 = _
    rw [← Matrix.mulVec_mulVec, hB', hA']
  inv_mem' := by
    intro A hA
    have hA' : A.1 *ᵥ Pi.single x 1 = Pi.single x 1 := hA
    show (A⁻¹).1 *ᵥ Pi.single x 1 = _
    have h1 : (A⁻¹).1 * A.1 = 1 := congrArg Subtype.val (inv_mul_cancel A)
    calc (A⁻¹).1 *ᵥ Pi.single x 1 = (A⁻¹).1 *ᵥ (A.1 *ᵥ Pi.single x 1) := by rw [hA']
      _ = ((A⁻¹).1 * A.1) *ᵥ Pi.single x 1 := by rw [Matrix.mulVec_mulVec]
      _ = Pi.single x 1 := by rw [h1, Matrix.one_mulVec]

theorem transvection_mem_fixBasisSL {i j : Fin 6} (hij : i ≠ j) (c : K) {x : Fin 6}
    (hjx : j ≠ x) : SpecialLinearGroup.transvection hij c ∈ fixBasisSL x := by
  show ((1 + single i j c : Matrix (Fin 6) (Fin 6) K)) *ᵥ Pi.single x 1 = Pi.single x 1
  rw [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq, Pi.single_eq_of_ne hjx, mul_zero,
    zero_smul, add_zero]

theorem eq_one_of_mem_center_of_mem_fixBasisSL {A : SpecialLinearGroup (Fin 6) K}
    (hA : A ∈ center (SpecialLinearGroup (Fin 6) K)) {x : Fin 6} (hx : A ∈ fixBasisSL x) :
    A = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hx' : A.1 *ᵥ Pi.single x 1 = Pi.single x 1 := hx
  have hA1 : A.1 = Matrix.scalar (Fin 6) r := hr.symm
  rw [hA1] at hx'
  have h1 := congrFun hx' x
  have hr1 : r = 1 := by
    simpa [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply] using h1
  apply Subtype.ext
  rw [hA1, hr1, map_one]
  rfl

end Stab

@[expose] def a5Lo : Fin 6 → Fin 6 := ![0, 0, 1, 2, 3, 4]

@[expose] def a5Hi : Fin 6 → Fin 6 := ![1, 1, 2, 3, 4, 5]

theorem a5Lo_ne_a5Hi (l : Fin 6) : a5Lo l ≠ a5Hi l := by
  revert l
  decide

theorem a5Root_lo_hi_check : ∀ l : Fin (Tag.rank .E6), l ≠ 1 →
    a5Root (a5Lo l) (a5Hi l) = Pi.single l 1 ∧ a5Root (a5Hi l) (a5Lo l) = -Pi.single l 1 := by
  decide +kernel

theorem exists_coord_not_mem_check : ∀ J : Finset (Fin 6),
    J ⊆ {0, 2, 3, 4, 5} → J.card ≤ 2 → ∃ x : Fin 6, ∀ l ∈ J, a5Lo l ≠ x ∧ a5Hi l ≠ x := by
  decide

section High


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem injective_slToAdjointE6_restrict_fixBasisSL (x : Fin 6) :
    Function.Injective ((slToAdjointE6 K).comp (fixBasisSL x).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have h1 : (A : SpecialLinearGroup (Fin 6) K) ∈ (slToAdjointE6 K).ker := hA
  rw [ker_slToAdjointE6] at h1
  exact (mem_bot).2 (Subtype.ext (eq_one_of_mem_center_of_mem_fixBasisSL h1 A.2))

theorem levi_le_map_fixBasisSL {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ E6Neighbour.high.nodes)
    {x : Fin 6} (hx : ∀ l ∈ J, a5Lo l ≠ x ∧ a5Hi l ≠ x) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤
      (fixBasisSL x).map (slToAdjointE6 K) := by
  refine iSup₂_le fun l hl => sup_le ?_ ?_ <;> intro g hg
  · have hl1 : l ≠ 1 := by
      rintro rfl
      have := hJ hl
      rw [nodes_high_eq] at this
      exact one_not_mem_nodes_high this
    obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff
      (isRoot_single .E6 l) g).1 hg
    refine ⟨_, transvection_mem_fixBasisSL (a5Lo_ne_a5Hi l) c (hx l hl).2, Subtype.ext ?_⟩
    rw [coe_slToAdjointE6_transvection, (a5Root_lo_hi_check l hl1).1,
      coe_xPar_eq_pinnedX (isRoot_single .E6 l)]
  · have hl1 : l ≠ 1 := by
      rintro rfl
      have := hJ hl
      rw [nodes_high_eq] at this
      exact one_not_mem_nodes_high this
    obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff
      (isRoot_neg_single .E6 l) g).1 hg
    refine ⟨_, transvection_mem_fixBasisSL (a5Lo_ne_a5Hi l).symm c (hx l hl).1, Subtype.ext ?_⟩
    rw [coe_slToAdjointE6_transvection, (a5Root_lo_hi_check l hl1).2,
      coe_xPar_eq_pinnedX (isRoot_neg_single .E6 l)]

theorem FieldNeighbourCover.exists_section_of_le_map (h : FieldNeighbourCover σ e .high)
    (hK : 5 ≤ Nat.card K) {x : Fin 6} {H : Subgroup (E6Neighbour.high.levi K)}
    (hH : ∀ y ∈ H, ((y : E6Neighbour.high.levi K) : adjointGroup .E6 K) ∈
      (fixBasisSL x).map (slToAdjointE6 K)) :
    ∃ s : H →* neighbourCore e .high, ∀ y, h.p (s y) = y := by
  obtain ⟨Ψ, hΨ⟩ := h.exists_sl6Lift hK
  set φB := (slToAdjointE6 K).comp (fixBasisSL x).subtype with hφB
  have hinj := injective_slToAdjointE6_restrict_fixBasisSL (K := K) x
  have hrange : φB.range = (fixBasisSL x).map (slToAdjointE6 K) := by
    rw [hφB, MonoidHom.range_comp, range_subtype]
  set ι : H →* φB.range :=
    (((E6Neighbour.high.levi K).subtype.comp H.subtype).codRestrict φB.range fun y => by
      rw [hrange]
      exact hH y y.2) with hι
  refine ⟨Ψ.comp ((fixBasisSL x).subtype.comp
    ((MonoidHom.ofInjective hinj).symm.toMonoidHom.comp ι)), fun y => ?_⟩
  apply Subtype.ext
  rw [MonoidHom.comp_apply, hΨ]
  have h1 := (MonoidHom.ofInjective hinj).apply_symm_apply (ι y)
  have h2 := congrArg Subtype.val h1
  rw [MonoidHom.ofInjective_apply] at h2
  exact h2

theorem FieldNeighbourCover.exists_section_high (h : FieldNeighbourCover σ e .high)
    (hK : 5 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ E6Neighbour.high.nodes)
    (hJ2 : J.card ≤ 2) :
    ∃ s : leviPiece K .high J →* neighbourCore e .high, ∀ y, h.p (s y) = y := by
  obtain ⟨x, hx⟩ := exists_coord_not_mem_check (J : Finset (Fin 6)) (fun l hl => by
    have := hJ hl
    rw [nodes_high_eq] at this
    exact this) hJ2
  refine h.exists_section_of_le_map hK fun y hy => levi_le_map_fixBasisSL hJ hx ?_
  have hy' : ((y : adjointGroup .E6 K) : ModGL .E6 K) ∈ rootSpan .E6 K (amalgamRoots J) := hy
  rw [levi_adjDatumE6_eq, mem_subgroupOf]
  exact hy'

end High

end CFSG.SeitzReduction.E6Pilot
