module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOCent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOBlock

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.U (blockGL coe_blockGL)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL
  isSubnormal_subgroupOf_of_normalizes)
open scoped MatrixGroups

variable {K : Type} [Field K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

omit [Field K] in
theorem blockGL_injective {K : Type} [Field K] (I : Finset (Fin d)) :
    Function.Injective (blockGL K I) := fun _ _ h =>
  Units.ext (blockOn_injective I (congrArg Units.val h))

abbrev omegaI (I : Finset (Fin d)) : Subgroup (GL (Fin I.card) K) :=
  omegaR (diagGL (wRes_ne_zero hw I))

abbrev projBlock (I : Finset (Fin d)) (L : Subgroup (GL (Fin I.card) K)) :
    Subgroup (StatedProj (matrixDerived (oQ (diagGL hw)))) :=
  ((L.map (blockGL K I)).subgroupOf (matrixDerived (oQ (diagGL hw)))).map (projH _)

theorem blockP_eq_projBlock (I : Finset (Fin d)) :
    blockP K hw I = projBlock hw I (omegaI hw I) := by
  rw [blockP, projBlock, oBlock_eq_map]

theorem map_blockGL_le_oBlock (I : Finset (Fin d)) {L : Subgroup (GL (Fin I.card) K)}
    (hL : L ≤ omegaI hw I) : L.map (blockGL K I) ≤ oBlock K hw I := by
  rw [oBlock_eq_map]
  exact map_mono hL

theorem projBlock_le_blockP (I : Finset (Fin d)) {L : Subgroup (GL (Fin I.card) K)}
    (hL : L ≤ omegaI hw I) : projBlock hw I L ≤ blockP K hw I :=
  map_mono fun _ hg => map_blockGL_le_oBlock hw I hL hg

theorem projBlock_sup (h2 : (2 : K) ≠ 0) (I : Finset (Fin d)) {L M : Subgroup (GL (Fin I.card) K)}
    (hL : L ≤ omegaI hw I) (hM : M ≤ omegaI hw I) :
    projBlock hw I (L ⊔ M) = projBlock hw I L ⊔ projBlock hw I M := by
  rw [projBlock, projBlock, projBlock, Subgroup.map_sup,
    subgroupOf_sup ((map_blockGL_le_oBlock hw I hL).trans (oBlock_le_matrixDerived hw h2 I))
      ((map_blockGL_le_oBlock hw I hM).trans (oBlock_le_matrixDerived hw h2 I)),
    Subgroup.map_sup]

theorem nonempty_projBlock_equiv (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty)
    {L : Subgroup (GL (Fin I.card) K)} (hL : L ≤ omegaI hw I) :
    Nonempty (projBlock hw I L ≃* L) := by
  set M := (L.map (blockGL K I)).subgroupOf (matrixDerived (oQ (diagGL hw))) with hM
  have hLM : L.map (blockGL K I) ≤ matrixDerived (oQ (diagGL hw)) :=
    (map_blockGL_le_oBlock hw I hL).trans (oBlock_le_matrixDerived hw h2 I)
  have hinj : Function.Injective ((projH (matrixDerived (oQ (diagGL hw)))).comp M.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : (g : matrixDerived (oQ (diagGL hw))) ∈
        (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) :=
      mem_subgroupOf.2 (map_blockGL_le_oBlock hw I hL (mem_subgroupOf.1 g.2))
    exact Subtype.ext (projH_injOn_oBlock hw hIc hg' hg)
  have hrange : ((projH (matrixDerived (oQ (diagGL hw)))).comp M.subtype).range =
      projBlock hw I L := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm).trans
    (subgroupOfEquivOfLe hLM)).trans
    (L.equivMapOfInjective _ (blockGL_injective I)).symm⟩

theorem isSubnormal_projBlock (hK : ringChar K ≠ 2) (J I : Finset (Fin d)) (hI : I = J ∨ I = Jᶜ)
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) {L : Subgroup (GL (Fin I.card) K)}
    (hL : L ≤ omegaI hw I) (hn : (L.subgroupOf (omegaI hw I)).Normal) :
    projBlock hw I L ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _) ∧
      ((projBlock hw I L).subgroupOf
        (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal := by
  have hle := projBlock_le_blockP hw I hL
  refine ⟨hle.trans (blockP_le_centralizer hw J I hI hJ),
    isSubnormal_subgroupOf_of_normalizes hle ?_ (isSubnormal_blockP hw hK J I hI hJ)⟩
  rw [blockP_eq_projBlock]
  rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
  obtain ⟨X₀, hX₀, hX₀e⟩ := mem_subgroupOf.1 hX
  obtain ⟨Y₀, hY₀, hY₀e⟩ := mem_subgroupOf.1 hY
  have hmem : X₀ * Y₀ * X₀⁻¹ ∈ L := by
    have h1 := hn.conj_mem ⟨Y₀, hL hY₀⟩ (mem_subgroupOf.2 hY₀) ⟨X₀, hX₀⟩
    rw [mem_subgroupOf] at h1
    simpa using h1
  refine ⟨X * Y * X⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  change ((X * Y * X⁻¹ : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) ∈ L.map (blockGL K I)
  refine ⟨X₀ * Y₀ * X₀⁻¹, hmem, ?_⟩
  rw [map_mul, map_mul, map_inv, hX₀e, hY₀e]
  rfl

@[expose] def SplitP (I : Finset (Fin d)) : Prop :=
  ∃ L₁ L₂ : Subgroup (GL (Fin I.card) K),
    blockP K hw I = projBlock hw I L₁ ⊔ projBlock hw I L₂ ∧ L₁ ≤ omegaI hw I ∧
    L₂ ≤ omegaI hw I ∧ (L₁.subgroupOf (omegaI hw I)).Normal ∧
    (L₂.subgroupOf (omegaI hw I)).Normal ∧ IsQuasisimple (projBlock hw I L₁) ∧
    IsQuasisimple (projBlock hw I L₂) ∧ Nonempty (projBlock hw I L₁ ≃* SL(2, K)) ∧
    Nonempty (projBlock hw I L₂ ≃* SL(2, K))

theorem blockP_cases [Finite K] (hK : ringChar K ≠ 2) (I : Finset (Fin d)) (hIc : Iᶜ.Nonempty) :
    Group.IsSolvable (blockP K hw I) ∨ IsQuasisimple (blockP K hw I) ∨
      (I.card = 4 ∧ Nat.card K ≠ 3 ∧ SplitP hw I) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨e⟩ := nonempty_projBlock_equiv hw h2 hIc (le_refl (omegaI hw I))
  rw [← blockP_eq_projBlock] at e
  rcases Nat.lt_or_ge I.card 3 with h3 | h3
  · left
    have := isSolvable_omegaR_of_le_two (by omega : I.card ≤ 2) (wRes_ne_zero hw I)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  rcases orth_block_cases hK h3 (diagGL (wRes_ne_zero hw I))
      (by rw [coe_diagGL]; exact diagonal_transpose _) with h | h | ⟨h4, hK3, L₁, L₂, hsup,
        hL₁, hL₂, hn₁, hn₂, hq₁, hq₂, ⟨e₁⟩, ⟨e₂⟩⟩
  · exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · exact Or.inr (Or.inl (LocalCores.isQuasisimple_of_mulEquiv e.symm h))
  · obtain ⟨f₁⟩ := nonempty_projBlock_equiv hw h2 hIc hL₁
    obtain ⟨f₂⟩ := nonempty_projBlock_equiv hw h2 hIc hL₂
    refine Or.inr (Or.inr ⟨h4, hK3, L₁, L₂, ?_, hL₁, hL₂, hn₁, hn₂,
      LocalCores.isQuasisimple_of_mulEquiv f₁.symm hq₁,
      LocalCores.isQuasisimple_of_mulEquiv f₂.symm hq₂, ⟨f₁.trans e₁⟩, ⟨f₂.trans e₂⟩⟩)
    rw [blockP_eq_projBlock, ← projBlock_sup hw h2 I hL₁ hL₂]
    exact congrArg _ hsup

end CFSG.ComponentClassification.Burgoyne.C
