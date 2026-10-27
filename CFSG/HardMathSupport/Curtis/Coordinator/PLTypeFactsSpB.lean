module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports

theorem statedScalars_subgroupOf_statedSp_zmod_two (r : ℕ) :
    (StatedScalars (Fin r ⊕ Fin r) (ZMod 2)).subgroupOf (StatedSp r (ZMod 2)) = ⊥ := by
  have hall : ∀ v : (ZMod 2)ˣ, v = 1 := by decide
  have : StatedScalars (Fin r ⊕ Fin r) (ZMod 2) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨c, rfl⟩
    rw [hall c, map_one]
    exact Subgroup.one_mem _
  rw [this, Subgroup.bot_subgroupOf]

noncomputable def statedSpEquivStatedProjZMod (r : ℕ) :
    ↥(StatedSp r (ZMod 2)) ≃* StatedProj (StatedSp r (ZMod 2)) :=
  (QuotientGroup.quotientBot (G := ↥(StatedSp r (ZMod 2)))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSp_zmod_two r).symm)

theorem spTypeB_holds : SpTypeB := by
  intro r hr
  let q : PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hq : q.card = 2 := by simp [PrimePower.card_def, q]
  have hv : (LieTypeIndex.B r q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  let d : ValidLieTypeIndex := ⟨.B r q, hv⟩
  have _ : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  have hK : Nat.card (ZMod 2) = Nat.card ↥d.fixedField := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, d, q]
  let φ : ZMod 2 ≃+* ↥d.fixedField := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard hK
  refine ⟨d, ⟨q, hq, rfl⟩, ⟨?_⟩⟩
  exact ((statedSpEquivStatedProjZMod r).trans
    (statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ r)
      (glCongr_statedScalars φ))).trans
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv rfl hr).symm

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
