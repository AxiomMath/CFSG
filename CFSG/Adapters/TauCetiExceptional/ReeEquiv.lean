module

public import CFSG.Adapters.TauCetiExceptional.ReeInj

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.TauCetiBridge.BigCell TauCeti
open CFSG.LieType.Chevalley

variable {L : Type} [Field L] [Algebra (ZMod 3) L]

theorem nodeMap_surjective : Function.Surjective nodeMap := by
  intro i
  fin_cases i
  exacts [⟨1, rfl⟩, ⟨0, rfl⟩]

theorem adjointGroup_le_range
    : adjointGroup .G2 L ≤ (adPoints L).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hx | hy⟩
  · obtain ⟨j, rfl⟩ := nodeMap_surjective i
    exact ⟨_, (adPoints_rootSubgroupPoints_inl j c).trans (Units.ext hx.symm)⟩
  · obtain ⟨j, rfl⟩ := nodeMap_surjective i
    exact ⟨_, (adPoints_rootSubgroupPoints_inr j c).trans (Units.ext hy.symm)⟩

variable (L) in
@[expose] def ZerosInAdjoint : Prop :=
  ∀ H : Subgroup (ModGL .G2 L), adjointGroup .G2 L ≤ H →
    (∀ h ∈ H, ∀ P, VanishesOnRat .G2 P →
      evalMat (natMat .G2 L (h : Module.End L (RootModule .G2 L))) P = 0) →
    H ≤ adjointGroup .G2 L

theorem range_adPoints
    (hZ : ZerosInAdjoint L) : (adPoints L).range = adjointGroup .G2 L := by
  refine le_antisymm (hZ _ adjointGroup_le_range ?_) adjointGroup_le_range
  rintro _ ⟨g, rfl⟩ P hP
  rw [coe_adPoints]
  exact evalMat_natMat_adConj_of_mem_points g.2 P hP

@[expose] def adEquiv
    (hZ : ZerosInAdjoint L) :
    G2ShortRoot.PrimeField.points L ≃* adjointGroup .G2 L :=
  (MonoidHom.ofInjective (f := adPoints L) adPoints_injective).trans
    (MulEquiv.subgroupCongr (range_adPoints hZ))

theorem coe_adEquiv
    (hZ : ZerosInAdjoint L) (g : G2ShortRoot.PrimeField.points L) :
    ((adEquiv hZ g : adjointGroup .G2 L) : ModGL .G2 L) = adPoints L g :=
  rfl

theorem adEquiv_rootSubgroupPoints_inl
    (hZ : ZerosInAdjoint L) (i : Fin 2) (t : L) :
    adEquiv hZ (G2ShortRoot.PrimeField.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd t)) =
      xElement (nodeMap i) t :=
  Subtype.ext (adPoints_rootSubgroupPoints_inl i t)

theorem adEquiv_rootSubgroupPoints_inr
    (hZ : ZerosInAdjoint L) (i : Fin 2) (t : L) :
    adEquiv hZ (G2ShortRoot.PrimeField.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd t)) =
      yElement (nodeMap i) t :=
  Subtype.ext (adPoints_rootSubgroupPoints_inr i t)

end CFSG.TauCetiBridge.Ree
