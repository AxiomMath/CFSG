module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcCent

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem finiteIndex_toralRootGroup {tau : Tag} {K : Type} [Field K]
    (a : Fin tau.rank → Kˣ) :
    ((toralRootGroup tau K a).subgroupOf (toralCentralizer tau K a)).FiniteIndex := by
  obtain ⟨-, hN, -, hKN, phi, hsurj, -⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient tau K a
  haveI := hN
  haveI := hKN
  have : Finite (toralCentralizer tau K a ⧸
      (toralRootGroup tau K a).subgroupOf (toralCentralizer tau K a)) :=
    Finite.of_surjective phi hsurj
  exact Subgroup.finiteIndex_of_finite_quotient

theorem isPointClosed_toralRootGroup {tau : Tag} {K : Type} [Field K] [IsAlgClosed K]
    (a : Fin tau.rank → Kˣ) :
    IsPointClosed K (transportPoints (modGLPoint tau K)
      (toralRootGroup tau K a : Set (ModGL tau K))) := by
  have he : familyGroup (fun _ : PUnit => a) = toralRootGroup tau K a := by
    have hker : familyKernel (fun _ : PUnit => a) = rootCharKernel a := by
      ext alpha
      simp [familyKernel, rootCharKernel]
    simp only [familyGroup, toralRootGroup, hker]
  simpa only [he] using isPointClosed_familyGroup (fun _ : PUnit => a)

theorem closedIdentityComponent_toralCentralizer_eq {tau : Tag} {K : Type} [Field K]
    [IsAlgClosed K] (a : Fin tau.rank → Kˣ) :
    closedIdentityComponent (toralCentralizer tau K a) = toralRootGroup tau K a := by
  letI := finiteIndex_toralRootGroup a
  refine le_antisymm
    (closedIdentityComponent_le_of_isPointClosed_finiteIndex (isPointClosed_toralRootGroup a)) ?_
  have he : familyGroup (fun _ : PUnit => a) = toralRootGroup tau K a := by
    have hker : familyKernel (fun _ : PUnit => a) = rootCharKernel a := by
      ext alpha
      simp [familyKernel, rootCharKernel]
    simp only [familyGroup, toralRootGroup, hker]
  have hc : closedIdentityComponent (toralRootGroup tau K a) = toralRootGroup tau K a := by
    simpa only [he] using closedIdentityComponent_familyGroup (fun _ : PUnit => a)
  rw [← hc]
  exact closedIdentityComponent_mono (toralRootGroup_le a)

theorem range_le_rootSpan_of_perfect_of_le_connectedCentralizer
    {tau : Tag} {K : Type} [Field K] [IsAlgClosed K]
    {P : Type*} [Group P] [Group.IsPerfect P]
    (a : Fin tau.rank → Kˣ) (phi : P →* ModGL tau K)
    (hRange : phi.range ≤ closedIdentityComponent (toralCentralizer tau K a)) :
    phi.range ≤ rootSpan tau K (rootCharKernel a) := by
  have hTG : phi.range ≤ toralRootGroup tau K a := by
    simpa only [closedIdentityComponent_toralCentralizer_eq] using hRange
  have hP : commutator P = ⊤ := Group.IsPerfect.commutator_eq_top
  have hc : ⁅phi.range, phi.range⁆ = phi.range := by
    simpa only [commutator_def, Subgroup.map_commutator, Subgroup.map_top] using
      congrArg (fun S : Subgroup P => S.map phi) hP
  rw [← hc]
  exact (Subgroup.commutator_mono hTG hTG).trans
    (CFSG.LocalAnalysis.GLTheoremA.T173O.commutator_toralRootGroup_le_rootSpan a)


end CFSG.LieType.AlgebraicGroups
