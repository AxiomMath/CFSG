module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIndexLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIdxRoots
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIdxWeyl

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Index


theorem a2ci_relIndex_dvd_three_of
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)
    {ta : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom ta))
    (hri : rationalRoots S.ρ (rootCharHom ta) i = kernelRoots (rootCharHom ta))
    (hI1 : S.Γ ⊓ rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) ≤
      rationalComponent S.ρ S.Γ (rootCharHom ta) i)
    (hI2 : torusGroup Tag.E6 L ≤ rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)))
    (hI3 : Nat.card (↥(rootCharStabilizerSubgroup ta) ⧸
      (kernelReflectionGroup ta).subgroupOf (rootCharStabilizerSubgroup ta)) ∣ 3) :
    (rationalComponent S.ρ S.Γ (rootCharHom ta) i).relIndex
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 ta}) ∣ 3 := by
  have hRA : rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤
      rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) := by
    intro x hx
    have hx' : x ∈ rationalSpan S.ρ S.Γ (rootCharHom ta) i :=
      Subgroup.commutator_le_self _ hx
    have hx'' := (Subgroup.mem_inf.1 hx').1
    rw [hri] at hx''
    exact hx''
  have hRC : rationalComponent S.ρ S.Γ (rootCharHom ta) i ⊓
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 ta}) =
      rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) ⊓
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 ta}) := by
    refine le_antisymm (inf_le_inf_right _ hRA) (le_inf ?_ inf_le_right)
    intro x hx
    exact hI1 (Subgroup.mem_inf.2
      ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).2).1, (Subgroup.mem_inf.1 hx).1⟩)
  have hM : toralRootGroup Tag.E6 L ta = rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) := by
    change torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) = _
    exact sup_eq_right.2 hI2
  have hCX : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 ta} ≤
      toralCentralizer Tag.E6 L ta := by
    intro x hx
    change x ∈ adjointGroup Tag.E6 L ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 ta}
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.commutator_le_self S.D.model
      (Subgroup.mem_inf.1 hx).1)).1, (Subgroup.mem_inf.1 hx).2⟩
  obtain ⟨-, -, -, -, φ, hφ, -⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient Tag.E6 L ta
  have h1 : (toralRootGroup Tag.E6 L ta).relIndex
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 ta}) ∣
      ((toralRootGroup Tag.E6 L ta).subgroupOf (toralCentralizer Tag.E6 L ta)).index := by
    rw [← Subgroup.relIndex_subgroupOf hCX]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  rw [Subgroup.index_eq_card] at h1
  rw [← Subgroup.inf_relIndex_right, hRC, Subgroup.inf_relIndex_right, ← hM]
  exact (h1.trans (Subgroup.card_dvd_of_surjective hφ)).trans hI3

theorem relIndex_rationalComponent_centralizer_dvd_three
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)
    {ta : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus)
    (hap : ∀ j, ta j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 ta ≠ 1)
    (h3 : ((3 : ℕ) : L) ≠ 0)
    (h18 : (kernelRoots (rootCharHom ta)).ncard = 18)
    (hrat : ∀ i : KernelComponent (rootCharHom ta),
      componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 3 ∧
        rationalRoots S.ρ (rootCharHom ta) i = kernelRoots (rootCharHom ta))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (h3q : 3 ∣ S.D.q + 1) (hq2 : S.D.q ≠ 2) (hout : rootDiagUnit Tag.E6 ta ∉ S.Γ)
    (i : KernelComponent (rootCharHom ta)) :
    (rationalComponent S.ρ S.Γ (rootCharHom ta) i).relIndex
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 ta}) ∣ 3 :=
  a2ci_relIndex_dvd_three_of S i (hrat i).2
    (a2cube_inf_rootSpan_le_rationalComponent S hT hap h1 h3 h18 hrat h3q hout i)
    (a2cube_torusGroup_le_rootSpan h3 hap h18) (a2cube_card_weylQuotient_dvd_three h3 hap h18)

end Index

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
