module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotRest
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Torus


theorem isSolvable_torusGroup (τ : Tag) (L : Type) [Field L] : Group.IsSolvable ↥(torusGroup τ L) := by
  have hle : torusGroup τ L ≤ (rootDiagUnitHom τ L).range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact ⟨fun j => u ^ τ.cartan i j, (torusElt_eq_rootDiagUnit i u).symm⟩
  haveI : Group.IsSolvable ↥((rootDiagUnitHom τ L).range) :=
    Group.isSolvable_of_surjective (rootDiagUnitHom τ L).rangeRestrict_surjective
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end Torus

section Monomial


theorem isSolvable_monomialSubgroup (τ : Tag) (L : Type) [Field L]
    (hW : Group.IsSolvable (WeylGroup τ)) : Group.IsSolvable ↥(monomialSubgroup τ L) := by
  obtain ⟨-, ⟨ρ, -, -, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient τ L
  haveI := isSolvable_torusGroup τ L
  exact Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (le_sup_left : torusGroup τ L ≤ monomialSubgroup τ L)) ρ
    (fun g hg => by
      rw [hker, Subgroup.mem_subgroupOf] at hg
      exact ⟨⟨g.1, hg⟩, Subtype.ext rfl⟩)

end Monomial

section Regular


theorem baseChangeGL_mem_adjointGroup' {τ : Tag} {K L : Type} [Field K] [Field L] (f : K →+* L)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) : baseChangeGL f g ∈ adjointGroup τ L := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, c, h | h⟩ := hy
    · rw [show y = xUnit τ K i c from Units.ext h, baseChangeGL_xUnit]
      exact xUnit_mem_adjointGroup _ _
    · rw [show y = yUnit τ K i c from Units.ext h, baseChangeGL_yUnit]
      exact yUnit_mem_adjointGroup _ _
  | one => simpa using one_mem _
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

theorem isSolvable_centralizer_of_regular {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup .F4 K)} (D : LangPlaneData .F4 K E₀)
    (hreg : ∀ α, IsRoot .F4 α → ¬ D.Kills α) :
    Group.IsSolvable ↥(Subgroup.centralizer (E₀ : Set (adjointGroup .F4 K))) := by
  choose a ha using fun x : E₀ =>
    exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D x.2)
  have hker : familyKernel a = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun α hα => hreg α hα.1 fun x hx => ?_
    exact ⟨a ⟨x, hx⟩, ha ⟨x, hx⟩, hα.2 ⟨x, hx⟩⟩
  have hgroup : familyGroup (K := AlgebraicClosure K) a = torusGroup .F4 (AlgebraicClosure K) := by
    rw [familyGroup, hker, rootSpan]
    simp
  have hmono : ∀ g : Subgroup.centralizer (E₀ : Set (adjointGroup .F4 K)),
      diagMap D g.1 ∈ monomialSubgroup .F4 (AlgebraicClosure K) := by
    intro g
    have hgc : diagMap D g.1 ∈ familyCentralizer .F4 (AlgebraicClosure K) a := by
      refine mem_familyCentralizer.2 ⟨?_, fun x => ?_⟩
      · rw [diagMap_apply]
        refine mul_mem (mul_mem ((adjointGroup _ _).inv_mem D.hg0C)
          (baseChangeGL_mem_adjointGroup' _ (D.c * g.1 * D.c⁻¹).2)) D.hg0C
      · rw [ha x, mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_centralizer_iff.1 g.2 x x.2
    obtain ⟨w, -, m, hm, hmg⟩ := familyCentralizer_le_mul .F4 (AlgebraicClosure K) a hgc
    rw [hmg]
    rw [hgroup] at hm
    exact mul_mem (Subgroup.mem_sup_left hm)
      (canonicalRep_mem_monomialSubgroup (AlgebraicClosure K) w)
  let ψ : Subgroup.centralizer (E₀ : Set (adjointGroup .F4 K)) →*
      monomialSubgroup .F4 (AlgebraicClosure K) :=
    MonoidHom.codRestrict ((diagMap D).comp (Subgroup.subtype _)) _ hmono
  have hψ : Function.Injective ψ := fun g g' h =>
    Subtype.ext (diagMap_injective D (congrArg Subtype.val h))
  haveI := isSolvable_monomialSubgroup .F4 (AlgebraicClosure K)
    CFSG.StandardType.LayerExc.isSolvable_weylGroup_F4
  exact Group.isSolvable_of_isSolvable_injective hψ

theorem f4RegularSolvable (ε : ℕ) : F4RegularSolvable ε :=
  fun _ _ _ _ _ _ _ D hreg => isSolvable_centralizer_of_regular D hreg

end Regular

end CFSG.LieType.SeitzGeneration.ExcHighThree
