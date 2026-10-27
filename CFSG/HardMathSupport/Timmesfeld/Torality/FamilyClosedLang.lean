module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] {ι : Type}

theorem isPointClosed_familyGroup (a : ι → Fin τ.rank → kˣ) :
    IsPointClosed k (transportPoints (modGLPoint τ k) (familyGroup a : Set (ModGL τ k))) := by
  have h := (isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (k := k)
    (familyChar a)).isPointClosed
  rw [subgroupPoints_map, kernelRoots_familyChar] at h
  exact h

theorem isPointIrreducible_familyGroup (a : ι → Fin τ.rank → kˣ) :
    IsPointIrreducible k (transportPoints (modGLPoint τ k) (familyGroup a : Set (ModGL τ k))) := by
  have h : IsPointIrreducible k (subgroupPoints
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots (familyChar a))).map
        (modGLPoint τ k).toMonoidHom)) :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.2
      (isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (familyChar a)).isPrime
  rw [subgroupPoints_map, kernelRoots_familyChar] at h
  exact h

theorem closedIdentityComponent_familyGroup (a : ι → Fin τ.rank → kˣ) :
    closedIdentityComponent (familyGroup a) = familyGroup (K := k) a :=
  closedIdentityComponent_eq_self (isPointIrreducible_familyGroup a)

theorem isPointClosed_familyGroup_inf_centralizer (a : ι → Fin τ.rank → kˣ)
    (T : Set (ModGL τ k)) :
    IsPointClosed k (transportPoints (modGLPoint τ k)
      ((familyGroup a ⊓ Subgroup.centralizer T : Subgroup (ModGL τ k)) : Set (ModGL τ k))) :=
  isPointClosed_inf (isPointClosed_familyGroup a) (isPointClosed_centralizer T)

theorem exists_inv_mul_frobTwistGL_familyGroup_inf_centralizer (p : ℕ) [Fact p.Prime]
    [CharP k p] (a : ι → Fin τ.rank → kˣ) (T : Set (ModGL τ k)) {e : ℕ} (he : 1 ≤ e)
    (Q : ModGL τ k)
    (hS : ∀ g ∈ familyGroup a ⊓ Subgroup.centralizer T,
      frobTwistGL τ k p e Q g ∈ familyGroup a ⊓ Subgroup.centralizer T) :
    ∀ c ∈ closedIdentityComponent (familyGroup a ⊓ Subgroup.centralizer T),
      ∃ ζ ∈ closedIdentityComponent (familyGroup a ⊓ Subgroup.centralizer T),
        ζ⁻¹ * frobTwistGL τ k p e Q ζ = c :=
  exists_inv_mul_frobTwistGL_closedIdentityComponent p
    (isPointClosed_familyGroup_inf_centralizer a T) he Q hS

end CFSG.HardMathSupport.Timmesfeld.Torality

end
