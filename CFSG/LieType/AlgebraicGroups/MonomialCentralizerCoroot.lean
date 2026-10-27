module
public import CFSG.LieType.AlgebraicGroups.DiagonalCocharacter
public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.LieType.AlgebraicGroups.ChevalleyDiagonalCocharacter
public import CFSG.LieType.Chevalley.MonomialCoroot

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open Matrix Module TauCeti WithConv
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open scoped TensorProduct CFSG.ConvolutionPoints
variable {k : Type} [Field k] [IsAlgClosed k] {τ : Tag}

theorem corootCurve_mem_closedIdentityComponent
    (Z : Subgroup (ModGL τ k)) (lam : Fin τ.rank → ℤ)
    (hZ : ∀ u : kˣ, rootDiagUnit τ (fun i => u ^ lam i) ∈ Z) (u : kˣ) :
    rootDiagUnit τ (fun i => u ^ lam i) ∈ closedIdentityComponent Z := by
  let wt : Label τ → ℤ := fun b => ∑ i, lam i * labelWt τ b i
  let P : Matrix (Label τ) (Label τ) (MonoidAlgebra k (Multiplicative ℤ)) :=
    Matrix.diagonal fun b => MonoidAlgebra.single (Multiplicative.ofAdd (wt b)) 1
  let c : (MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] k) → ModGL τ k := fun z =>
    rootDiagUnit τ (fun i => DiagonalizableGroup.pointsMulEquiv (toConv z)
      (Multiplicative.ofAdd 1) ^ lam i)
  have hc : ∀ z a b, endMatrix τ (c z : Module.End k (RootModule τ k)) a b = z (P a b) := by
    intro z a b
    have hpt := diagonalCocharacterBialgHom_rootDiagPoint (k := k) lam (toConv z)
    have h := congrArg (fun p => p.ofConv (glEntry k (Label τ) a b)) hpt
    rw [TauCeti.AlgHom.mapDomain_apply] at h
    simp only [AlgHom.comp_apply, diagonalCocharacterBialgHom_toAlgHom,
      diagonalCocharacterAlgHom_entry, modGLPoint_apply_glEntry] at h
    rw [endMatrix_apply]
    change _ = z (Matrix.diagonal (fun b => MonoidAlgebra.single
      (Multiplicative.ofAdd (wt b)) 1) a b)
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst b
      simpa only [ite_true] using h.symm
    · simpa only [hab, ite_false, map_zero] using h.symm
  have hcZ : ∀ z, c z ∈ Z := fun z => hZ _
  have hz : c (Bialgebra.counitAlgHom k (MonoidAlgebra k (Multiplicative ℤ))) = 1 := by
    change rootDiagUnit τ (fun i => DiagonalizableGroup.pointsMulEquiv
      (1 : WithConv (MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] k))
      (Multiplicative.ofAdd 1) ^ lam i) = 1
    simp only [map_one, MonoidHom.one_apply, _root_.one_zpow]
    exact rootDiagUnit_one
  let p : WithConv (MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] k) :=
    (DiagonalizableGroup.pointsMulEquiv (R := k) (A := k)).symm (zpowersHom kˣ u)
  have hpu : DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) = u := by
    change (DiagonalizableGroup.pointsMulEquiv (R := k) (A := k))
      ((DiagonalizableGroup.pointsMulEquiv (R := k) (A := k)).symm (zpowersHom kˣ u))
      (Multiplicative.ofAdd 1) = u
    rw [MulEquiv.apply_symm_apply]
    simp
  have hm := mem_closedIdentityComponent_of_matrix P hc hcZ hz p.ofConv
  simpa only [c, hpu] using hm

theorem corootCurve_mem_connectedCentralizer_of_all_weyl_fixed
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (E : Subgroup (ModGL τ k)) (hEM : E ≤ monomialSubgroup τ k)
    (hfix : ∀ e (he : e ∈ E), weylQuotientHom τ k ⟨e, hEM he⟩ • β = β)
    (u : kˣ) :
    rootDiagUnit τ (fun j => u ^ corootPair β (Pi.single j 1)) ∈
      closedIdentityComponent (adjointGroup τ k ⊓ Subgroup.centralizer (E : Set (ModGL τ k))) := by
  apply corootCurve_mem_closedIdentityComponent
  intro v
  refine ⟨monomialSubgroup_le_adjointGroup' (torusGroup_le_monomialSubgroup (rootDiagUnit_mem_torusGroup _)), ?_⟩
  change _ ∈ Subgroup.centralizer (E : Set (ModGL τ k))
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact (commute_corootCurve_of_weyl_fixed hβ v ⟨e, hEM he⟩ (hfix e he)).eq

end CFSG.LieType.AlgebraicGroups
