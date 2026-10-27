module

public import CFSG.LieType.AlgebraicGroups.RealizedTangentCurves
public import CFSG.LieType.AlgebraicGroups.CentralizerInvolutionTangent
public import CFSG.LieType.AlgebraicGroups.AdFixedTangentKer

import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.LieType.AlgebraicGroups.RealizedTangentBound
import CFSG.LieType.AlgebraicGroups.InnerInvolutionTorus
import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
import CFSG.LieType.Chevalley.PinnedTangentIndependence
import CFSG.LieType.Chevalley.E7InvolutionFixedDim
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped CFSG.ConvolutionPoints

private theorem adTangent_proof_irrel {k : Type} [Field k] [IsAlgClosed k]
    {A : Type} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]
    (M : Subgroup (WithConv (A →ₐ[k] k))) {g : WithConv (A →ₐ[k] k)}
    (h h' : g ∈ M) : adTangent M h = adTangent M h' :=
  congrArg (fun hp => adTangent M hp) (Subsingleton.elim h h')

private theorem adTangent_congr {k : Type} [Field k] [IsAlgClosed k]
    {A : Type} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]
    (M : Subgroup (WithConv (A →ₐ[k] k))) {g g' : WithConv (A →ₐ[k] k)}
    (h : g = g') (hg : g ∈ M) (hg' : g' ∈ M) : adTangent M hg = adTangent M hg' := by
  subst h
  exact adTangent_proof_irrel M hg hg'

variable {L : Type} [Field L] [IsAlgClosed L]

section Basis

theorem linearIndependent_rootTangent_torusTangent_E7 (h2 : (2 : L) ≠ 0) :
    LinearIndependent L
      (Sum.elim (fun α : {α // IsRoot Tag.E7 α} => rootTangent Tag.E7 L α.1)
        (torusTangent Tag.E7 L)) := by
  classical
  let Φ : Module.End L (RootModule Tag.E7 L) ≃ₗ[L]
      Matrix (Label Tag.E7) (Label Tag.E7) L :=
    (LinearMap.toMatrixAlgEquiv (Finsupp.basisSingleOne (R := L) (ι := Label Tag.E7)))
      |>.toLinearEquiv
  have hli := (linearIndependent_pinnedE_tangentH_E7 (F := L) h2).map' Φ.toLinearMap
    (LinearEquiv.ker Φ)
  refine LinearIndependent.of_comp
    (tangentEntries (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) ?_
  convert hli using 1
  funext s
  ext a c
  rcases s with α | i
  · change tangentEntries (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))
        (rootTangent Tag.E7 L α.1) a c =
      endMatrix Tag.E7 (pinnedE Tag.E7 L α.1) a c
    rw [tangentEntries_apply, rootTangent_mk, endMatrix_apply]
  · change tangentEntries (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))
        (torusTangent Tag.E7 L i) a c =
      endMatrix Tag.E7 (tangentH Tag.E7 L i) a c
    rw [tangentEntries_apply, torusTangent_mk, endMatrix_apply]

theorem finrank_tangentSpace_realizedCoord_E7 (h2 : (2 : L) ≠ 0) :
    Module.finrank L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) = 133 := by
  classical
  have hfd : FiniteDimensional L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    finiteDimensional_tangentSpace (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))
  let _ := hfd
  have hcard : Fintype.card ({α // IsRoot Tag.E7 α} ⊕ Fin Tag.E7.rank) = 133 := by
    rw [Fintype.card_sum, Fintype.card_fin, card_isRoot]
    rfl
  have hge := (linearIndependent_rootTangent_torusTangent_E7 h2).fintype_card_le_finrank
  rw [hcard] at hge
  have hle := finrank_tangentSpace_realizedCoord_E7_le
    (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))
  omega

@[expose] def rootModuleTangentEquiv (h2 : (2 : L) ≠ 0) :
    RootModule Tag.E7 L ≃ₗ[L] TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L)) := by
  classical
  letI : Nonempty (Label Tag.E7) := ⟨Sum.inl ⟨0, by decide⟩⟩
  let b : Module.Basis (Label Tag.E7) L
      (TangentSpace L (realizedCoord Tag.E7 L)
        (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    basisOfLinearIndependentOfCardEqFinrank
      (b := fun l : Label Tag.E7 =>
        Sum.elim (fun i : Fin Tag.E7.rank => torusTangent Tag.E7 L i)
          (fun α : {α // IsRoot Tag.E7 α} => rootTangent Tag.E7 L α.1) l)
      (by
        have h := (linearIndependent_rootTangent_torusTangent_E7 (L := L) h2).comp
          (Equiv.sumComm (Fin Tag.E7.rank) {α // IsRoot Tag.E7 α})
          (Equiv.sumComm _ _).injective
        convert h using 1
        funext l
        rcases l with i | α <;> rfl)
      (by
        rw [show Fintype.card (Label Tag.E7) = 133 from by
          rw [Fintype.card_sum, Fintype.card_fin, card_isRoot]
          rfl,
          finrank_tangentSpace_realizedCoord_E7 (L := L) h2])
  exact b.repr.symm

theorem rootModuleTangentEquiv_single_inl (h2 : (2 : L) ≠ 0) (i : Fin Tag.E7.rank) :
    rootModuleTangentEquiv h2 (Finsupp.single (Sum.inl i) 1) = torusTangent Tag.E7 L i := by
  rw [rootModuleTangentEquiv, Module.Basis.repr_symm_single_one]
  simp only [basisOfLinearIndependentOfCardEqFinrank, Module.Basis.mk_apply, Sum.elim_inl]

theorem rootModuleTangentEquiv_single_inr (h2 : (2 : L) ≠ 0) (α : {α // IsRoot Tag.E7 α}) :
    rootModuleTangentEquiv h2 (Finsupp.single (Sum.inr α) 1) = rootTangent Tag.E7 L α.1 := by
  rw [rootModuleTangentEquiv, Module.Basis.repr_symm_single_one]
  simp only [basisOfLinearIndependentOfCardEqFinrank, Module.Basis.mk_apply, Sum.elim_inr]

theorem adTangent_rootDiagUnit_rootModuleTangentEquiv (h2 : (2 : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (ha : rootDiagUnit Tag.E7 a ∈ adjointGroup Tag.E7 L)
    (v : RootModule Tag.E7 L) :
    adTangent (adjointPointSubgroup Tag.E7 L)
        (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom ha)
        (rootModuleTangentEquiv h2 v) =
      rootModuleTangentEquiv h2 (rootDiag a v) := by
  have hsingle : ∀ b : Label Tag.E7,
      adTangent (adjointPointSubgroup Tag.E7 L)
        (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom ha)
        (rootModuleTangentEquiv h2 (Finsupp.single b 1)) =
      rootModuleTangentEquiv h2 (rootDiag a (Finsupp.single b 1)) := by
    intro b
    rcases b with i | α
    · rw [rootModuleTangentEquiv_single_inl, rootDiag_single_inl,
        rootModuleTangentEquiv_single_inl]
      exact adTangent_rootDiagUnit_torusTangent (L := L) ha i
    · rw [rootModuleTangentEquiv_single_inr, rootDiag_single, map_smul,
        rootModuleTangentEquiv_single_inr]
      simpa only [labelWt] using adTangent_rootDiagUnit_rootTangent (L := L) ha α.2
  have hmain : ∀ w : RootModule Tag.E7 L,
      adTangent (adjointPointSubgroup Tag.E7 L)
        (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom ha)
        (rootModuleTangentEquiv h2 w) =
      rootModuleTangentEquiv h2 (rootDiag a w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
        rw [map_add, map_add, map_add, hf, hg]
        simp only [map_add]
    | single c r =>
        have hc : Finsupp.single c r = r • Finsupp.single c (1 : L) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hc, map_smul, map_smul, map_smul, hsingle c, map_smul]
  exact hmain v

end Basis

section Involution

variable {p : ℕ} [Fact p.Prime] [CharP L p]

theorem exists_adTangent_involution_rootDiag (hp2 : p ≠ 2) {x : ModGL Tag.E7 L}
    (hx : x ∈ adjointGroup Tag.E7 L) (hx2 : x ^ 2 = 1) :
    ∃ a : Fin Tag.E7.rank → Lˣ, (∀ i, a i = 1 ∨ a i = -1) ∧ ((∀ i, a i = 1) → x = 1) ∧
      ∃ e : RootModule Tag.E7 L ≃ₗ[L] TangentSpace L (realizedCoord Tag.E7 L)
          (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L)),
        ∀ v, adTangent (adjointPointSubgroup Tag.E7 L)
            (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hx) (e v) =
          e (rootDiag a v) := by
  classical
  have hchar : (2 : L) ≠ 0 := by
    refine Ring.two_ne_zero ?_
    rw [ringChar.eq L p]
    exact hp2
  obtain ⟨g, hg, a, ha, hgx⟩ :=
    exceptional_Lang_inner_involution_torus_conjugacy Tag.E7 hp2 L hx hx2
  have haG : rootDiagUnit Tag.E7 a ∈ adjointGroup Tag.E7 L := by
    rw [← hgx]
    exact mul_mem (mul_mem hg hx) (inv_mem hg)
  have hxM : (modGLPoint Tag.E7 L) x ∈ adjointPointSubgroup Tag.E7 L :=
    Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hx
  have hgM : (modGLPoint Tag.E7 L) g ∈ adjointPointSubgroup Tag.E7 L :=
    Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hg
  have hgiM : ((modGLPoint Tag.E7 L) g)⁻¹ ∈ adjointPointSubgroup Tag.E7 L := by
    rw [← map_inv]
    exact Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom (inv_mem hg)
  have haM : (modGLPoint Tag.E7 L) (rootDiagUnit Tag.E7 a) ∈
      adjointPointSubgroup Tag.E7 L :=
    Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom haG
  have hxg : x * g⁻¹ = g⁻¹ * rootDiagUnit Tag.E7 a := by
    rw [← hgx]
    group
  have hxgM : (modGLPoint Tag.E7 L) x * ((modGLPoint Tag.E7 L) g)⁻¹ =
      ((modGLPoint Tag.E7 L) g)⁻¹ * (modGLPoint Tag.E7 L) (rootDiagUnit Tag.E7 a) := by
    simpa only [map_mul, map_inv] using congrArg (modGLPoint Tag.E7 L) hxg
  let Adx : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    adTangent (adjointPointSubgroup Tag.E7 L) hxM
  let Adg : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    adTangent (adjointPointSubgroup Tag.E7 L) hgM
  let Adgi : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    adTangent (adjointPointSubgroup Tag.E7 L) hgiM
  let Ada : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    adTangent (adjointPointSubgroup Tag.E7 L) haM
  have hAdgiAdg : Adgi * Adg = 1 := by
    rw [← adTangent_mul (adjointPointSubgroup Tag.E7 L) hgiM hgM, ← adTangent_one]
    exact adTangent_congr _ (by group) _ _
  have hAdgAdgi : Adg * Adgi = 1 := by
    rw [← adTangent_mul (adjointPointSubgroup Tag.E7 L) hgM hgiM, ← adTangent_one]
    exact adTangent_congr _ (by group) _ _
  have hleft : Adgi.comp Adg = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, hAdgiAdg]
    rfl
  have hright : Adg.comp Adgi = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, hAdgAdgi]
    rfl
  let E : TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L)) ≃ₗ[L]
      TangentSpace L (realizedCoord Tag.E7 L)
        (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L)) :=
    LinearEquiv.ofLinearMap Adgi Adg hleft hright
  have hAdMul : Adx * Adgi = Adgi * Ada := by
    rw [← adTangent_mul (adjointPointSubgroup Tag.E7 L) hxM hgiM,
      ← adTangent_mul (adjointPointSubgroup Tag.E7 L) hgiM haM]
    exact adTangent_congr _ hxgM _ _
  refine ⟨a, ha, ?_, ?_⟩
  · intro h1
    have ha1 : a = 1 := funext h1
    have hd : rootDiagUnit Tag.E7 a = 1 := by rw [ha1, rootDiagUnit_one]
    have hgx1 : g * x * g⁻¹ = 1 := by rw [hgx, hd]
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [hgx1]
      _ = 1 := by group
  · refine ⟨(rootModuleTangentEquiv hchar).trans E, fun v => ?_⟩
    change Adx (E ((rootModuleTangentEquiv hchar) v)) =
      E ((rootModuleTangentEquiv hchar) (rootDiag a v))
    calc Adx (E ((rootModuleTangentEquiv hchar) v))
        = (Adx * Adgi) ((rootModuleTangentEquiv hchar) v) := rfl
      _ = (Adgi * Ada) ((rootModuleTangentEquiv hchar) v) := by rw [hAdMul]
      _ = Adgi (Ada ((rootModuleTangentEquiv hchar) v)) := rfl
      _ = Adgi ((rootModuleTangentEquiv hchar) (rootDiag a v)) := by
            change Adgi (adTangent (adjointPointSubgroup Tag.E7 L)
              (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom haG)
              ((rootModuleTangentEquiv hchar) v)) = _
            rw [adTangent_rootDiagUnit_rootModuleTangentEquiv (L := L) hchar haG v]
      _ = E ((rootModuleTangentEquiv hchar) (rootDiag a v)) := rfl

private theorem finrank_ker_adTangent_eq {x : ModGL Tag.E7 L}
    (hx : x ∈ adjointGroup Tag.E7 L) {a : Fin Tag.E7.rank → Lˣ}
    (e : RootModule Tag.E7 L ≃ₗ[L] TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L)))
    (he : ∀ v, adTangent (adjointPointSubgroup Tag.E7 L)
        (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hx) (e v) =
      e (rootDiag a v)) :
    Module.finrank L (LinearMap.ker (adTangent (adjointPointSubgroup Tag.E7 L)
        (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hx) - 1)) =
      Module.finrank L (LinearMap.ker (rootDiag a - 1)) := by
  have hker : LinearMap.ker (adTangent (adjointPointSubgroup Tag.E7 L)
        (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hx) - 1) =
      (LinearMap.ker (rootDiag a - 1)).map e.toLinearMap := by
    ext w
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    conv_lhs => rw [show w = e (e.symm w) from (e.apply_symm_apply w).symm]
    repeat rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [he (e.symm w)]
    exact e.injective.eq_iff
  calc Module.finrank L (LinearMap.ker (adTangent (adjointPointSubgroup Tag.E7 L)
        (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hx) - 1))
      = Module.finrank L ((LinearMap.ker (rootDiag a - 1)).map e.toLinearMap) := by rw [hker]
    _ = Module.finrank L (LinearMap.ker (rootDiag a - 1)) :=
        LinearEquiv.finrank_map_eq e _

theorem e7_adTangent_involution_fixed_finrank_ge (hp2 : p ≠ 2) {x : ModGL Tag.E7 L}
    (hx : x ∈ adjointGroup Tag.E7 L) (hx2 : x ^ 2 = 1) :
    63 ≤ Module.finrank L (LinearMap.ker (adTangent (adjointPointSubgroup Tag.E7 L)
      (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hx) - 1)) := by
  classical
  have hchar : (2 : L) ≠ 0 := by
    refine Ring.two_ne_zero ?_
    rw [ringChar.eq L p]
    exact hp2
  obtain ⟨a, ha, -, e, he⟩ :=
    exists_adTangent_involution_rootDiag (p := p) hp2 hx hx2
  rw [finrank_ker_adTangent_eq hx e he]
  exact e7_sign_fixed_finrank_ge hchar a ha

theorem e7_adFixedTangent_pair_finrank_ge (hp2 : p ≠ 2) {x y : ModGL Tag.E7 L}
    (hx : x ∈ adjointGroup Tag.E7 L) (hy : y ∈ adjointGroup Tag.E7 L) (hx2 : x ^ 2 = 1)
    (hy2 : y ^ 2 = 1) (hxy : Commute x y) :
    28 ≤ Module.finrank L (adFixedTangent (adjointPointSubgroup Tag.E7 L)
      {(modGLPoint Tag.E7 L).toMonoidHom x, (modGLPoint Tag.E7 L).toMonoidHom y}) := by
  classical
  have hchar : (2 : L) ≠ 0 := by
    refine Ring.two_ne_zero ?_
    rw [ringChar.eq L p]
    exact hp2
  have hfd : FiniteDimensional L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    finiteDimensional_tangentSpace (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))
  let _ := hfd
  have hxM : (modGLPoint Tag.E7 L) x ∈ adjointPointSubgroup Tag.E7 L :=
    Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hx
  have hyM : (modGLPoint Tag.E7 L) y ∈ adjointPointSubgroup Tag.E7 L :=
    Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hy
  change 28 ≤ Module.finrank L (adFixedTangent (adjointPointSubgroup Tag.E7 L)
    {(modGLPoint Tag.E7 L) x, (modGLPoint Tag.E7 L) y})
  rw [adFixedTangent_pair_eq (adjointPointSubgroup Tag.E7 L) hxM hyM]
  let σ : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    adTangent (adjointPointSubgroup Tag.E7 L) hxM
  let τ : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    adTangent (adjointPointSubgroup Tag.E7 L) hyM
  have hsqx : (modGLPoint Tag.E7 L) x * (modGLPoint Tag.E7 L) x = 1 := by
    simpa [pow_two] using congrArg (modGLPoint Tag.E7 L) hx2
  have hsqy : (modGLPoint Tag.E7 L) y * (modGLPoint Tag.E7 L) y = 1 := by
    simpa [pow_two] using congrArg (modGLPoint Tag.E7 L) hy2
  have hmulx : σ * σ = 1 := by
    change adTangent (adjointPointSubgroup Tag.E7 L) hxM *
        adTangent (adjointPointSubgroup Tag.E7 L) hxM = 1
    rw [← adTangent_mul (adjointPointSubgroup Tag.E7 L) hxM hxM, ← adTangent_one]
    exact adTangent_congr _ hsqx _ _
  have hmuly : τ * τ = 1 := by
    change adTangent (adjointPointSubgroup Tag.E7 L) hyM *
        adTangent (adjointPointSubgroup Tag.E7 L) hyM = 1
    rw [← adTangent_mul (adjointPointSubgroup Tag.E7 L) hyM hyM, ← adTangent_one]
    exact adTangent_congr _ hsqy _ _
  have hσ : ∀ w, σ (σ w) = w := by
    intro w
    have h := congrArg (fun u : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
        (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) => u w) hmulx
    simpa [Module.End.mul_apply] using h
  have hτ : ∀ w, τ (τ w) = w := by
    intro w
    have h := congrArg (fun u : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
        (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) => u w) hmuly
    simpa [Module.End.mul_apply] using h
  have hcommM : (modGLPoint Tag.E7 L) x * (modGLPoint Tag.E7 L) y =
      (modGLPoint Tag.E7 L) y * (modGLPoint Tag.E7 L) x := by
    simpa only [map_mul] using congrArg (modGLPoint Tag.E7 L) hxy
  have hcomm : σ * τ = τ * σ := by
    change adTangent (adjointPointSubgroup Tag.E7 L) hxM *
        adTangent (adjointPointSubgroup Tag.E7 L) hyM =
      adTangent (adjointPointSubgroup Tag.E7 L) hyM *
        adTangent (adjointPointSubgroup Tag.E7 L) hxM
    rw [← adTangent_mul (adjointPointSubgroup Tag.E7 L) hxM hyM,
      ← adTangent_mul (adjointPointSubgroup Tag.E7 L) hyM hxM]
    exact adTangent_congr _ hcommM _ _
  have hστ : ∀ w, σ (τ w) = τ (σ w) := by
    intro w
    have h := congrArg (fun u : Module.End L (TangentSpace L (realizedCoord Tag.E7 L)
        (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) => u w) hcomm
    simpa [Module.End.mul_apply] using h
  obtain ⟨h1, h2, h3, h4⟩ :=
    CFSG.RankThree.OddKernel.finrank_four_group hchar σ τ hσ hτ hστ ⊤
      (fun _ _ => trivial) (fun _ _ => trivial)
  have htop : ∀ s : Submodule L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))),
      Module.finrank L ↥(⊤ ⊓ s) = Module.finrank L ↥s := by
    intro s
    rw [top_inf_eq]
  simp only [htop] at h1 h2 h3 h4
  have hdim : Module.finrank L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) = 133 :=
    finrank_tangentSpace_realizedCoord_E7 hchar
  have htopdim : (133 : ℕ) = Module.finrank L ↥(⊤ : Submodule L
      (TangentSpace L (realizedCoord Tag.E7 L)
        (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L)))) := by
    rw [finrank_top]
    exact hdim.symm
  have htotal := htopdim.trans h1
  have hx63 : 63 ≤ Module.finrank L (CFSG.RankThree.OddKernel.fixSpace σ) := by
    change 63 ≤ Module.finrank L (CFSG.RankThree.OddKernel.fixSpace
      (adTangent (adjointPointSubgroup Tag.E7 L) hxM))
    exact e7_adTangent_involution_fixed_finrank_ge (p := p) hp2 hx hx2
  have hy63 : 63 ≤ Module.finrank L (CFSG.RankThree.OddKernel.fixSpace τ) := by
    change 63 ≤ Module.finrank L (CFSG.RankThree.OddKernel.fixSpace
      (adTangent (adjointPointSubgroup Tag.E7 L) hyM))
    exact e7_adTangent_involution_fixed_finrank_ge (p := p) hp2 hy hy2
  have hxyMem : x * y ∈ adjointGroup Tag.E7 L := mul_mem hx hy
  have hxy2 : (x * y) ^ 2 = 1 := by
    rw [hxy.mul_pow 2, hx2, hy2, mul_one]
  have hcomp : σ ∘ₗ τ = adTangent (adjointPointSubgroup Tag.E7 L)
      (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hxyMem) := by
    change adTangent (adjointPointSubgroup Tag.E7 L) hxM *
        adTangent (adjointPointSubgroup Tag.E7 L) hyM =
      adTangent (adjointPointSubgroup Tag.E7 L)
        (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hxyMem)
    rw [← adTangent_mul (adjointPointSubgroup Tag.E7 L) hxM hyM]
    exact adTangent_congr _ (map_mul (modGLPoint Tag.E7 L) x y).symm _ _
  have hxy63 : 63 ≤ Module.finrank L
      (CFSG.RankThree.OddKernel.fixSpace (σ ∘ₗ τ)) := by
    rw [hcomp]
    exact e7_adTangent_involution_fixed_finrank_ge (p := p) hp2 hxyMem hxy2
  have hgoal : 28 ≤ Module.finrank L ↥(CFSG.RankThree.OddKernel.fixSpace σ ⊓
      CFSG.RankThree.OddKernel.fixSpace τ) := by
    rw [h2] at hx63
    rw [h3] at hy63
    rw [h4] at hxy63
    omega
  exact hgoal

end Involution

end CFSG.LieType.AlgebraicGroups

end
