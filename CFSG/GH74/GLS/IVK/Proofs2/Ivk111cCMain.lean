module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cCSL2Conj
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cCIncl
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ScalarDescent
public import CFSG.CharacterTheory.SteinbergBYModularRealization
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.LocalAnalysis.SectionRank.PRank
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.TensorProduct.Free

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG CFSG.CharacterTheory.SteinbergBY
open scoped TensorProduct

section OverK

variable {p n : ℕ} {F : Type} [Field F] (k : Type) [Field k] [Algebra F k]

theorem steinberg_nonempty_asModule_equiv {A V W : Type} [Field A] [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W] {G : Type} [Group G]
    {ρ : Representation A G V} {σ : Representation A G W} (e : ρ.Equiv σ) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra A G] σ.asModule) :=
  ⟨LinearEquiv.ofBijective (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
    e.toIntertwiningMap) e.bijective⟩

theorem steinberg_isEmpty_equiv (hI : SteinbergInjStmt) (hp : p.Prime) (hp2 : p ≠ 2) [Finite F]
    (hF : Nat.card F = p ^ n) (i j : Fin (p ^ n)) (hij : i ≠ j) :
    IsEmpty ((steinbergRep F k i.1).Equiv (steinbergRep F k j.1)) :=
  ⟨fun e => hij (Fin.ext (hI p n F k hp hp2 hF i.1 j.1 i.2 j.2
    (steinberg_nonempty_asModule_equiv e)))⟩

end OverK

section Closed

variable {p n : ℕ} {F : Type} [Field F]

theorem steinberg_complete_over (hS : SteinbergSimpleStmt) (hI : SteinbergInjStmt)
    (hp : p.Prime) (hp2 : p ≠ 2) [Finite F] (hF : Nat.card F = p ^ n) [CharP F p]
    (k : Type) [Field k] [Algebra F k] [IsAlgClosed k] [CharP k p]
    (W : Type) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k (SLm F) W) [σ.IsIrreducible] :
    ∃ B : ℕ, B < p ^ n ∧ Nonempty (σ.Equiv (steinbergRep F k B)) := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hFin : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hodd : Fintype.card F % 2 = 1 := by
    rw [hF', Nat.pow_mod, hp.eq_two_or_odd.resolve_left hp2]
    simp
  have hirr : ∀ i : Fin (p ^ n), (steinbergRep F k i.1).IsIrreducible := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr (hS p n F k hp hp2 hF i.1 i.2)
  have hfd : ∀ i : Fin (p ^ n), FiniteDimensional k (steinbergSub F k i.1) := fun i =>
    haveI := hirr i
    finiteDimensional_of_isIrreducible (steinbergRep F k i.1)
  have hcard : Fintype.card (PRegularClass p (SLm F)) ≤ Fintype.card (Fin (p ^ n)) := by
    rw [Fintype.card_fin, ← hF']
    exact sl2c_card_pRegularClass_le p hp2 hodd
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_card_pRegularClass_le_of_univ (k := k) (G := SLm F) p
    (ι := Fin (p ^ n)) (V := fun i => ↥(steinbergSub F k i.1)) (fun i => steinbergRep F k i.1)
    (steinberg_isEmpty_equiv k hI hp hp2 hF) hcard W σ
    (fun i => ⟨(Module.finBasis k _).equivFun⟩) ⟨(Module.finBasis k W).equivFun⟩
  exact ⟨i.1, i.2, ⟨e⟩⟩

end Closed

theorem steinberg_complete_of (hS : SteinbergSimpleStmt) (hI : SteinbergInjStmt) :
    SteinbergCompleteStmt := by
  intro p n F _ _ hp hp2 hF Q _ _ _ π hπ
  have hpf : Fact p.Prime := ⟨hp⟩
  have hFin : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hcharF : CharP F p := charP_of_card_eq_prime_pow hF'
  have hcharK : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hπirr : π.IsIrreducible := (Representation.irreducible_iff_isSimpleModule_asModule π).mpr hπ
  have hQnt : Nontrivial Q := by
    have := IsSimpleModule.nontrivial (MonoidAlgebra F (SLm F)) π.asModule
    exact π.asModuleEquiv.symm.toEquiv.nontrivial
  have hk : Nontrivial (AlgebraicClosure F ⊗[F] Q) :=
    (Module.Flat.tensorProduct_mk_injective F Q (AlgebraicClosure F)).nontrivial
  obtain ⟨U, hU0, hUirr⟩ := exists_isIrreducible_subrepresentation
    (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F) π)
  haveI := hUirr
  obtain ⟨B, hB, ⟨e⟩⟩ := steinberg_complete_over hS hI hp hp2 hF (AlgebraicClosure F)
    U.toSubmodule U.toRepresentation
  have hρirr : (steinbergRep F F B).IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr (hS p n F F hp hp2 hF B hB)
  have hVnt : Nontrivial (steinbergSub F F B) := by
    have := IsSimpleModule.nontrivial (MonoidAlgebra F (SLm F)) (steinbergRep F F B).asModule
    exact (steinbergRep F F B).asModuleEquiv.symm.toEquiv.nontrivial
  have : FiniteDimensional F (steinbergSub F F B) :=
    finiteDimensional_of_isIrreducible (steinbergRep F F B)
  let Φ : (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F)
      (steinbergRep F F B)).IntertwiningMap (steinbergRep F (AlgebraicClosure F) B) :=
    ⟨steinbergMulSub F (AlgebraicClosure F) B, fun g => LinearMap.ext fun x => steinbergMulSub_rep F _ B g x⟩
  let incl : U.toRepresentation.IntertwiningMap
      (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F) π) :=
    ⟨U.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  let T := incl.comp (e.symm.toIntertwiningMap.comp Φ)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : steinbergSub F F B)
  have hT : T ≠ 0 := by
    intro h0
    have h1 : T ((1 : AlgebraicClosure F) ⊗ₜ[F] v₀) = 0 := by rw [h0]; rfl
    have hΦ : Φ ((1 : AlgebraicClosure F) ⊗ₜ[F] v₀) = steinbergInclSub F (AlgebraicClosure F) B v₀ := by
      show steinbergMulSub F (AlgebraicClosure F) B ((1 : AlgebraicClosure F) ⊗ₜ[F] v₀) = _
      rw [steinbergMulSub_tmul, one_smul]
    have h2 : (e.symm (steinbergInclSub F (AlgebraicClosure F) B v₀) : U.toSubmodule) = 0 := by
      rw [← hΦ]
      exact Subtype.ext h1
    have h3 : steinbergInclSub F (AlgebraicClosure F) B v₀ = 0 := by
      have := congrArg e h2
      rwa [Representation.Equiv.apply_symm_apply, map_zero] at this
    exact hv₀ (steinbergInclSub_injective F (AlgebraicClosure F) B (h3.trans (map_zero _).symm))
  have hnz : ∃ f : (steinbergRep F F B).IntertwiningMap π, f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton ((steinbergRep F F B).IntertwiningMap π) :=
      ⟨fun f g => (hcon f).trans (hcon g).symm⟩
    have hsub' : Subsingleton (AlgebraicClosure F ⊗[F] ((steinbergRep F F B).IntertwiningMap π)) :=
      inferInstance
    obtain ⟨x, hx⟩ := (CFSG.Theory.Representation.intertwiningMapBaseChangeEquiv
      (E := AlgebraicClosure F) (steinbergRep F F B) π).surjective T
    apply hT
    rw [← hx, Subsingleton.elim x 0, map_zero]
  obtain ⟨f, hf⟩ := hnz
  have hbij : Function.Bijective f :=
    (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf
  exact ⟨B, hB, ⟨(LinearEquiv.ofBijective (Representation.IntertwiningMap.equivLinearMapAsModule
    (steinbergRep F F B) π f) hbij).symm⟩⟩

end CFSG.GH74.GLS.Stage4.Rest
