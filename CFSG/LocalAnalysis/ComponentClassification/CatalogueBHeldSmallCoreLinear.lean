module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBHeldSmallCore

open scoped LinearAlgebra.Projectivization MatrixGroups

instance three_prime_fact : Fact (Nat.Prime 3) := ⟨by decide⟩

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def projectiveAction :
    (V ≃ₗ[K] V) →* Equiv.Perm (Projectivization K V) :=
  MulAction.toPermHom (V ≃ₗ[K] V) (Projectivization K V)

theorem projectiveAction_ker_scalar (f : (projectiveAction (K := K) (V := V)).ker) :
    ∃ a : K, (f.val : V →ₗ[K] V) = a • 1 := by
  have hf : ∀ D : Projectivization K V, f.val • D = D := by
    intro D
    exact congrArg (fun e : Equiv.Perm (Projectivization K V) => e D) f.property
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro v
  by_cases hv : v = 0
  · simp [hv, linearIndependent_fin2]
  · simpa [LinearIndependent.pair_iff' hv, Projectivization.mk_eq_mk_iff'] using!
      hf (Projectivization.mk K v hv)

theorem projectiveAction_mem_ker_iff (f : V ≃ₗ[K] V) :
    f ∈ (projectiveAction (K := K) (V := V)).ker ↔
      ∃ a : K, (f : V →ₗ[K] V) = a • 1 := by
  constructor
  · exact fun hf => projectiveAction_ker_scalar ⟨f, hf⟩
  · rintro ⟨a, ha⟩
    apply Equiv.ext
    intro D
    induction D using Projectivization.ind with
    | h v hv =>
      change f • Projectivization.mk K v hv = Projectivization.mk K v hv
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      exact ⟨a, by
        have h := congrArg (fun l : V →ₗ[K] V => l v) ha
        simpa using h.symm⟩

theorem projectiveAction_ker_isMulCommutative :
    IsMulCommutative (projectiveAction (K := K) (V := V)).ker := by
  apply IsMulCommutative.of_comm
  intro f g
  obtain ⟨a, ha⟩ := projectiveAction_ker_scalar f
  obtain ⟨b, hb⟩ := projectiveAction_ker_scalar g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hf : ∀ w, f.val w = a • w := fun w => by
    simpa using congrArg (fun l : V →ₗ[K] V => l w) ha
  have hg : ∀ w, g.val w = b • w := fun w => by
    simpa using congrArg (fun l : V →ₗ[K] V => l w) hb
  change f.val (g.val v) = g.val (f.val v)
  rw [hf, hg, hf, hg, smul_smul, smul_smul, mul_comm a b]

theorem linearAut_solvable_of_projective_card_le_four [Finite (Projectivization K V)]
    (hcard : Nat.card (Projectivization K V) ≤ 4) : Group.IsSolvable (V ≃ₗ[K] V) := by
  let : IsMulCommutative (projectiveAction (K := K) (V := V)).ker :=
    projectiveAction_ker_isMulCommutative
  let : Group.IsSolvable (Equiv.Perm (Projectivization K V)) := Equiv.Perm.isSolvable hcard
  exact Group.isSolvable_of_ker_le_range (projectiveAction (K := K) (V := V)).ker.subtype
    projectiveAction (by rw [Subgroup.range_subtype])

theorem projective_line_three_card :
    Nat.card (Projectivization (ZMod 3) (Fin 2 → ZMod 3)) = 4 := by
  rw [Projectivization.card_of_finrank_two (ZMod 3) (Fin 2 → ZMod 3)
    (by simp [Module.finrank_fintype_fun_eq_card])]
  simp

theorem gl_two_three_solvable :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  let : Group.IsSolvable ((Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3)) :=
    linearAut_solvable_of_projective_card_le_four (by rw [projective_line_three_card])
  let e := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin 2 → ZMod 3))
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem cyclic_automorphism_solvable (H : Type*) [Group H] [IsCyclic H] :
    Group.IsSolvable (MulAut H) :=
  Group.isSolvable_of_isSolvable_injective
    (f := (IsCyclic.mulAutMulEquiv H).toMonoidHom) (IsCyclic.mulAutMulEquiv H).injective

theorem elementaryAbelian_nine_automorphism_solvable (H : Type*) [Group H] [Finite H]
    [CFSG.IsElementaryAbelian 3 H] (hcard : Nat.card H = 9) :
    Group.IsSolvable (MulAut H) := by
  classical
  let : CommGroup H := IsMulCommutative.instCommGroup
  let A := Additive H
  have hAcard : Nat.card A = 9 := by
    rw [Nat.card_congr (Additive.toMul : Additive H ≃ H), hcard]
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := A)
  rw [Nat.card_zmod, hAcard] at hpow
  have hrank : Module.finrank (ZMod 3) A = 2 := by
    apply (Nat.pow_right_injective (by norm_num : 2 ≤ 3))
    simpa using hpow.symm
  let e : A ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) :=
    (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (hrank.trans (by simp [Module.finrank_fintype_fun_eq_card]))).some
  let b : Module.Basis (Fin 2) (ZMod 3) A := (Pi.basisFun (ZMod 3) (Fin 2)).map e.symm
  let autLinear : MulAut H ≃* (A ≃ₗ[ZMod 3] A) :=
    { toFun := fun f => (MulEquiv.toAdditive f).toLinearEquiv
        (ZMod.map_smul (MulEquiv.toAdditive f))
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => by ext x; rfl }
  let eGL := autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) A).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm)
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := gl_two_three_solvable
  exact Group.isSolvable_of_isSolvable_injective (f := eGL.toMonoidHom) eGL.injective

end CFSG.ComponentClassification.CatalogueBHeldSmallCore
