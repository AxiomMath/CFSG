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
  -- each vector is an eigenvector of `↑f`
  have hmem : ∀ v : V, (f.val : V →ₗ[K] V) v ∈ K ∙ v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, map_zero]
      exact Submodule.zero_mem _
    · rw [Submodule.mem_span_singleton]
      have hfix := hf (Projectivization.mk K v hv)
      rw [Projectivization.smul_mk] at hfix
      rw [Projectivization.mk_eq_mk_iff'] at hfix
      simpa using hfix
  rcases subsingleton_or_nontrivial V with hV | hV
  · haveI := hV
    exact ⟨1, by ext x; exact Subsingleton.elim _ _⟩
  · obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hmem v₀)
    have hpt : ∀ v : V, (f.val : V →ₗ[K] V) v = a • v := by
      intro v
      by_cases hv : v ∈ K ∙ v₀
      · obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hv
        calc (f.val : V →ₗ[K] V) v
              = (f.val : V →ₗ[K] V) (d • v₀) := congrArg _ hd.symm
          _ = d • (f.val : V →ₗ[K] V) v₀ := by rw [map_smul]
          _ = d • (a • v₀) := by rw [← ha]
          _ = a • (d • v₀) := by rw [smul_smul, smul_smul, mul_comm d a]
          _ = a • v := congrArg _ hd
      · obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hmem v)
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hmem (v₀ + v))
        have hpair : ∀ s t : K, s • v₀ + t • v = 0 → s = 0 ∧ t = 0 := by
          rw [← LinearIndependent.pair_iff, LinearIndependent.pair_iff' hv₀]
          intro d hd
          exact hv (Submodule.mem_span_singleton.mpr ⟨d, hd⟩)
        have heq : a • v₀ + b • v = c • v₀ + c • v := by
          calc a • v₀ + b • v
              = (f.val : V →ₗ[K] V) v₀ + (f.val : V →ₗ[K] V) v := by rw [← ha, ← hb]
            _ = (f.val : V →ₗ[K] V) (v₀ + v) := by rw [map_add]
            _ = c • (v₀ + v) := by rw [← hc]
            _ = c • v₀ + c • v := by rw [smul_add]
        have hzero : (a - c) • v₀ + (b - c) • v = 0 := by
          have h1 : a • v₀ + b • v - (c • v₀ + c • v) = 0 := sub_eq_zero.mpr heq
          have h2 : a • v₀ + b • v - (c • v₀ + c • v) =
              (a - c) • v₀ + (b - c) • v := by
            rw [sub_smul, sub_smul]; abel
          rwa [h2] at h1
        obtain ⟨hac, hbc⟩ := hpair (a - c) (b - c) hzero
        rw [sub_eq_zero] at hac hbc
        rw [← hb, hbc, hac]
    refine ⟨a, ?_⟩
    ext v
    simpa [LinearMap.smul_apply] using hpt v

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
