module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistGL
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A.GL

open Polynomial CFSG.Open

noncomputable section

abbrev q4pol : (ZMod 2)[X] := X ^ 2 + X + 1

instance fact_irreducible_q4pol : Fact (Irreducible q4pol) :=
  ⟨CFSG.HardMathSupport.Curtis.Coordinator.irreducible_X_sq_add_X_add_one_of_card_eq_two
    (K := ZMod 2) (by simp)⟩

abbrev Fq : Type := AdjoinRoot q4pol

theorem card_Fq : Nat.card Fq = 4 := by
  have h := CFSG.HardMathSupport.Curtis.Coordinator.natCard_adjoinRoot_of_card_eq_two
    (K := ZMod 2) (by simp) (b := q4pol) (Fact.out)
  rw [h]
  have : q4pol.natDegree = 2 := by unfold q4pol; compute_degree!
  rw [this]; norm_num


theorem finrank_Fq : Module.finrank (ZMod 2) Fq = 2 := by
  have h := (AdjoinRoot.powerBasis (Fact.out : Irreducible q4pol).ne_zero).finrank
  rw [AdjoinRoot.powerBasis_dim] at h
  have : q4pol.natDegree = 2 := by unfold q4pol; compute_degree!
  rw [h, this]

section FModule

variable {A : Type} [AddCommGroup A] [Module (ZMod 2) A]

def fHom (e : A ≃ₗ[ZMod 2] A) (hq : ∀ a, e (e a) + e a + a = 0) :
    Fq →ₐ[ZMod 2] Module.End (ZMod 2) A :=
  Ideal.Quotient.liftₐ (Ideal.span {q4pol}) (Polynomial.aeval (e : A →ₗ[ZMod 2] A)) (by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨t, rfl⟩ := hp
    rw [map_mul]
    have : Polynomial.aeval (e : A →ₗ[ZMod 2] A) q4pol = 0 := by
      apply LinearMap.ext
      intro a
      simp only [q4pol, map_add, map_pow, Polynomial.aeval_X, map_one]
      simp only [LinearMap.add_apply, LinearMap.zero_apply, pow_two, Module.End.mul_apply,
        Module.End.one_apply, LinearEquiv.coe_coe]
      exact hq a
    rw [this, zero_mul])

theorem fHom_root (e : A ≃ₗ[ZMod 2] A) (hq : ∀ a, e (e a) + e a + a = 0) :
    fHom e hq (AdjoinRoot.root q4pol) = (e : A →ₗ[ZMod 2] A) := by
  have h : fHom e hq (AdjoinRoot.root q4pol) =
      Polynomial.aeval (e : A →ₗ[ZMod 2] A) Polynomial.X := rfl
  rw [h, Polynomial.aeval_X]

theorem exists_fModule (e : A ≃ₗ[ZMod 2] A) (hq : ∀ a, e (e a) + e a + a = 0) :
    ∃ (_ : Module Fq A), IsScalarTower (ZMod 2) Fq A ∧
      ∀ a, (AdjoinRoot.root q4pol) • a = e a := by
  letI : Module Fq A := Module.compHom A (fHom e hq).toRingHom
  refine ⟨this, ⟨fun c f a => ?_⟩, fun a => ?_⟩
  · show (fHom e hq) (c • f) a = c • (fHom e hq f a)
    rw [map_smul]
    rfl
  · show (fHom e hq) (AdjoinRoot.root q4pol) a = e a
    rw [fHom_root]
    rfl

end FModule


section FLin

variable {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Module Fq A]
  [IsScalarTower (ZMod 2) Fq A]

theorem finrank_two_mul [FiniteDimensional (ZMod 2) A] :
    Module.finrank (ZMod 2) A = 2 * Module.finrank Fq A := by
  haveI : Module.Finite Fq A := Module.Finite.of_restrictScalars_finite (ZMod 2) Fq A
  have := Module.finrank_mul_finrank (ZMod 2) Fq A
  rw [finrank_Fq] at this
  exact this.symm

theorem root_pow_smul {e : A ≃ₗ[ZMod 2] A} (hroot : ∀ a, (AdjoinRoot.root q4pol) • a = e a)
    (n : ℕ) (a : A) : ((AdjoinRoot.root q4pol) ^ n) • a = (e ^ n) a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, hroot, ih, pow_succ, LinearEquiv.mul_apply]

theorem smul_comm_of_commute {e : A ≃ₗ[ZMod 2] A}
    (hroot : ∀ a, (AdjoinRoot.root q4pol) • a = e a) {g : A ≃ₗ[ZMod 2] A}
    (hg : ∀ a, g (e a) = e (g a)) (f : Fq) (a : A) : g (f • a) = f • g a := by
  have hgpow : ∀ (n : ℕ) (a : A), g ((e ^ n) a) = (e ^ n) (g a) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, ih]
  induction f using AdjoinRoot.induction_on with
  | _ p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, add_smul, add_smul, map_add, hp, hq]
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
        mul_smul, mul_smul, root_pow_smul hroot, root_pow_smul hroot, ← AdjoinRoot.algebraMap_eq,
        algebraMap_smul, algebraMap_smul, map_smul, hgpow]


end FLin

section Even

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {e : V ≃ₗ[ZMod 2] V}

@[expose] def resComSp (e : V ≃ₗ[ZMod 2] V) : comSp e ≃ₗ[ZMod 2] comSp e :=
  LinearEquiv.ofInjectiveEndo ((e : V →ₗ[ZMod 2] V).restrict (fun a ha => e_mem_comSp ha))
    (by
      intro a b hab
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val hab))

theorem resComSp_apply (a : comSp e) : ((resComSp e a : comSp e) : V) = e a := rfl

theorem even_finrank_comSp (h3 : e ^ 3 = 1) : Even (Module.finrank (ZMod 2) (comSp e)) := by
  have hq : ∀ a : comSp e, resComSp e (resComSp e a) + resComSp e a + a = 0 := by
    intro a
    apply Subtype.ext
    have := quad_of_mem_comSp h3 a.2
    simpa [resComSp_apply] using this
  obtain ⟨inst, hts, -⟩ := exists_fModule (resComSp e) hq
  haveI := inst
  haveI := hts
  rw [finrank_two_mul (A := comSp e)]
  exact even_two_mul _

end Even

end

end CFSG.LocalAnalysis.GLTheoremA.S172A.GL

end
