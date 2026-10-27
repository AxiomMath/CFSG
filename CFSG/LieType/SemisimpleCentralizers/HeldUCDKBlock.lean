module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDPrimary
public import Mathlib.RingTheory.AdjoinRoot

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

variable {L : Type} [Field L] {n : ℕ}

@[expose] noncomputable def Vf (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X])
    (F : Finset L[X]) (f : L[X]) : Submodule L (Fin n → L) :=
  LinearMap.ker (Matrix.toLin' (1 - Pmat s b F f))

theorem mem_Vf {s : Matrix (Fin n) (Fin n) L} {b : L[X] → L[X]} {F : Finset L[X]} {f : L[X]}
    {x : Fin n → L} : x ∈ Vf s b F f ↔ Pmat s b F f *ᵥ x = x := by
  rw [Vf, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero, eq_comm]

section Block

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}

theorem aeval_mem_Vf {f : L[X]} (q : L[X]) {x : Fin n → L} (hx : x ∈ Vf s b F f) :
    aeval s q *ᵥ x ∈ Vf s b F f := by
  rw [mem_Vf] at hx ⊢
  have hc : Pmat s b F f * aeval s q = aeval s q * Pmat s b F f := by
    rw [Pmat, ← map_mul, ← map_mul, mul_comm]
  rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hx]

theorem aeval_factor_mulVec_eq_zero (H : PrimaryHyp τ s m F a b) {f : L[X]} (hf : f ∈ F)
    {x : Fin n → L} (hx : x ∈ Vf s b F f) : aeval s f *ᵥ x = 0 := by
  rw [mem_Vf] at hx
  rw [← hx, Matrix.mulVec_mulVec, aeval_mul_Pmat_self H.hirr H.hmon H.hprod H.hsm H.hab hf,
    Matrix.zero_mulVec]

@[expose] noncomputable def opV (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X])
    (F : Finset L[X]) (f : L[X]) (q : L[X]) : Module.End L (Vf s b F f) :=
  (Matrix.toLin' (aeval s q)).restrict (fun _ hx => aeval_mem_Vf q hx)

theorem coe_opV {f : L[X]} (q : L[X]) (x : Vf s b F f) :
    ((opV s b F f q x : Vf s b F f) : Fin n → L) = aeval s q *ᵥ (x : Fin n → L) := by
  rfl

theorem coe_opV_pow {f : L[X]} (j : ℕ) (x : Vf s b F f) :
    (((opV s b F f X : Module.End L (Vf s b F f)) ^ j) x : Fin n → L) =
      aeval s (X ^ j : L[X]) *ᵥ (x : Fin n → L) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (opV s b F f X) j, Module.End.mul_apply, ih, coe_opV, Matrix.mulVec_mulVec,
      ← map_mul, ← pow_succ]

theorem coe_aeval_opV {f : L[X]} (q : L[X]) (x : Vf s b F f) :
    ((aeval (opV s b F f X) q : Module.End L (Vf s b F f)) x : Fin n → L) =
      aeval s q *ᵥ (x : Fin n → L) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq, map_add, Matrix.add_mulVec]
  | monomial k c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
      coe_opV_pow, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, aeval_X_pow]

end Block

section KAction

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}

theorem aeval_opV_factor {f : L[X]} (hkill : ∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0) :
    Polynomial.aeval (R := L) (opV s b F f X) f = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [coe_aeval_opV, LinearMap.zero_apply, Submodule.coe_zero, hkill x.1 x.2]

@[expose] noncomputable def psiK {f : L[X]} (hkill : ∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0) :
    AdjoinRoot f →+* Module.End L (Vf s b F f) :=
  Ideal.Quotient.lift (Ideal.span {f}) (Polynomial.aeval (R := L) (opV s b F f X)).toRingHom
    (by
      intro p hp
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hp
      change Polynomial.aeval (R := L) (opV s b F f X) (f * g) = 0
      rw [map_mul, aeval_opV_factor hkill, zero_mul])

noncomputable instance instModuleAdjoinRootVf {f : L[X]}
    [hk : Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)] :
    Module (AdjoinRoot f) (Vf s b F f) :=
  Module.compHom _ (psiK hk.out)

variable {f : L[X]} [hk : Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]

theorem coe_smul_mk (q : L[X]) (x : Vf s b F f) :
    ((AdjoinRoot.mk f q • x : Vf s b F f) : Fin n → L) = aeval s q *ᵥ (x : Fin n → L) := by
  show ((psiK hk.out (AdjoinRoot.mk f q)) x : Fin n → L) = _
  rw [psiK]
  change ((aeval (opV s b F f X) q : Module.End L (Vf s b F f)) x : Fin n → L) = _
  rw [coe_aeval_opV]

theorem psiK_algebraMap {f : L[X]} (hkill : ∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0) (l : L) :
    psiK hkill (algebraMap L (AdjoinRoot f) l) = algebraMap L (Module.End L (Vf s b F f)) l := by
  have hk : psiK hkill (AdjoinRoot.mk f (Polynomial.C l)) =
      Polynomial.aeval (R := L) (opV s b F f X) (Polynomial.C l) := by
    rw [psiK]
    exact Ideal.Quotient.lift_mk _ _ _
  have hmk : algebraMap L (AdjoinRoot f) l = AdjoinRoot.mk f (Polynomial.C l) :=
    (AdjoinRoot.mk_C (f := f) l).symm
  rw [hmk, hk, Polynomial.aeval_C]

theorem psiK_smul {f : L[X]} (hkill : ∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0) (l : L)
    (c : AdjoinRoot f) : psiK hkill (l • c) = l • psiK hkill c := by
  rw [Algebra.smul_def, map_mul, psiK_algebraMap, Algebra.smul_def]

instance instIsScalarTowerVf {f : L[X]} [hk : Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)] :
    IsScalarTower L (AdjoinRoot f) (Vf s b F f) where
  smul_assoc l c x := by
    show psiK hk.out (l • c) x = l • psiK hk.out c x
    rw [psiK_smul, LinearMap.smul_apply]

theorem starP_add (τ : L ≃+* L) (m : ℕ) (p q : L[X]) :
    starP τ m (p + q) = starP τ m p + starP τ m q := by
  simp only [starP, Polynomial.map_add, Polynomial.add_comp]

theorem eval₂_starP (τ : L ≃+* L) (m : ℕ) (f : L[X]) (q : L[X]) :
    q.eval₂ ((AdjoinRoot.of f).comp (τ : L →+* L)) (AdjoinRoot.root f ^ (m - 1)) =
      AdjoinRoot.mk f (starP τ m q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add, hp, hq, starP_add, map_add]
  | monomial k c =>
    rw [Polynomial.eval₂_monomial, RingHom.comp_apply, starP, Polynomial.map_monomial,
      Polynomial.monomial_comp, map_mul, map_pow, AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X]

@[expose] noncomputable def sigmaK (τ : L ≃+* L) (m : ℕ) {f : L[X]} (hdiv : f ∣ starP τ m f) :
    AdjoinRoot f →+* AdjoinRoot f :=
  AdjoinRoot.lift (f := f) ((AdjoinRoot.of f).comp (τ : L →+* L)) (AdjoinRoot.root f ^ (m - 1)) (by
    rw [eval₂_starP, AdjoinRoot.mk_eq_zero]
    exact hdiv)

theorem sigmaK_mk (τ : L ≃+* L) (m : ℕ) {f : L[X]} (hdiv : f ∣ starP τ m f) (q : L[X]) :
    sigmaK τ m hdiv (AdjoinRoot.mk f q) = AdjoinRoot.mk f (starP τ m q) := by
  rw [sigmaK, AdjoinRoot.lift_mk, eval₂_starP]

theorem sigmaK_of (τ : L ≃+* L) (m : ℕ) {f : L[X]} (hdiv : f ∣ starP τ m f) (l : L) :
    sigmaK τ m hdiv (AdjoinRoot.of f l) = AdjoinRoot.of f (τ l) := by
  rw [sigmaK, AdjoinRoot.lift_of, RingHom.comp_apply]
  rfl

theorem sigmaK_root (τ : L ≃+* L) (m : ℕ) {f : L[X]} (hdiv : f ∣ starP τ m f) :
    sigmaK τ m hdiv (AdjoinRoot.root f) = AdjoinRoot.root f ^ (m - 1) := by
  rw [sigmaK, AdjoinRoot.lift_root]

theorem root_pow_eq_one {m : ℕ} {f : L[X]} (hdvd : f ∣ (X ^ m - 1 : L[X])) :
    AdjoinRoot.root f ^ m = 1 := by
  have h0 : AdjoinRoot.mk f (X ^ m - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
  exact h0

theorem sigmaK_sigmaK (τ : L ≃+* L) (hτ : ∀ x, τ (τ x) = x) {m : ℕ} (hm : 0 < m)
    {f : L[X]} (hdiv : f ∣ starP τ m f) (hdvd : f ∣ (X ^ m - 1 : L[X])) (x : AdjoinRoot f) :
    sigmaK τ m hdiv (sigmaK τ m hdiv x) = x := by
  have hcomp : (sigmaK τ m hdiv).comp (sigmaK τ m hdiv) = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · ext l
      simp only [RingHom.comp_apply, RingHom.id_apply, RingHom.coe_comp, Function.comp_apply]
      rw [sigmaK_of, sigmaK_of, hτ]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [sigmaK_root, map_pow, sigmaK_root]
      set β := AdjoinRoot.root f ^ (m - 1) with hβ
      have hβm : β ^ m = 1 := by
        rw [hβ, ← pow_mul, mul_comm, pow_mul, root_pow_eq_one hdvd, one_pow]
      have h1 : β ^ (m - 1) * β = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hm, hβm]
      have h2 : β * AdjoinRoot.root f = 1 := by
        rw [hβ, ← pow_succ, Nat.sub_add_cancel hm, root_pow_eq_one hdvd]
      calc β ^ (m - 1) = β ^ (m - 1) * (β * AdjoinRoot.root f) := by rw [h2, mul_one]
        _ = (β ^ (m - 1) * β) * AdjoinRoot.root f := by rw [mul_assoc]
        _ = AdjoinRoot.root f := by rw [h1, one_mul]
  exact congrArg (fun g : AdjoinRoot f →+* AdjoinRoot f => g x) hcomp

end KAction

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
