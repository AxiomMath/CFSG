module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCount
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFlip
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCollapse

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Transport

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] {m : ℕ}
  (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E] [CharP E 2] [Algebra F E]
  (ιD : EndRing ρ →+* E) (J : Finset ℕ)
  (Φ : (matRepE b ιD).Equiv (frobTensor F E J))

@[expose] noncomputable def tauHom :
    Module.End (EndRing ρ) W →+* Module.End E ((J → Fin 2) → E) where
  toFun a := Φ.toLinearEquiv.conj (Matrix.toLin' ((LinearMap.toMatrix b b a).map ιD))
  map_one' := by
    rw [LinearMap.toMatrix_one, Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.toLin'_one]
    exact LinearEquiv.conj_id _
  map_mul' a a' := by
    rw [LinearMap.toMatrix_mul, Matrix.map_mul, Matrix.toLin'_mul]
    exact LinearEquiv.conj_comp _ _ _
  map_zero' := by
    rw [map_zero, Matrix.map_zero ιD (map_zero ιD), map_zero, map_zero]
  map_add' a a' := by
    rw [map_add, Matrix.map_add _ (fun x y => ιD.map_add x y), map_add, map_add]

theorem tauHom_apply (a : Module.End (EndRing ρ) W) (y : (J → Fin 2) → E) :
    tauHom ρ b ιD J Φ a y =
      Φ.toLinearEquiv (((LinearMap.toMatrix b b a).map ιD).mulVec (Φ.toLinearEquiv.symm y)) := by
  rfl

theorem tauHom_repD (g : SL(2, F)) : tauHom ρ b ιD J Φ (repD ρ g) = frobTensor F E J g := by
  apply LinearMap.ext
  intro y
  rw [tauHom_apply]
  have h1 : (LinearMap.toMatrix b b (repD ρ g)) = matRep b g := rfl
  rw [h1, ← matRepE_apply]
  have h2 := equiv_apply Φ g (Φ.toLinearEquiv.symm y)
  have h3 : Φ (Φ.toLinearEquiv.symm y) = y := Φ.toLinearEquiv.apply_symm_apply y
  rw [h3] at h2
  exact h2

theorem natCard_fix_pow [Finite E] (a : Module.End (EndRing ρ) W) :
    Nat.card {w : W // a w = w} ^ (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) =
      Nat.card {y : (J → Fin 2) → E // tauHom ρ b ιD J Φ a y = y} := by
  have hcoord : ∀ w : W, (LinearMap.toMatrix b b a).mulVec (b.equivFun w) = b.equivFun (a w) :=
    fun w => LinearMap.toMatrix_mulVec_repr b b a w
  have h1 : {w : W // a w = w} ≃
      {x : Fin m → EndRing ρ // ∀ _ : Unit, (LinearMap.toMatrix b b a - 1).mulVec x = 0} :=
    Equiv.subtypeEquiv b.equivFun.toEquiv (fun w => by
      change a w = w ↔ ∀ _ : Unit, (LinearMap.toMatrix b b a - 1).mulVec (b.equivFun w) = 0
      constructor
      · intro h _
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, h, sub_self]
      · intro h
        have h' := h ()
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, sub_eq_zero] at h'
        exact b.equivFun.injective h')
  have h2 := natCard_common_ker_map ιD (fun _ : Unit => LinearMap.toMatrix b b a - 1)
  have h3 : {x : Fin m → E // ∀ _ : Unit, ((LinearMap.toMatrix b b a - 1).map ιD).mulVec x = 0} ≃
      {y : (J → Fin 2) → E // tauHom ρ b ιD J Φ a y = y} :=
    Equiv.subtypeEquiv Φ.toLinearEquiv.toEquiv (fun x => by
      have hx : tauHom ρ b ιD J Φ a (Φ.toLinearEquiv x) =
          Φ.toLinearEquiv (((LinearMap.toMatrix b b a).map ιD).mulVec x) := by
        rw [tauHom_apply, LinearEquiv.symm_apply_apply]
      change (∀ _ : Unit, ((LinearMap.toMatrix b b a - 1).map ιD).mulVec x = 0) ↔
        tauHom ρ b ιD J Φ a (Φ.toLinearEquiv x) = Φ.toLinearEquiv x
      rw [hx]
      constructor
      · intro h
        have h' := h ()
        rw [Matrix.map_sub _ (fun a b => ιD.map_sub a b),
          Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec, Matrix.one_mulVec,
          sub_eq_zero] at h'
        rw [h']
      · intro h _
        have h' := Φ.toLinearEquiv.injective h
        rw [Matrix.map_sub _ (fun a b => ιD.map_sub a b),
          Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec, Matrix.one_mulVec,
          sub_eq_zero]
        exact h')
  rw [Nat.card_congr h1]
  rw [Nat.card_congr h3] at h2
  exact h2.symm

omit [Finite W] in
@[expose] def linD (a : Module.End (ZMod 2) W) (ha : ∀ δ : EndRing ρ, a * epsHom ρ δ = epsHom ρ δ * a) :
    Module.End (EndRing ρ) W where
  toFun := a
  map_add' := a.map_add
  map_smul' δ w := by
    show a (δ w) = δ (a w)
    have h := congrArg (fun f : Module.End (ZMod 2) W => f w) (ha δ)
    simpa [epsHom_apply] using h

end Transport

section Count

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W)
  [Fact ρ.IsIrreducible] {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*}
  [Field E] [Finite E] [CharP E 2] [Algebra F E] (ιD : EndRing ρ →+* E) (J : Finset ℕ)
  (Φ : (matRepE b ιD).Equiv (frobTensor F E J))

include b ιD Φ in
theorem outer_involution_count {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ (2 * s))
    (hJ : ∀ i ∈ J, i < 2 * s) (a : Module.End (EndRing ρ) W) (ha2 : a * a = 1)
    (hconj : ∀ g : SL(2, F), a * repD ρ g = repD ρ (fieldAut F s g) * a) :
    J.image (shiftExp s) = J ∧ ∃ m' : ℕ, J.card = 2 * m' ∧
      Nat.card {w : W // a w = w} = Nat.card (EndRing ρ) ^ (2 ^ m' * (2 ^ m' + 1) / 2) := by
  have hτ2 : tauHom ρ b ιD J Φ a * tauHom ρ b ιD J Φ a = 1 := by
    rw [← map_mul, ha2, map_one]
  have hτconj : ∀ g : SL(2, F), tauHom ρ b ιD J Φ a * frobTensor F E J g =
      frobTensor F E J (fieldAut F s g) * tauHom ρ b ιD J Φ a := by
    intro g
    rw [← tauHom_repD ρ b ιD J Φ g, ← tauHom_repD ρ b ιD J Φ (fieldAut F s g), ← map_mul,
      ← map_mul, hconj g]
  obtain ⟨hJs, -, m', hm', hker, -⟩ :=
    frobTensor_field_involution hs hF hJ (tauHom ρ b ιD J Φ a) hτ2 hτconj
  refine ⟨hJs, m', hm', ?_⟩
  have h1 := natCard_fix_pow ρ b ιD J Φ a
  have h2 : Nat.card {y : (J → Fin 2) → E // tauHom ρ b ιD J Φ a y = y} =
      Nat.card E ^ (2 ^ m' * (2 ^ m' + 1) / 2) := by
    have e : {y : (J → Fin 2) → E // tauHom ρ b ιD J Φ a y = y} ≃
        ↥(LinearMap.ker (tauHom ρ b ιD J Φ a - 1)) :=
      Equiv.subtypeEquivRight (fun y => by
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero])
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := E), hker]
  have ht : 0 < (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) := by
    let _ := ιD.toAlgebra
    have : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
    exact Module.finrank_pos
  rw [h2, natCard_E_eq ιD, ← pow_mul, mul_comm, pow_mul] at h1
  exact Nat.pow_left_injective ht.ne' h1

end Count

end CFSG.QuasithinUnique.Setup.SL2Modules
