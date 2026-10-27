module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBaseChange
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInvolution
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Count

variable {F : Type*} [Field F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]

theorem natCard_fixW_pow {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {κ : Type*}
    (s : κ → SL(2, F)) {E : Type*} [Field E] [Finite E] [CharP E 2] (ιF : F →+* E)
    (ιD : EndRing ρ →+* E) (J : Finset ℕ)
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J))) :
    Nat.card {w : W // ∀ a, ρ (s a) w = w} ^ (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) =
      Nat.card {y : (J → Fin 2) → E // ∀ a, (letI := ιF.toAlgebra; frobTensor F E J (s a)) y = y} := by
  let _ := ιF.toAlgebra
  have hD : Finite (EndRing ρ) := finite_endRing ρ
  have hcoord : ∀ (g : SL(2, F)) (w : W),
      (matRep b g).mulVec (b.equivFun w) = b.equivFun (ρ g w) := fun g w =>
    LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  have h1 : {w : W // ∀ a, ρ (s a) w = w} ≃
      {x : Fin m → EndRing ρ // ∀ a, (matRep b (s a) - 1).mulVec x = 0} :=
    Equiv.subtypeEquiv b.equivFun.toEquiv (fun w => by
      change (∀ a, ρ (s a) w = w) ↔ ∀ a, (matRep b (s a) - 1).mulVec (b.equivFun w) = 0
      constructor
      · intro h a
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, h a, sub_self]
      · intro h a
        have := h a
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, sub_eq_zero] at this
        exact b.equivFun.injective this)
  have h2 := natCard_common_ker_map ιD (fun a => matRep b (s a) - 1)
  have h3 : {x : Fin m → E // ∀ a, ((matRep b (s a) - 1).map ιD).mulVec x = 0} ≃
      {y : (J → Fin 2) → E // ∀ a, frobTensor F E J (s a) y = y} :=
    Equiv.subtypeEquiv Φ.toLinearEquiv.toEquiv (fun x => by
      constructor
      · intro h a
        have h4 := h a
        have h5 : matRepE b ιD (s a) x = x := by
          rw [matRepE_apply]
          rw [Matrix.map_sub _ (fun a b => map_sub ιD a b), Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec,
            Matrix.one_mulVec, sub_eq_zero] at h4
          exact h4
        have := equiv_apply Φ (s a) x
        rw [h5] at this
        exact this.symm
      · intro h a
        have h4 := h a
        rw [Matrix.map_sub _ (fun a b => map_sub ιD a b), Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec,
          Matrix.one_mulVec, sub_eq_zero, ← matRepE_apply]
        apply Φ.toLinearEquiv.injective
        exact (equiv_apply Φ (s a) x).trans h4)
  rw [Nat.card_congr h1] 
  rw [Nat.card_congr h3] at h2
  exact h2.symm


theorem natCard_E_eq {D E : Type*} [Field D] [Field E] [Finite E] (ι : D →+* E) :
    Nat.card E = Nat.card D ^ (letI := ι.toAlgebra; Module.finrank D E) := by
  let _ := ι.toAlgebra
  have : Module.Finite D E := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank

theorem natCard_fixW_involution {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (ιF : F →+* E)
    (ιD : EndRing ρ →+* E) (J : Finset ℕ) (hJ : J.Nonempty)
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J)))
    (a : SL(2, F)) (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    Nat.card {w : W // ρ a w = w} = Nat.card (EndRing ρ) ^ 2 ^ (J.card - 1) := by
  let _ := ιF.toAlgebra
  have hD : Finite (EndRing ρ) := finite_endRing ρ
  have h1 := natCard_fixW_pow ρ b (fun _ : Unit => a) ιF ιD J Φ
  have : Nonempty J := hJ.to_subtype
  have hker : Nat.card {y : (J → Fin 2) → E // ∀ _ : Unit, frobTensor F E J a y = y} =
      Nat.card E ^ 2 ^ (J.card - 1) := by
    have h2 : {y : (J → Fin 2) → E // ∀ _ : Unit, frobTensor F E J a y = y} ≃
        ↥(LinearMap.ker (frobTensor F E J a - 1)) :=
      Equiv.subtypeEquivRight (fun y => by
        simp only [forall_const, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
          sub_eq_zero])
    rw [Nat.card_congr h2, Module.natCard_eq_pow_finrank (K := E)]
    congr 1
    have := finrank_ker_tensor_involution (F := F) (k := E) (fun i : J => (i : ℕ)) a ha1 ha2
    rw [Fintype.card_coe] at this
    exact this
  have ht : 0 < (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) := by
    let _ := ιD.toAlgebra
    have : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
    exact Module.finrank_pos
  rw [hker, natCard_E_eq ιD, ← pow_mul, mul_comm, pow_mul] at h1
  have h3 : (Nat.card {w : W // ∀ _ : Unit, ρ a w = w}) = Nat.card {w : W // ρ a w = w} := by
    simp
  rw [h3] at h1
  exact Nat.pow_left_injective ht.ne' h1

end Count

end CFSG.QuasithinUnique.Setup.SL2Modules
