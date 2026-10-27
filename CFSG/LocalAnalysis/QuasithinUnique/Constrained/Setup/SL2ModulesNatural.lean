module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Natural

variable {F : Type*} [Field F]

theorem frobTensor_singleton_apply {k : Type*} [Field k] [Algebra F k] [CharP k 2] (j : ℕ)
    (g : SL(2, F)) (y : ((↥({j} : Finset ℕ)) → Fin 2) → k) (a : Fin 2) :
    frobTensor F k {j} g y (fun _ => a) =
      ∑ c : Fin 2, (algebraMap F k (g a c)) ^ (2 ^ j) * y (fun _ => c) := by
  have hU : Unique (↥({j} : Finset ℕ)) :=
    ⟨⟨⟨j, Finset.mem_singleton_self j⟩⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.2)⟩
  unfold frobTensor
  rw [tensorRep_apply]
  rw [← Equiv.sum_comp (Equiv.funUnique ↥({j} : Finset ℕ) (Fin 2)).symm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : (Equiv.funUnique ↥({j} : Finset ℕ) (Fin 2)).symm c = fun _ => c := rfl
  rw [this]
  congr 1
  simp only [tmatE, Fintype.prod_unique, twistMat_apply]
  rw [Finset.mem_singleton.mp (default : ↥({j} : Finset ℕ)).2]

variable [Fintype F] [CharP F 2] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

set_option synthInstance.maxHeartbeats 400000 in
theorem exists_coordinate_iso {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    {d : ℕ} (hD : Nat.card (EndRing ρ) = 2 ^ d) (hdim : Module.finrank (EndRing ρ) W = 2)
    (ιF : F →+* EndRing ρ) :
    ∃ (j : ℕ) (θ : W ≃+ (Fin 2 → EndRing ρ)), ∀ (g : SL(2, F)) (w : W) (a : Fin 2),
      θ (ρ g w) a =
        ∑ c : Fin 2, (ιF ((g : Matrix (Fin 2) (Fin 2) F) a c)) ^ (2 ^ j) * θ w c := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  let _ : Algebra F (EndRing ρ) := ιF.toAlgebra
  obtain ⟨J, hJne, hJn, ⟨Φ⟩, -, hJdim⟩ :=
    descent_core hn hF ρ hnt hD b ιF (RingHom.id (EndRing ρ))
  have hJcard : J.card = 1 := by
    have h1 : 2 ^ J.card = 2 ^ 1 := by rw [← hJdim, hdim]; rfl
    exact Nat.pow_right_injective le_rfl h1
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJcard
  let θ : W ≃+ (Fin 2 → EndRing ρ) :=
    (b.equivFun.toAddEquiv.trans Φ.toLinearEquiv.toAddEquiv).trans
      (LinearEquiv.funCongrLeft (EndRing ρ) (EndRing ρ)
        (Equiv.funUnique ↥({j} : Finset ℕ) (Fin 2)).symm).toAddEquiv
  have hθ : ∀ w a, θ w a = Φ (b.equivFun w) (fun _ => a) := fun w a => rfl
  refine ⟨j, θ, fun g w a => ?_⟩
  have hcoord : b.equivFun (ρ g w) = matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w) := by
    rw [matRepE_apply]
    have := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
    rw [repD_apply] at this
    simpa [matRep] using this.symm
  rw [hθ, hcoord, equiv_apply Φ g, frobTensor_singleton_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hθ]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem exists_natural_iso {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    (hD : Nat.card (EndRing ρ) = 2 ^ n) (hdim : Module.finrank (EndRing ρ) W = 2) :
    ∃ φ : W ≃+ (Fin 2 → F),
      ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w) := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  let _ : Fintype (EndRing ρ) := Fintype.ofFinite _
  have hcardD : Fintype.card F = Fintype.card (EndRing ρ) := by
    rw [hF, ← Nat.card_eq_fintype_card, hD]
  let ιF : F ≃+* EndRing ρ := FiniteField.ringEquivOfCardEq hcardD
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  obtain ⟨j, θ, hθ⟩ := exists_coordinate_iso hn hF ρ hnt hD hdim (ιF : F →+* EndRing ρ)
  let frobj : F →+* EndRing ρ := (iterateFrobenius (EndRing ρ) 2 j).comp (ιF : F →+* EndRing ρ)
  have hbij : Function.Bijective frobj := by
    refine frobj.injective.bijective_of_nat_card_le ?_
    rw [hD, Nat.card_eq_fintype_card, hF]
  let κ : EndRing ρ ≃+* F := (RingEquiv.ofBijective frobj hbij).symm
  have hκ : ∀ z : F, κ ((ιF z) ^ (2 ^ j)) = z := fun z => by
    have h : frobj z = (ιF z) ^ (2 ^ j) := by simp [frobj, iterateFrobenius_def]
    rw [← h]
    exact (RingEquiv.ofBijective frobj hbij).symm_apply_apply z
  let φ : W ≃+ (Fin 2 → F) := θ.trans (AddEquiv.piCongrRight (fun _ : Fin 2 => κ.toAddEquiv))
  refine ⟨φ, fun g w => ?_⟩
  funext a
  show κ (θ (ρ g w) a) = _
  rw [hθ, map_sum]
  simp only [Matrix.mulVec, dotProduct, map_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact hκ _

end Natural

end CFSG.QuasithinUnique.Setup.SL2Modules
