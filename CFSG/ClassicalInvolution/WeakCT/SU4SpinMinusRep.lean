module

public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusData

public section

namespace CFSG.ClassicalInvolution.WeakCT.SU4

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CliffordAlgebra QuadraticMap
open scoped Matrix

@[expose] def iZ : Fin (3 - 1) := ⟨0, by decide⟩

@[expose] def iO : Fin (3 - 1) := ⟨1, by decide⟩

section Coordinates

variable {F : Type} [Field F] {b c : F}

theorem quadMinus_three_apply (v : Vm 3 F) : quadMinus 3 F b c v =
    v (.inl iZ) * v (.inr (.inl iZ)) + v (.inl iO) * v (.inr (.inl iO)) +
      v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2 := by
  rw [quadMinus_apply]
  have h : ∑ i : Fin (3 - 1), v (.inl i) * v (.inr (.inl i)) =
      v (.inl iZ) * v (.inr (.inl iZ)) + v (.inl iO) * v (.inr (.inl iO)) :=
    Fin.sum_univ_two (fun i : Fin 2 => v (.inl i) * v (.inr (.inl i)))
  rw [h]

end Coordinates

namespace KleinData

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}
  (D : KleinData F K σ₀ b c)

@[expose] def Xmat (v : Vm 3 F) : Matrix (Fin 4) (Fin 4) K :=
  skew6 (algebraMap F K (v (.inl iZ))) (algebraMap F K (v (.inr (.inl iZ))))
    (D.δ * algebraMap F K (v (.inl iO))) (-(D.ε * algebraMap F K (v (.inr (.inl iO)))))
    (algebraMap F K (v (.inr (.inr 0))) - algebraMap F K (v (.inr (.inr 1))) * D.ω)
    (algebraMap F K (v (.inr (.inr 0))) + algebraMap F K (v (.inr (.inr 1))) * algebraMap F K b +
      algebraMap F K (v (.inr (.inr 1))) * D.ω)

@[expose] def Xlin : Vm 3 F →ₗ[F] Matrix (Fin 4) (Fin 4) K where
  toFun := D.Xmat
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xmat, skew6] <;> ring
  map_smul' r v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xmat, skew6, Algebra.smul_def] <;> ring

theorem Xlin_apply (v : Vm 3 F) : D.Xlin v = D.Xmat v := rfl

@[expose] def HsLin : Matrix (Fin 4) (Fin 4) K →ₗ[F] Matrix (Fin 4) (Fin 4) K where
  toFun := D.Hs
  map_add' := D.Hs_add
  map_smul' r X := D.Hs_smul r X

theorem HsLin_apply (X : Matrix (Fin 4) (Fin 4) K) : D.HsLin X = D.Hs X := rfl

theorem Hs_Xmat (v : Vm 3 F) :
    D.Hs (D.Xmat v) =
      skew6 (-algebraMap F K (v (.inr (.inl iZ)))) (-algebraMap F K (v (.inl iZ)))
        (-(D.ε * algebraMap F K (v (.inr (.inl iO))))) (D.δ * algebraMap F K (v (.inl iO)))
        (-(algebraMap F K (v (.inr (.inr 0))) +
          algebraMap F K (v (.inr (.inr 1))) * algebraMap F K b +
            algebraMap F K (v (.inr (.inr 1))) * D.ω))
        (-(algebraMap F K (v (.inr (.inr 0))) -
          algebraMap F K (v (.inr (.inr 1))) * D.ω)) := by
  rw [Xmat, Hs_skew6]
  have e1 := D.σ_alg (v (.inl iZ))
  have e2 := D.σ_alg (v (.inr (.inl iZ)))
  have e3 : σ₀ (D.δ * algebraMap F K (v (.inl iO))) = -(D.δ * algebraMap F K (v (.inl iO))) := by
    rw [map_mul, D.σ_δ, D.σ_alg]; ring
  have e4 : σ₀ (-(D.ε * algebraMap F K (v (.inr (.inl iO))))) =
      D.ε * algebraMap F K (v (.inr (.inl iO))) := by
    rw [map_neg, map_mul, D.σ_ε, D.σ_alg]; ring
  rw [e1, e2, e3, e4, D.σ_sub_mul, D.σ_add_mul]
  simp

theorem Xmat_mul_Hs (v : Vm 3 F) :
    D.Xmat v * D.Hs (D.Xmat v) = quadMinus 3 F b c v • (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [Hs_Xmat, Xmat, skew6_mul_skew6, ← algebraMap_smul K (quadMinus 3 F b c v)]
  congr 1
  rw [quadMinus_three_apply]
  simp only [pf6, map_add, map_mul, map_pow]
  have h1 := D.δ_mul_ε
  have h2 := D.ω_sq
  linear_combination (algebraMap F K (v (.inl iO)) * algebraMap F K (v (.inr (.inl iO)))) * h1 -
    (algebraMap F K (v (.inr (.inr 1)))) ^ 2 * h2

theorem Hs_Xmat_mul (v : Vm 3 F) :
    D.Hs (D.Xmat v) * D.Xmat v = quadMinus 3 F b c v • (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [Hs_Xmat, Xmat, skew6_mul_skew6', ← algebraMap_smul K (quadMinus 3 F b c v)]
  congr 1
  rw [quadMinus_three_apply]
  simp only [pf6, map_add, map_mul, map_pow]
  have h1 := D.δ_mul_ε
  have h2 := D.ω_sq
  linear_combination (algebraMap F K (v (.inl iO)) * algebraMap F K (v (.inr (.inl iO)))) * h1 -
    (algebraMap F K (v (.inr (.inr 1)))) ^ 2 * h2

@[expose] noncomputable def bilinX :
    Vm 3 F →ₗ[F] Vm 3 F →ₗ[F] Matrix (Fin 4) (Fin 4) K :=
  (LinearMap.mul F (Matrix (Fin 4) (Fin 4) K)).compl₁₂ D.Xlin (D.HsLin ∘ₗ D.Xlin)

theorem bilinX_apply (v w : Vm 3 F) : D.bilinX v w = D.Xmat v * D.Hs (D.Xmat w) := rfl

@[expose] noncomputable def evenHom : EvenHom (quadMinus 3 F b c) (Matrix (Fin 4) (Fin 4) K) where
  bilin := D.bilinX
  contract m := by
    rw [bilinX_apply, Xmat_mul_Hs, Algebra.algebraMap_eq_smul_one]
  contract_mid m₁ m₂ m₃ := by
    simp only [bilinX_apply]
    calc D.Xmat m₁ * D.Hs (D.Xmat m₂) * (D.Xmat m₂ * D.Hs (D.Xmat m₃))
        = D.Xmat m₁ * (D.Hs (D.Xmat m₂) * D.Xmat m₂) * D.Hs (D.Xmat m₃) := by
          simp only [Matrix.mul_assoc]
      _ = quadMinus 3 F b c m₂ • (D.Xmat m₁ * D.Hs (D.Xmat m₃)) := by
          rw [Hs_Xmat_mul]
          simp

@[expose] noncomputable def PhiAlg :
    CliffordAlgebra.even (quadMinus 3 F b c) →ₐ[F] Matrix (Fin 4) (Fin 4) K :=
  CliffordAlgebra.even.lift (quadMinus 3 F b c) D.evenHom

theorem PhiAlg_ι (m₁ m₂ : Vm 3 F) :
    D.PhiAlg ((CliffordAlgebra.even.ι (quadMinus 3 F b c)).bilin m₁ m₂) =
      D.Xmat m₁ * D.Hs (D.Xmat m₂) :=
  CliffordAlgebra.even.lift_ι (quadMinus 3 F b c) D.evenHom m₁ m₂

@[expose] noncomputable def PhiMon : spinGroup (quadMinus 3 F b c) →* Matrix (Fin 4) (Fin 4) K where
  toFun s := D.PhiAlg ⟨(s : CliffordAlgebra (quadMinus 3 F b c)), spinGroup.mem_even s.2⟩
  map_one' := by
    have h : (⟨((1 : spinGroup (quadMinus 3 F b c)) : CliffordAlgebra (quadMinus 3 F b c)),
        spinGroup.mem_even (1 : spinGroup (quadMinus 3 F b c)).2⟩ :
        CliffordAlgebra.even (quadMinus 3 F b c)) = 1 := Subtype.ext rfl
    rw [h, map_one]
  map_mul' s t := by
    have h : (⟨((s * t : spinGroup (quadMinus 3 F b c)) : CliffordAlgebra (quadMinus 3 F b c)),
        spinGroup.mem_even (s * t : spinGroup (quadMinus 3 F b c)).2⟩ :
        CliffordAlgebra.even (quadMinus 3 F b c)) =
        ⟨(s : CliffordAlgebra (quadMinus 3 F b c)), spinGroup.mem_even s.2⟩ *
          ⟨(t : CliffordAlgebra (quadMinus 3 F b c)), spinGroup.mem_even t.2⟩ := Subtype.ext rfl
    rw [h, map_mul]

theorem PhiMon_apply (s : spinGroup (quadMinus 3 F b c)) :
    D.PhiMon s = D.PhiAlg ⟨(s : CliffordAlgebra (quadMinus 3 F b c)), spinGroup.mem_even s.2⟩ :=
  rfl

@[expose] def rv : (Fin 4 → K) →ₗ[F] (Fin 4 → K) where
  toFun x := fun j => σ₀ (x (Fin.rev j))
  map_add' x y := by
    ext j
    simp
  map_smul' r x := by
    ext j
    simp [Algebra.smul_def, D.σ_alg]

theorem rv_apply (x : Fin 4 → K) (j : Fin 4) : D.rv x j = σ₀ (x (Fin.rev j)) := rfl

theorem rv_rv (x : Fin 4 → K) : D.rv (D.rv x) = x := by
  ext j
  simp [rv_apply, D.σσ]

@[expose] noncomputable def gam (v : Vm 3 F) : Module.End F (Fin 4 → K) :=
  (Matrix.mulVecLin (D.Xmat v)).restrictScalars F ∘ₗ D.rv

theorem gam_apply (v : Vm 3 F) (x : Fin 4 → K) : D.gam v x = D.Xmat v *ᵥ D.rv x := rfl

theorem gam_gam (v w : Vm 3 F) (x : Fin 4 → K) :
    D.gam v (D.gam w x) = (D.Xmat v * D.Hs (D.Xmat w)) *ᵥ x := by
  have h : D.rv (D.Xmat w *ᵥ D.rv x) = D.Hs (D.Xmat w) *ᵥ D.rv (D.rv x) := by
    ext i
    rw [rv_apply, D.Hs_mulVec]
    rfl
  rw [gam_apply, gam_apply, h, rv_rv, Matrix.mulVec_mulVec]

@[expose] noncomputable def gamLin : Vm 3 F →ₗ[F] Module.End F (Fin 4 → K) where
  toFun := D.gam
  map_add' v w := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.add_apply, gam_apply, gam_apply, gam_apply, ← Xlin_apply, ← Xlin_apply,
      ← Xlin_apply, map_add, Matrix.add_mulVec]
  map_smul' r v := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.smul_apply, gam_apply, gam_apply, ← Xlin_apply, ← Xlin_apply, map_smul]
    funext j
    simp [Matrix.mulVec, dotProduct, Finset.smul_sum]

theorem gamLin_apply (v : Vm 3 F) : D.gamLin v = D.gam v := rfl

theorem gam_sq (v : Vm 3 F) :
    D.gamLin v * D.gamLin v = algebraMap F (Module.End F (Fin 4 → K)) (quadMinus 3 F b c v) := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, gamLin_apply, gam_gam, Xmat_mul_Hs, Module.algebraMap_end_apply]
  funext j
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

@[expose] noncomputable def Psi :
    CliffordAlgebra (quadMinus 3 F b c) →ₐ[F] Module.End F (Fin 4 → K) :=
  CliffordAlgebra.lift (quadMinus 3 F b c)
    (⟨D.gamLin, D.gam_sq⟩ : {f : Vm 3 F →ₗ[F] Module.End F (Fin 4 → K) //
      ∀ m, f m * f m = algebraMap F (Module.End F (Fin 4 → K)) (quadMinus 3 F b c m)})

theorem Psi_ι (v : Vm 3 F) : D.Psi (ι (quadMinus 3 F b c) v) = D.gam v := by
  unfold Psi
  rw [CliffordAlgebra.lift_ι_apply]
  rfl

theorem Psi_even (s : CliffordAlgebra (quadMinus 3 F b c))
    (hs : s ∈ CliffordAlgebra.evenOdd (quadMinus 3 F b c) 0) (x : Fin 4 → K) :
    D.Psi s x = D.PhiAlg ⟨s, hs⟩ *ᵥ x := by
  induction s, hs using CliffordAlgebra.evenOdd_induction generalizing x with
  | range_ι_pow v h =>
    have h1 : v ∈ (1 : Submodule F (CliffordAlgebra (quadMinus 3 F b c))) := by
      simpa using h
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp h1
    have h2 : (⟨algebraMap F (CliffordAlgebra (quadMinus 3 F b c)) r, _⟩ :
        CliffordAlgebra.even (quadMinus 3 F b c)) =
        algebraMap F (CliffordAlgebra.even (quadMinus 3 F b c)) r := Subtype.ext rfl
    rw [h2, AlgHom.commutes, AlgHom.commutes]
    ext j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  | add y z hy hz ihy ihz =>
    have h2 : (⟨y + z, Submodule.add_mem _ hy hz⟩ : CliffordAlgebra.even (quadMinus 3 F b c)) =
        ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
    rw [h2, map_add, map_add, LinearMap.add_apply, Matrix.add_mulVec, ihy, ihz]
  | ι_mul_ι_mul m₁ m₂ y hy ih =>
    have h2 : (⟨ι (quadMinus 3 F b c) m₁ * ι (quadMinus 3 F b c) m₂ * y, _⟩ :
        CliffordAlgebra.even (quadMinus 3 F b c)) =
        (CliffordAlgebra.even.ι (quadMinus 3 F b c)).bilin m₁ m₂ * ⟨y, hy⟩ := Subtype.ext rfl
    rw [h2, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ih,
      Psi_ι, Psi_ι, gam_gam, PhiAlg_ι, Matrix.mulVec_mulVec]

theorem Psi_spin (s : spinGroup (quadMinus 3 F b c)) (x : Fin 4 → K) :
    D.Psi (s : CliffordAlgebra (quadMinus 3 F b c)) x = D.PhiMon s *ᵥ x :=
  D.Psi_even _ _ x

end KleinData

end CFSG.ClassicalInvolution.WeakCT.SU4
