module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutMono

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def ffMat (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) :
    Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.of fun i j => if i = σ j then (if j ∈ K then -1 else 1) else 0

@[expose] def ffH : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 0, 1, 0, 0, 0;
     0, 1, 0, 1, 0, 0;
     1, 0, -1, 0, 0, 0;
     0, 1, 0, -1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, -1]

theorem ffH_mul_self : ffH * ffH = -1 := by
  decide +kernel

theorem ffH_sum_sq (w : Fin 6 → ZMod 3) :
    ∑ i, (ffH.mulVec w i) ^ 2 = -∑ i, (w i) ^ 2 := by
  revert w
  decide +kernel

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def ffX0Lin (fr : NFrame Q (Fin 6) 1) : V →ₗ[ZMod 3] V :=
  Matrix.toLin fr.b fr.b ffH

theorem ffX0Lin_apply_apply (fr : NFrame Q (Fin 6) 1) (v : V) :
    ffX0Lin fr (ffX0Lin fr v) = -v := by
  have h : (ffX0Lin fr).comp (ffX0Lin fr) = -LinearMap.id := by
    unfold ffX0Lin
    rw [← Matrix.toLin_mul, ffH_mul_self, map_neg, Matrix.toLin_one]
  simpa using LinearMap.congr_fun h v

private theorem ffOutSimDef_repr (fr : NFrame Q (Fin 6) 1) (v : V) :
    ⇑(fr.b.repr (ffX0Lin fr v)) = ffH.mulVec ⇑(fr.b.repr v) := by
  have h := LinearMap.toMatrix_mulVec_repr fr.b fr.b (ffX0Lin fr) v
  simp only [ffX0Lin, LinearMap.toMatrix_toLin] at h
  exact h.symm

@[expose] noncomputable def ffX0E (fr : NFrame Q (Fin 6) 1) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofLinear (ffX0Lin fr) (-ffX0Lin fr)
    (LinearMap.ext fun v => by simp [ffX0Lin_apply_apply])
    (LinearMap.ext fun v => by simp [ffX0Lin_apply_apply])

theorem ffX0E_apply (fr : NFrame Q (Fin 6) 1) (v : V) : ffX0E fr v = ffX0Lin fr v :=
  rfl

theorem ffX0E_isSimilitude (fr : NFrame Q (Fin 6) 1) : IsSimilitude Q (ffX0E fr) (-1) := by
  intro v
  rw [ffX0E_apply, fr.map_eq (ffX0Lin fr v), fr.map_eq v, ffOutSimDef_repr fr v,
    ffH_sum_sq]
  simp

@[expose] noncomputable def ffX0S (fr : NFrame Q (Fin 6) 1) : simGroup Q :=
  ⟨ffX0E fr, ⟨-1, ffX0E_isSimilitude fr⟩⟩

@[expose] noncomputable def ffX0 (fr : NFrame Q (Fin 6) 1) : ProjSim Q :=
  QuotientGroup.mk (ffX0S fr)

theorem ffX0_mul_self (fr : NFrame Q (Fin 6) 1) : ffX0 fr * ffX0 fr = 1 := by
  rw [ffX0, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  refine mem_piSim_iff.mpr (Or.inr ?_)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change ffX0Lin fr (ffX0Lin fr v) = (piOrth Q : V ≃ₗ[ZMod 3] V) v
  rw [ffX0Lin_apply_apply, coe_piOrth_apply]

theorem ffX0_inv (fr : NFrame Q (Fin 6) 1) : (ffX0 fr)⁻¹ = ffX0 fr :=
  inv_eq_of_mul_eq_one_right (ffX0_mul_self fr)

theorem ffX0_not_simInGStar (fr : NFrame Q (Fin 6) 1) : ¬ SimInGStar (ffX0 fr) := by
  rintro ⟨y, hy⟩
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  rw [projOrthToProjSim_toProj] at hy
  have hmem : (orthToSim Q t)⁻¹ * ffX0S fr ∈ piSim Q :=
    QuotientGroup.eq.mp (show (QuotientGroup.mk (orthToSim Q t) : ProjSim Q) =
      QuotientGroup.mk (ffX0S fr) from hy)
  have hcase : ffX0S fr = orthToSim Q t ∨ ffX0S fr = orthToSim Q t * orthToSim Q (piOrth Q) := by
    rcases mem_piSim_iff.mp hmem with h | h
    · exact Or.inl (inv_mul_eq_one.mp h).symm
    · exact Or.inr (eq_mul_of_inv_mul_eq h)
  have hq : Q ((ffX0S fr : V ≃ₗ[ZMod 3] V) (fr.b 0)) = Q (fr.b 0) := by
    rcases hcase with h | h
    · rw [h]
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup t.2 _
    · rw [h]
      change Q ((t : V ≃ₗ[ZMod 3] V) ((piOrth Q : V ≃ₗ[ZMod 3] V) (fr.b 0))) = Q (fr.b 0)
      rw [coe_piOrth_apply, map_neg, QuadraticMap.map_neg]
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup t.2 _
  have hs := ffX0E_isSimilitude fr (fr.b 0)
  rw [fr.norm 0] at hs
  change Q (ffX0E fr (fr.b 0)) = _ at hq
  rw [hs, fr.norm 0] at hq
  exact (by decide : ((-1 : (ZMod 3)ˣ) : ZMod 3) * 1 ≠ 1) hq

theorem ffToMatrix_mono (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6))
    (K : Finset (Fin 6)) :
    LinearMap.toMatrix fr.b fr.b
        (((fr.permOrth σ * fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) =
      ffMat σ K := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, ffMono_basis fr σ K j]
  by_cases hi : i = σ j <;> by_cases hj : j ∈ K <;>
    simp [ffMat, hi, hj, Module.Basis.repr_self, Finsupp.single_apply]

private theorem ffOutSimDef_mk_eq {a b : simGroup Q}
    (h : a = b ∨ a = orthToSim Q (piOrth Q) * b) :
    (QuotientGroup.mk a : ProjSim Q) = QuotientGroup.mk b := by
  rcases h with rfl | rfl
  · rfl
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (orthToSim Q (piOrth Q))).mpr
      (mem_piSim_iff.mpr (Or.inr rfl)), one_mul]

theorem ffX0_conj_of_mat (fr : NFrame Q (Fin 6) 1) {σ τ : Equiv.Perm (Fin 6)}
    {K J : Finset (Fin 6)}
    (h : ffH * ffMat σ K = ffMat τ J * ffH ∨ ffH * ffMat σ K = -(ffMat τ J * ffH)) :
    ffX0 fr * ffM fr σ K = ffM fr τ J * ffX0 fr := by
  have hX : LinearMap.toMatrix fr.b fr.b (ffX0Lin fr) = ffH := by
    simp only [ffX0Lin, LinearMap.toMatrix_toLin]
  have h1 : LinearMap.toMatrix fr.b fr.b ((ffX0Lin fr).comp
      (((fr.permOrth σ * fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V)) =
        ffH * ffMat σ K := by
    rw [LinearMap.toMatrix_comp fr.b fr.b fr.b, hX, ffToMatrix_mono]
  have h2 : LinearMap.toMatrix fr.b fr.b
      ((((fr.permOrth τ * fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).comp
        (ffX0Lin fr)) = ffMat τ J * ffH := by
    rw [LinearMap.toMatrix_comp fr.b fr.b fr.b, hX, ffToMatrix_mono]
  unfold ffX0 ffM
  simp only [projOrthToProjSim_toProj, ← QuotientGroup.mk_mul]
  apply ffOutSimDef_mk_eq
  rcases h with h | h
  · refine Or.inl ?_
    have hlin := (LinearMap.toMatrix fr.b fr.b).injective (h1.trans (h.trans h2.symm))
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun hlin v
  · refine Or.inr ?_
    have hlin := (LinearMap.toMatrix fr.b fr.b).injective
      (show LinearMap.toMatrix fr.b fr.b ((ffX0Lin fr).comp
          (((fr.permOrth σ * fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) :
            V →ₗ[ZMod 3] V)) = LinearMap.toMatrix fr.b fr.b (-((((fr.permOrth τ *
              fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).comp
                (ffX0Lin fr))) by rw [h1, map_neg, h2, h])
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv := LinearMap.congr_fun hlin v
    change ffX0Lin fr (((fr.permOrth σ * fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) v) =
      (piOrth Q : V ≃ₗ[ZMod 3] V)
        (((fr.permOrth τ * fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) (ffX0Lin fr v))
    rw [coe_piOrth_apply]
    simpa using hv

end CFSG.OddStandard.SmallF3.Omega
