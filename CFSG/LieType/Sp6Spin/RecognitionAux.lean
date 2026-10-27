module

public import CFSG.LieType.Sp6Spin.Frame
public import CFSG.LieType.Sp6Spin.FrameModel

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.LieType.TorusWeights CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank
  TauCeti.GLSymplecticFin QuadraticMap CFSG.StandardType CFSG.StandardType.Triality
  CFSG.LieType.D4Small CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

namespace SpinSetting

variable {S : SpinSetting K V}

private abbrev spinMat (M : spinSeven K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K :=
  ((M : Om8 K) : GL (Fin (2 * 4)) K)

private theorem spinMat_mul (M N : spinSeven K) :
    spinMat (M * N) = spinMat M * spinMat N :=
  rfl

private theorem spinMat_one : spinMat (1 : spinSeven K) = 1 :=
  rfl

private theorem spinMat_mk {A : Om8 K} (h : A ∈ spinSeven K) :
    spinMat (⟨A, h⟩ : spinSeven K) =
      ((A : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) :=
  rfl

private theorem mulVec_eq_of_frame {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
    (g : StatedSp 3 K) (h : ∀ σ, A *ᵥ e (Fr.v σ) = e (S.ψ g (Fr.v σ))) :
    ∀ v, A *ᵥ e v = e (S.ψ g v) := by
  have hlin : A.mulVecLin.comp e.toLinearMap = e.toLinearMap.comp (S.ψ g).toLinearMap := by
    refine LinearMap.ext_on_range (span_eq_top_of_frame S.finrank_eq S.Q Fr.v Fr.polar_eq) ?_
    intro σ
    simpa using h σ
  intro v
  simpa using LinearMap.congr_fun hlin v

private theorem exists_short_mem {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (hev : ∀ σ, e (Fr.v σ) = pv K σ)
    (r : RootSubgroupIndex 3) (hr : IsShortIndex r) (c : K) :
    ∃ M : spinSeven K, ∀ v, spinMat M *ᵥ e v = e (S.ψ (elt r c) v) := by
  obtain ⟨lam, hlam⟩ := Fr.short_eq r hr
  obtain ⟨γ, hγmem, hγ⟩ := exists_X8_short (K := K) r hr
  refine ⟨⟨X8 γ (c ^ 2 ^ R.l * lam), hγmem _⟩, ?_⟩
  refine mulVec_eq_of_frame Fr e _ _ fun σ => ?_
  rw [spinMat_mk, hev σ, hγ _ σ, R.short_apply r hr c (Fr.v σ), map_add, map_smul, hev σ]
  by_cases hs : IsSrc (stdVec r) σ
  · rw [if_pos hs, hlam σ, if_pos hs, map_smul, hev (flipAt (stdVec r) σ), mul_smul]
  · rw [if_neg hs, hlam σ, if_neg hs, map_zero, smul_zero, add_zero]

private theorem exists_long_mem {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (hev : ∀ σ, e (Fr.v σ) = pv K σ) (c : K) :
    ∃ M : spinSeven K,
      ∀ v, spinMat M *ᵥ e v = e (S.ψ (elt (n := 3) (.positiveLong 2) c) v) := by
  refine ⟨⟨theta (Y (c ^ 2 ^ R.l')), theta_Y_mem _⟩, ?_⟩
  refine mulVec_eq_of_frame Fr e _ _ fun σ => ?_
  rw [spinMat_mk, hev σ, theta_Y_mulVec, R.long_apply c (Fr.v σ), map_add, map_smul, hev σ]
  by_cases hs : σ 2 = false
  · rw [if_pos hs, Fr.long_eq σ hs, hev (Function.update σ 2 true)]
  · have h2 : σ 2 = true := by revert hs; cases σ 2 <;> simp
    rw [if_neg hs, R.long_not_src σ h2 (Fr.v σ) (Fr.mem σ), map_zero, smul_zero, add_zero]

private noncomputable def spinImage (e : V ≃ₗ[K] (Fin (2 * 4) → K)) :
    Subgroup (StatedSp 3 K) where
  carrier := {g | ∃ M : spinSeven K, ∀ v, spinMat M *ᵥ e v = e (S.ψ g v)}
  one_mem' := by
    refine ⟨1, fun v => ?_⟩
    rw [spinMat_one, Matrix.one_mulVec]
    simp
  mul_mem' := by
    rintro a b ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨M * N, fun v => ?_⟩
    rw [spinMat_mul, ← Matrix.mulVec_mulVec, hN v, hM (S.ψ b v)]
    simp
  inv_mem' := by
    rintro a ⟨M, hM⟩
    refine ⟨M⁻¹, fun v => ?_⟩
    obtain ⟨w, rfl⟩ := (S.ψ a).surjective v
    have hcancel : spinMat M⁻¹ * spinMat M = 1 := by
      rw [← spinMat_mul, inv_mul_cancel, spinMat_one]
    have hcomp : S.ψ a⁻¹ (S.ψ a w) = w := by simp
    calc spinMat M⁻¹ *ᵥ e (S.ψ a w)
        = spinMat M⁻¹ *ᵥ (spinMat M *ᵥ e w) := by rw [← hM w]
      _ = (spinMat M⁻¹ * spinMat M) *ᵥ e w := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e w := by rw [hcancel]
      _ = e w := by rw [Matrix.one_mulVec]
      _ = e (S.ψ a⁻¹ (S.ψ a w)) := by rw [hcomp]

private theorem spinImage_eq_top {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (hev : ∀ σ, e (Fr.v σ) = pv K σ) :
    spinImage (S := S) e = ⊤ := by
  rw [eq_top_iff, ← closure_short_long_eq_top (K := K), Subgroup.closure_le]
  rintro g (⟨r, hr, c, rfl⟩ | ⟨c, rfl⟩)
  · exact exists_short_mem Fr e hev r hr c
  · exact exists_long_mem Fr e hev c

private theorem exists_spinMat {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (hev : ∀ σ, e (Fr.v σ) = pv K σ)
    (g : StatedSp 3 K) :
    ∃ M : spinSeven K, ∀ v, spinMat M *ᵥ e v = e (S.ψ g v) := by
  have hg : g ∈ spinImage (S := S) e := by
    rw [spinImage_eq_top Fr e hev]
    exact Subgroup.mem_top g
  exact hg

private theorem spinMat_unique (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (g : StatedSp 3 K)
    {M M' : spinSeven K} (hM : ∀ v, spinMat M *ᵥ e v = e (S.ψ g v))
    (hM' : ∀ v, spinMat M' *ᵥ e v = e (S.ψ g v)) : M = M' := by
  have hmat : spinMat M = spinMat M' := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    obtain ⟨w, hw⟩ := e.surjective (Pi.single i 1)
    rw [← hw, hM w, hM' w]
  exact Subtype.ext (Subtype.ext (Units.ext hmat))

private noncomputable def spinHom {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (hev : ∀ σ, e (Fr.v σ) = pv K σ) :
    StatedSp 3 K →* spinSeven K where
  toFun g := Classical.choose (exists_spinMat Fr e hev g)
  map_one' := spinMat_unique e 1 (Classical.choose_spec (exists_spinMat Fr e hev 1)) (by
    intro v
    rw [spinMat_one, Matrix.one_mulVec]
    simp)
  map_mul' g h :=
    spinMat_unique e (g * h) (Classical.choose_spec (exists_spinMat Fr e hev (g * h))) (by
      intro v
      rw [spinMat_mul, ← Matrix.mulVec_mulVec,
        Classical.choose_spec (exists_spinMat Fr e hev h) v,
        Classical.choose_spec (exists_spinMat Fr e hev g) (S.ψ h v)]
      simp)

private theorem spinHom_apply {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (hev : ∀ σ, e (Fr.v σ) = pv K σ)
    (g : StatedSp 3 K) :
    ∀ v, spinMat (spinHom Fr e hev g) *ᵥ e v = e (S.ψ g v) :=
  Classical.choose_spec (exists_spinMat Fr e hev g)

private theorem spinHom_injective {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (hev : ∀ σ, e (Fr.v σ) = pv K σ) :
    Function.Injective (spinHom (S := S) Fr e hev) := by
  intro g h hgh
  have hMv : ∀ v, e (S.ψ g v) = e (S.ψ h v) := by
    intro v
    rw [← spinHom_apply Fr e hev g v, ← spinHom_apply Fr e hev h v, hgh]
  exact S.ψ_injective (LinearEquiv.ext fun v => e.injective (hMv v))

private theorem spinHom_bijective {R : S.SpinRoots} (Fr : SpinFrame R)
    (e : V ≃ₗ[K] (Fin (2 * 4) → K)) (hev : ∀ σ, e (Fr.v σ) = pv K σ) :
    Function.Bijective (spinHom (S := S) Fr e hev) :=
  (spinHom_injective Fr e hev).bijective_of_nat_card_le
    (le_of_eq (natCard_spinSeven (K := K)))

theorem exists_spinEquiv :
    ∃ e : V ≃ₗ[K] (Fin (2 * 4) → K), (∀ v, coordinateQuadPlus 4 K (e v) = S.Q v) ∧
      (∀ g : StatedSp 3 K, ∃ M ∈ spinSeven K, ∀ v,
        ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v =
          e (S.ψ g v)) ∧
      ∀ M ∈ spinSeven K, ∃ g : StatedSp 3 K, ∀ v,
        ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ e v =
          e (S.ψ g v) := by
  obtain ⟨x, hP⟩ := S.exists_isSpinPattern
  obtain ⟨R⟩ := S.nonempty_spinRoots hP
  obtain ⟨Fr⟩ := R.nonempty_spinFrame
  obtain ⟨e, hev, heQ⟩ := exists_isometry_of_frame S.finrank_eq S.Q Fr.v Fr.Q_eq Fr.polar_eq
  refine ⟨e, heQ, ?_, ?_⟩
  · intro g
    obtain ⟨M, hM⟩ := exists_spinMat Fr e hev g
    exact ⟨(M : Om8 K), M.2, hM⟩
  · intro M hM
    obtain ⟨g, hg⟩ := (spinHom_bijective Fr e hev).2 ⟨M, hM⟩
    have hval : ((spinHom Fr e hev g : spinSeven K) : Om8 K) = M := congrArg Subtype.val hg
    refine ⟨g, fun v => ?_⟩
    rw [← hval]
    exact spinHom_apply Fr e hev g v

end SpinSetting

end CFSG.LieType.Sp6Spin

end
