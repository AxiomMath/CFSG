module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankD
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankFix
public import CFSG.ClassicalGroups.Unitary.PerpQuotient
public import CFSG.Quasithin.Background.F918Z3CbHerm
public import CFSG.CGT.PushingUpLit.A78.NoSU4

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LocalAnalysis.RankThreeUC CFSG.ClassicalGroups.Unitary
open CFSG.Quasithin.OrthMinus (IsHerm Fx card_herm)

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem siegel_pairing_bijective
    (hσ : IsUnitaryInvolution σ) {W U : Submodule F (Fin 4 → F)}
    (hWmax : ∀ x, (∀ y ∈ W, herm σ x y = 0) → x ∈ W)
    (hW2 : Module.finrank F W = 2) (hcompl : IsCompl W U) :
    Function.Bijective (fun u : U => fun j : Fin 2 =>
      herm σ ((Module.finBasis F W).reindex (finCongr hW2) j : Fin 4 → F)
        (u : Fin 4 → F)) := by
  classical
  have hdimV : Module.finrank F (Fin 4 → F) = 4 := Module.finrank_fin_fun F
  have hdimU : Module.finrank F U = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (s := W) (t := U)
    rw [hcompl.sup_eq_top, hcompl.inf_eq_bot, finrank_top, finrank_bot, hdimV, hW2] at h
    omega
  let wb : Module.Basis (Fin 2) F W := (Module.finBasis F W).reindex (finCongr hW2)
  let phi : U →ₗ[F] (Fin 2 → F) :=
    { toFun := fun u j => herm σ (wb j : Fin 4 → F) (u : Fin 4 → F)
      map_add' := by intro u u'; funext j; simp
      map_smul' := by intro c u; funext j; simp }
  have hphi_inj : Function.Injective phi := by
    intro u u' h
    have h0 : phi (u - u') = 0 := by rw [map_sub, h, sub_self]
    have hzj : ∀ j, herm σ (wb j : Fin 4 → F) ((u - u' : U) : Fin 4 → F) = 0 := by
      intro j
      have hj : phi (u - u') j = 0 := by rw [h0]; rfl
      simpa [phi] using hj
    let Gm : W →ₗ[F] F :=
      { toFun := fun w => herm σ ((u - u' : U) : Fin 4 → F) (w : Fin 4 → F)
        map_add' := by intro a b; simp
        map_smul' := by intro c a; simp }
    have hGm : Gm = 0 := wb.ext (fun j => by
      show herm σ ((u - u' : U) : Fin 4 → F) (wb j : Fin 4 → F) = 0
      have hj := hzj j
      rw [herm_conj σ hσ.invol] at hj
      exact (map_eq_zero_iff σ σ.injective).mp hj)
    have hz : ∀ w : W, herm σ (w : Fin 4 → F) ((u - u' : U) : Fin 4 → F) = 0 := by
      intro w
      have h1 : herm σ ((u - u' : U) : Fin 4 → F) (w : Fin 4 → F) = 0 := by
        have := congrArg (fun f : W →ₗ[F] F => f w) hGm
        simpa [Gm] using this
      rw [herm_conj σ hσ.invol ((u - u' : U) : Fin 4 → F) w, h1, map_zero]
    have hz' : ∀ w ∈ W, herm σ ((u - u' : U) : Fin 4 → F) w = 0 := by
      intro w hw
      rw [herm_conj σ hσ.invol, hz ⟨w, hw⟩, map_zero]
    have hmem : ((u - u' : U) : Fin 4 → F) ∈ W := hWmax _ hz'
    have hbot : ((u - u' : U) : Fin 4 → F) ∈ (⊥ : Submodule F (Fin 4 → F)) := by
      rw [← hcompl.inf_eq_bot]
      exact Submodule.mem_inf.mpr ⟨hmem, (u - u').2⟩
    have hzero : ((u - u' : U) : Fin 4 → F) = 0 := by simpa using hbot
    exact sub_eq_zero.mp (Subtype.ext hzero)
  refine ⟨hphi_inj, ?_⟩
  have hdimDual : Module.finrank F (Fin 2 → F) = 2 := Module.finrank_fin_fun F
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [hdimU, hdimDual])).mp hphi_inj

noncomputable def siegelN {U W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W] (w : Fin 2 → W) (P : U →ₗ[F] (Fin 2 → F))
    (M : Matrix (Fin 2) (Fin 2) F) : U →ₗ[F] W :=
  (Fintype.linearCombination F w).comp ((Matrix.mulVecLin M).comp P)

theorem siegelN_apply {U W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W] (w : Fin 2 → W) (P : U →ₗ[F] (Fin 2 → F))
    (M : Matrix (Fin 2) (Fin 2) F) (u : U) :
    siegelN w P M u = ∑ i, (M *ᵥ P u) i • w i := by
  rw [siegelN, LinearMap.comp_apply, LinearMap.comp_apply, Fintype.linearCombination_apply,
    Matrix.mulVecLin_apply]

theorem siegelN_fb {U W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W] (w : Fin 2 → W) (P : U →ₗ[F] (Fin 2 → F))
    (M : Matrix (Fin 2) (Fin 2) F) {fb : Fin 2 → U} {j : Fin 2}
    (hP : P (fb j) = Pi.single j 1) :
    siegelN w P M (fb j) = ∑ i, M i j • w i := by
  rw [siegelN_apply, hP, Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

section Siegel

variable {W U : Submodule F (Fin 4 → F)}

theorem siegelN_herm_left {w : Fin 2 → W} {P : U ≃ₗ[F] (Fin 2 → F)}
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    (M : Matrix (Fin 2) (Fin 2) F) (u v : U) :
    herm σ ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u : W) : Fin 4 → F)
        (v : Fin 4 → F) =
      ∑ i, σ ((M *ᵥ P u) i) * P v i := by
  have hNu : ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u : W) : Fin 4 → F) =
      ∑ i, ((M *ᵥ P u) i) • (w i : Fin 4 → F) := by
    rw [siegelN_apply]
    simp
  rw [hNu, herm_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [herm_smul_left, hP v i]

theorem siegelN_herm_right (hσ : IsUnitaryInvolution σ) {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)}
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    (M : Matrix (Fin 2) (Fin 2) F) (u v : U) :
    herm σ (u : Fin 4 → F)
        ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v : W) : Fin 4 → F) =
      ∑ i, (M *ᵥ P v) i * σ (P u i) := by
  have hNv : ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v : W) : Fin 4 → F) =
      ∑ i, ((M *ᵥ P v) i) • (w i : Fin 4 → F) := by
    rw [siegelN_apply]
    simp
  rw [hNv, herm_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [herm_smul_right, herm_conj σ hσ.invol (w i : Fin 4 → F) (u : Fin 4 → F), hP u i]

theorem siegelN_herm_add [CharP F 2] (hσ : IsUnitaryInvolution σ) {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)}
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    {M : Matrix (Fin 2) (Fin 2) F} (hM : IsHerm (σ : F →+* F) M) (u v : U) :
    herm σ ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u : W) : Fin 4 → F)
        (v : Fin 4 → F) +
      herm σ (u : Fin 4 → F)
        ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v : W) : Fin 4 → F) = 0 := by
  have hMu : ∀ i, (M *ᵥ P u) i = ∑ j, M i j * P u j := by
    intro i
    rw [Matrix.mulVec_apply]
    rfl
  have hMv : ∀ i, (M *ᵥ P v) i = ∑ j, M i j * P v j := by
    intro i
    rw [Matrix.mulVec_apply]
    rfl
  have h1a : (∑ i, σ ((M *ᵥ P u) i) * P v i) =
      ∑ i, ∑ j, σ (M i j) * σ (P u j) * P v i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hMu i, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
  have h1b : (∑ i, ∑ j, σ (M i j) * σ (P u j) * P v i) =
      ∑ i, ∑ j, M i j * σ (P u i) * P v j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show σ (M b a) = M a b from hM.apply a b]
  have h2 : (∑ i, (M *ᵥ P v) i * σ (P u i)) =
      ∑ i, ∑ j, M i j * P v j * σ (P u i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hMv i, Finset.sum_mul]
  have hEq : (∑ i, ∑ j, M i j * P v j * σ (P u i)) =
      ∑ i, ∑ j, M i j * σ (P u i) * P v j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [siegelN_herm_left hP M u v, siegelN_herm_right hσ hP M u v, h1a, h1b, h2, hEq]
  exact CharTwo.add_self_eq_zero _

noncomputable def siegelT (hcompl : IsCompl W U) (w : Fin 2 → W)
    (P : U ≃ₗ[F] (Fin 2 → F)) (M : Matrix (Fin 2) (Fin 2) F) :
    (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
  LinearMap.id + W.subtype.comp
    ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M).comp (U.projectionOnto W hcompl.symm))

theorem siegelT_apply {hcompl : IsCompl W U} {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)} {M : Matrix (Fin 2) (Fin 2) F} (x : Fin 4 → F) :
    siegelT hcompl w P M x =
      x + ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M (U.projectionOnto W hcompl.symm x) : W) :
        Fin 4 → F) := by
  simp [siegelT]

theorem siegelT_fixes_W {hcompl : IsCompl W U} {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)} {M : Matrix (Fin 2) (Fin 2) F} (x : W) :
    siegelT hcompl w P M (x : Fin 4 → F) = (x : Fin 4 → F) := by
  rw [siegelT_apply, Submodule.projectionOnto_apply_right]
  simp

theorem siegelT_proj {hcompl : IsCompl W U} {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)} {M : Matrix (Fin 2) (Fin 2) F} (x : Fin 4 → F) :
    U.projectionOnto W hcompl.symm (siegelT hcompl w P M x) =
      U.projectionOnto W hcompl.symm x := by
  rw [siegelT_apply, map_add]
  have hz : U.projectionOnto W hcompl.symm
      ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M (U.projectionOnto W hcompl.symm x) : W) :
        Fin 4 → F) = 0 :=
    Submodule.projectionOnto_apply_right hcompl.symm
      (siegelN w (P : U →ₗ[F] (Fin 2 → F)) M (U.projectionOnto W hcompl.symm x))
  rw [hz, add_zero]

theorem siegelT_comp_self [CharP F 2] {hcompl : IsCompl W U} {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)} {M : Matrix (Fin 2) (Fin 2) F} :
    (siegelT hcompl w P M).comp (siegelT hcompl w P M) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, siegelT_apply, siegelT_proj, siegelT_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rfl

theorem siegelT_apply_fb {hcompl : IsCompl W U} {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)} {M : Matrix (Fin 2) (Fin 2) F} (fb : Fin 2 → U)
    (j : Fin 2) :
    siegelT hcompl w P M (fb j : Fin 4 → F) =
      (fb j : Fin 4 → F) +
        ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M (fb j) : W) : Fin 4 → F) := by
  rw [siegelT_apply, Submodule.projectionOnto_apply_left]

theorem siegelT_isometry [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {hcompl : IsCompl W U} {w : Fin 2 → W} {P : U ≃ₗ[F] (Fin 2 → F)}
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    {M : Matrix (Fin 2) (Fin 2) F} (hM : IsHerm (σ : F →+* F) M)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) (x y : Fin 4 → F) :
    herm σ (siegelT hcompl w P M x) (siegelT hcompl w P M y) = herm σ x y := by
  classical
  set u : U := U.projectionOnto W hcompl.symm x with hu
  set v : U := U.projectionOnto W hcompl.symm y with hv
  have hxu : x - (u : Fin 4 → F) ∈ W := by
    simpa [hu] using Submodule.sub_projection_mem hcompl.symm x
  have hyv : y - (v : Fin 4 → F) ∈ W := by
    simpa [hv] using Submodule.sub_projection_mem hcompl.symm y
  have hNu : ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u : W) : Fin 4 → F) ∈ W :=
    (siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u).2
  have hNv : ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v : W) : Fin 4 → F) ∈ W :=
    (siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v).2
  have hx : x = (x - (u : Fin 4 → F)) + (u : Fin 4 → F) := by abel
  have hy : y = (y - (v : Fin 4 → F)) + (v : Fin 4 → F) := by abel
  have h1 : herm σ x ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v : W) : Fin 4 → F) =
      herm σ (u : Fin 4 → F)
        ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v : W) : Fin 4 → F) := by
    conv_lhs => rw [hx]
    rw [herm_add_left, hWiso _ hxu _ hNv, zero_add]
  have h2 : herm σ ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u : W) : Fin 4 → F) y =
      herm σ ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u : W) : Fin 4 → F)
        (v : Fin 4 → F) := by
    conv_lhs => rw [hy]
    rw [herm_add_right, hWiso _ hNu _ hyv, zero_add]
  have h3 : herm σ ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u : W) : Fin 4 → F)
      ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v : W) : Fin 4 → F) = 0 :=
    hWiso _ hNu _ hNv
  have hzero : herm σ (u : Fin 4 → F)
        ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M v : W) : Fin 4 → F) +
      herm σ ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M u : W) : Fin 4 → F)
        (v : Fin 4 → F) = 0 := by
    rw [add_comm]
    exact siegelN_herm_add hσ hP hM u v
  rw [siegelT_apply, siegelT_apply, ← hu, ← hv]
  rw [herm_add_left, herm_add_right, herm_add_right]
  rw [h1, h2, h3, add_zero, add_assoc]
  rw [hzero, add_zero]

noncomputable def siegelMatrix (hcompl : IsCompl W U) (w : Fin 2 → W)
    (P : U ≃ₗ[F] (Fin 2 → F)) (M : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 4) (Fin 4) F :=
  LinearMap.toMatrix' (siegelT hcompl w P M)

theorem siegelMatrix_mul_self [CharP F 2] {hcompl : IsCompl W U} {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)} {M : Matrix (Fin 2) (Fin 2) F} :
    siegelMatrix hcompl w P M * siegelMatrix hcompl w P M = 1 := by
  rw [siegelMatrix, ← LinearMap.toMatrix'_comp, siegelT_comp_self, LinearMap.toMatrix'_id]

theorem siegelMatrix_det [CharP F 2] {hcompl : IsCompl W U} {w : Fin 2 → W}
    {P : U ≃ₗ[F] (Fin 2 → F)} {M : Matrix (Fin 2) (Fin 2) F} :
    (siegelMatrix hcompl w P M).det = 1 :=
  CFSG.CGT.PushingUpLit.A78.det_eq_one_of_mul_self (siegelMatrix_mul_self (M := M))

theorem siegelMatrix_isometry [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {hcompl : IsCompl W U} {w : Fin 2 → W} {P : U ≃ₗ[F] (Fin 2 → F)}
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    {M : Matrix (Fin 2) (Fin 2) F} (hM : IsHerm (σ : F →+* F) M)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) :
    ∀ x y, herm σ (siegelMatrix hcompl w P M *ᵥ x) (siegelMatrix hcompl w P M *ᵥ y) =
      herm σ x y := by
  intro x y
  rw [siegelMatrix, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact siegelT_isometry hσ hP hM hWiso x y

noncomputable def siegelSU [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (hcompl : IsCompl W U) (w : Fin 2 → W) (P : U ≃ₗ[F] (Fin 2 → F))
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    (M : Matrix (Fin 2) (Fin 2) F) (hM : IsHerm (σ : F →+* F) M)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) : SUid σ 4 :=
  mkSU σ (siegelMatrix hcompl w P M) siegelMatrix_det (siegelMatrix_isometry hσ hP hM hWiso)

theorem siegelSU_smul [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (hcompl : IsCompl W U) (w : Fin 2 → W) (P : U ≃ₗ[F] (Fin 2 → F))
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    (M : Matrix (Fin 2) (Fin 2) F) (hM : IsHerm (σ : F →+* F) M)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) (x : Fin 4 → F) :
    siegelSU hσ hcompl w P hP M hM hWiso • x = siegelT hcompl w P M x := by
  rw [siegelSU, mkSU_smul, siegelMatrix, LinearMap.toMatrix'_mulVec]

theorem siegelN_herm_fb (hσ : IsUnitaryInvolution σ) {w : Fin 2 → W}
    {P : U →ₗ[F] (Fin 2 → F)} {M : Matrix (Fin 2) (Fin 2) F} {fb : Fin 2 → U}
    (hPfb : ∀ j, P (fb j) = Pi.single j 1)
    (hpair : ∀ i j, herm σ (w i : Fin 4 → F) (fb j : Fin 4 → F) =
      if i = j then 1 else 0) (i j : Fin 2) :
    herm σ (fb i : Fin 4 → F) ((siegelN w P M (fb j) : W) : Fin 4 → F) = M i j := by
  have hN : ((siegelN w P M (fb j) : W) : Fin 4 → F) =
      ∑ k, M k j • (w k : Fin 4 → F) := by
    rw [siegelN_fb w P M (hPfb j)]
    simp
  rw [hN, herm_sum_right]
  rw [Finset.sum_eq_single i]
  · rw [herm_smul_right, herm_conj σ hσ.invol (w i : Fin 4 → F) (fb i : Fin 4 → F),
      hpair i i, if_pos rfl, map_one, mul_one]
  · intro k _ hk
    rw [herm_smul_right, herm_conj σ hσ.invol (w k : Fin 4 → F) (fb i : Fin 4 → F),
      hpair k i, if_neg hk, map_zero, mul_zero]
  · intro hi
    simp at hi

variable [Finite F]

theorem siegelSU_mem_PW [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (hcompl : IsCompl W U) (w : Fin 2 → W) (P : U ≃ₗ[F] (Fin 2 → F))
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    (M : Matrix (Fin 2) (Fin 2) F) (hM : IsHerm (σ : F →+* F) M)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) :
    siegelSU hσ hcompl w P hP M hM hWiso ∈ PW (σ := σ) W := by
  refine mem_PW.mpr ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [siegelSU_smul hσ hcompl w P hP M hM hWiso, siegelT_apply]
    have hx' : x + ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M
        (U.projectionOnto W hcompl.symm x) : W) : Fin 4 → F) - x =
        ((siegelN w (P : U →ₗ[F] (Fin 2 → F)) M (U.projectionOnto W hcompl.symm x) : W) :
          Fin 4 → F) := by abel
    rw [hx']
    exact (siegelN w (P : U →ₗ[F] (Fin 2 → F)) M (U.projectionOnto W hcompl.symm x)).2
  · rw [siegelSU_smul hσ hcompl w P hP M hM hWiso]
    exact siegelT_fixes_W (hcompl := hcompl) ⟨x, hx⟩

theorem siegelSU_injective [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {hcompl : IsCompl W U} {w : Fin 2 → W} {P : U ≃ₗ[F] (Fin 2 → F)}
    (hP : ∀ (u : U) (i : Fin 2), P u i = herm σ (w i : Fin 4 → F) (u : Fin 4 → F))
    {fb : Fin 2 → U} (hPfb : ∀ j, P (fb j) = Pi.single j 1)
    (hpair : ∀ i j, herm σ (w i : Fin 4 → F) (fb j : Fin 4 → F) =
      if i = j then 1 else 0)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) :
    Function.Injective (fun M : {M : Matrix (Fin 2) (Fin 2) F // IsHerm (σ : F →+* F) M} =>
      (⟨siegelSU hσ hcompl w P hP M.1 M.2 hWiso,
        siegelSU_mem_PW hσ hcompl w P hP M.1 M.2 hWiso⟩ : PW (σ := σ) W)) := by
  rintro ⟨M, hM⟩ ⟨M', hM'⟩ h
  have hsu : siegelSU hσ hcompl w P hP M hM hWiso =
      siegelSU hσ hcompl w P hP M' hM' hWiso :=
    congrArg Subtype.val h
  have hfun : ∀ j, siegelT hcompl w P M (fb j : Fin 4 → F) =
      siegelT hcompl w P M' (fb j : Fin 4 → F) := by
    intro j
    have h2 := congrArg (fun g : SUid σ 4 => g • (fb j : Fin 4 → F)) hsu
    rwa [siegelSU_smul hσ hcompl w P hP M hM hWiso,
      siegelSU_smul hσ hcompl w P hP M' hM' hWiso] at h2
  ext i j
  have hN : siegelN w P M (fb j) = siegelN w P M' (fb j) := by
    apply Subtype.ext
    have hT := hfun j
    rw [siegelT_apply_fb, siegelT_apply_fb] at hT
    exact add_left_cancel hT
  have hp := congrArg (fun z : W => herm σ (fb i : Fin 4 → F) (z : Fin 4 → F)) hN
  rwa [siegelN_herm_fb hσ hPfb hpair i j, siegelN_herm_fb hσ hPfb hpair i j] at hp

end Siegel

variable [Finite F]

theorem card_PW_eq_two_pow_four_mul (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) {W : Submodule F (Fin 4 → F)}
    (hW2 : Module.finrank F W = 2) (hWiso : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0)
    (hWmax : ∀ x, (∀ y ∈ W, herm σ x y = 0) → x ∈ W) :
    Nat.card ↥(PW (σ := σ) W) = 2 ^ (4 * n) := by
  classical
  have : CharP F 2 := charP_of_card_sq (p := 2) (f := n) hF
  have hn : 1 ≤ n := by
    by_contra hcon
    have h0 : n = 0 := by omega
    rw [h0] at hF
    simp at hF
    have hlt := Finite.one_lt_card (α := F)
    omega
  obtain ⟨U, hcompl⟩ := Submodule.exists_isCompl W
  let wb : Module.Basis (Fin 2) F W := (Module.finBasis F W).reindex (finCongr hW2)
  let P : U →ₗ[F] (Fin 2 → F) :=
    { toFun := fun u j => herm σ (wb j : Fin 4 → F) (u : Fin 4 → F)
      map_add' := by
        intro u u'
        funext j
        simp
      map_smul' := by
        intro c u
        funext j
        simp }
  have hPbij : Function.Bijective P := by
    simpa [P, wb] using siegel_pairing_bijective (hσ := hσ) (W := W) (U := U)
      hWmax hW2 hcompl
  let Pe : U ≃ₗ[F] (Fin 2 → F) := LinearEquiv.ofBijective P hPbij
  have hPe : ∀ (u : U) (j : Fin 2),
      Pe u j = herm σ (wb j : Fin 4 → F) (u : Fin 4 → F) := fun u j => rfl
  let fb : Fin 2 → U := fun j => Pe.symm (Pi.single j 1)
  have hPfb : ∀ j, Pe (fb j) = Pi.single j 1 := fun j => Pe.apply_symm_apply _
  have hpair : ∀ i j,
      herm σ (wb i : Fin 4 → F) (fb j : Fin 4 → F) = if i = j then 1 else 0 := by
    intro i j
    have h := (hPe (fb j) i).symm
    rw [hPfb j] at h
    simpa [Pi.single_apply, eq_comm] using h
  have hinj := siegelSU_injective (hσ := hσ) (hcompl := hcompl) (w := wb) (P := Pe)
    hPe (fb := fb) hPfb hpair hWiso
  have hq : Nat.card (Fx (σ : F →+* F)) = 2 ^ n := by
    have hFix := card_fixedField_mul_self hσ h2
    rw [hF, ← sq] at hFix
    exact Nat.pow_left_injective (by norm_num) hFix
  have hH := card_herm (σ := (σ : F →+* F)) hσ.invol
  rw [hq, hF] at hH
  have hge : 2 ^ (4 * n) ≤ Nat.card ↥(PW (σ := σ) W) := by
    calc 2 ^ (4 * n) = Nat.card {M : Matrix (Fin 2) (Fin 2) F // IsHerm (σ : F →+* F) M} := by
          rw [hH]; ring
      _ ≤ Nat.card ↥(PW (σ := σ) W) := Nat.card_le_card_of_injective _ hinj
  exact le_antisymm (card_le_two_pow_four hσ (fun g hg => PW_sq h2 hg)
    (fun g hg g' hg' => PW_comm hg hg') hn hF) hge

end CFSG.LieType.Universal.Unitary
