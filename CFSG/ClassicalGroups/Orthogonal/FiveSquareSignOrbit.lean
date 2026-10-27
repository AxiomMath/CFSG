module
public import CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
public import CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddOrthogonal

open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal
open CFSG.Quasithin
open QuadraticMap
open scoped commutatorElement

public section
namespace CFSG.ClassicalGroups.Orthogonal.FiveSquareSignOrbit
local instance instAddCommGroupV : AddCommGroup (Fin 5 → F) :=
  { Pi.addCommGroup with toAddCommMonoid := Pi.addCommMonoid }
abbrev G := ↥derived
@[expose]
noncomputable def frameSigns : Subgroup G :=
  (signChangeSubgroup stdFrame.e).subgroupOf derived
@[expose]
noncomputable def coordinateEight (i : Fin 5) : Subgroup G :=
  frameSigns ⊓ MulAction.stabilizer G (e i)
@[expose]
noncomputable def rankThreeOrbit : Set (Subgroup G) :=
  {A | ∃ g : G, A = CFSG.Quasithin.A1b.conjSub g (coordinateEight 4)}
private def diagMat : Matrix (Fin 2) (Fin 2) F := !![(-1 : F), 0; 0, 1]
private noncomputable def diagNegOneO2 : CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2 F where
  val := Matrix.GeneralLinearGroup.mkOfDetNeZero diagMat (by rw [diagMat, Matrix.det_fin_two]; decide)
  property := by
    change Matrix.transpose diagMat * diagMat = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> decide
private theorem reflect_r24_e2 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 2) = e 4 :=
  Generic.reflect_sub_apply_left F (i := 2) (j := 4) (by decide)

private theorem reflect_r24_e4 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 4) = e 2 :=
  Generic.reflect_sub_apply_right F (i := 2) (j := 4) (by decide)

private theorem reflect_s12_e1 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 1) = e 2 :=
  Generic.reflect_sub_apply_left F (i := 1) (j := 2) (by decide)

private theorem reflect_s12_e2 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 2) = e 1 :=
  Generic.reflect_sub_apply_right F (i := 1) (j := 2) (by decide)

private theorem reflect_r24_e0 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 0) = e 0 :=
  Generic.reflect_sub_apply_of_ne F (i := 2) (j := 4) (k := 0)
    (by decide) (by decide) (by decide)

private theorem reflect_r24_e1 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 1) = e 1 :=
  Generic.reflect_sub_apply_of_ne F (i := 2) (j := 4) (k := 1)
    (by decide) (by decide) (by decide)

private theorem reflect_r24_e3 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 3) = e 3 :=
  Generic.reflect_sub_apply_of_ne F (i := 2) (j := 4) (k := 3)
    (by decide) (by decide) (by decide)

private theorem reflect_s12_e0 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 0) = e 0 :=
  Generic.reflect_sub_apply_of_ne F (i := 1) (j := 2) (k := 0)
    (by decide) (by decide) (by decide)

private theorem reflect_s12_e3 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 3) = e 3 :=
  Generic.reflect_sub_apply_of_ne F (i := 1) (j := 2) (k := 3)
    (by decide) (by decide) (by decide)

private theorem reflect_s12_e4 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 4) = e 4 :=
  Generic.reflect_sub_apply_of_ne F (i := 1) (j := 2) (k := 4)
    (by decide) (by decide) (by decide)

private noncomputable def cycle124 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) :=
  ⁅CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4),
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)⁆
private theorem cycle124_e0 : cycle124 (e 0) = e 0 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 0)))) = e 0
  rw [reflect_s12_e0, reflect_r24_e0, reflect_s12_e0, reflect_r24_e0]
private theorem cycle124_e1 : cycle124 (e 1) = e 2 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 1)))) = e 2
  rw [reflect_s12_e1, reflect_r24_e2, reflect_s12_e4, reflect_r24_e4]
private theorem cycle124_e2 : cycle124 (e 2) = e 4 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 2)))) = e 4
  rw [reflect_s12_e2, reflect_r24_e1, reflect_s12_e1, reflect_r24_e2]
private theorem cycle124_e3 : cycle124 (e 3) = e 3 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 3)))) = e 3
  rw [reflect_s12_e3, reflect_r24_e3, reflect_s12_e3, reflect_r24_e3]
private theorem cycle124_e4 : cycle124 (e 4) = e 1 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 4)))) = e 1
  rw [reflect_s12_e4, reflect_r24_e4, reflect_s12_e2, reflect_r24_e1]
public theorem sign_t : signEquiv stdFrame.e ({0, 1} : Finset (Fin 5)) = stdFrame.t := by
  apply LinearEquiv.toLinearMap_injective
  apply stdFrame.e.ext
  intro i
  change (signEquiv stdFrame.e ({0, 1} : Finset (Fin 5))) (stdFrame.e i) = stdFrame.t (stdFrame.e i)
  rw [signEquiv_apply_basis, FrameData.t_e]
  fin_cases i <;> simp <;> rfl
public theorem sign_z : signEquiv stdFrame.e ({0, 1, 2, 3} : Finset (Fin 5)) = stdFrame.z := by
  apply LinearEquiv.toLinearMap_injective
  apply stdFrame.e.ext
  intro i
  change (signEquiv stdFrame.e ({0, 1, 2, 3} : Finset (Fin 5))) (stdFrame.e i) = stdFrame.z (stdFrame.e i)
  rw [signEquiv_apply_basis, FrameData.z_e]
  fin_cases i <;> simp <;> rfl
private theorem sign_beta :
    signEquiv stdFrame.e ({0, 2} : Finset (Fin 5)) =
      stdFrame.betaO diagNegOneO2 diagNegOneO2 := by
  apply LinearEquiv.toLinearMap_injective
  apply stdFrame.e.ext
  intro i
  change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e i) =
    (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e i)
  fin_cases i
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 0) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 0)
    rw [signEquiv_apply_basis, FrameData.beta_e_zero]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 1) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 1)
    rw [signEquiv_apply_basis, FrameData.beta_e_one]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 2) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 2)
    rw [signEquiv_apply_basis, FrameData.beta_e_two]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 3) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 3)
    rw [signEquiv_apply_basis, FrameData.beta_e_three]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 4) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 4)
    rw [signEquiv_apply_basis, FrameData.beta_e_four]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
private noncomputable def betaGi : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) :=
  stdFrame.betaO diagNegOneO2 diagNegOneO2
private theorem betaGi_mem_derived : betaGi ∈ derived := stdFrame.betaO_diag_mem_commutator diagNegOneO2
private theorem t_mem_derived : stdFrame.t ∈ derived := stdFrame.t_mem_commutator
private theorem z_mem_derived : stdFrame.z ∈ derived := stdFrame.z_mem_commutator
private theorem cycle124_mem_derived : cycle124 ∈ derived :=
  Subgroup.commutator_mem_commutator
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (Generic.Q F) (e 2 - e 4))
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (Generic.Q F) (e 1 - e 2))
private def cPerm : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 2 4
private theorem cPerm_apply (i : Fin 5) : cPerm i =
    if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 4 else if i = 3 then 3 else 1 := by
  fin_cases i <;> decide
private theorem cycle124_apply_basis (i : Fin 5) : cycle124 (e i) = e (cPerm i) := by
  rw [cPerm_apply]
  fin_cases i
  · simpa [Generic.e_apply] using cycle124_e0
  · simpa [Generic.e_apply] using cycle124_e1
  · simpa [Generic.e_apply] using cycle124_e2
  · simpa [Generic.e_apply] using cycle124_e3
  · simpa [Generic.e_apply] using cycle124_e4
theorem conj_signEquiv {g : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)} {σ : Equiv.Perm (Fin 5)}
    (hg : ∀ i, g (stdFrame.e i) = stdFrame.e (σ i)) (S : Finset (Fin 5)) :
    g * signEquiv stdFrame.e S * g⁻¹ = signEquiv stdFrame.e (S.image σ) := by
  apply LinearEquiv.toLinearMap_injective
  apply stdFrame.e.ext
  intro i
  have hg_inv : g⁻¹ (stdFrame.e i) = stdFrame.e (σ.symm i) := by
    apply g.injective
    calc g (g⁻¹ (stdFrame.e i)) = stdFrame.e i := LinearEquiv.apply_symm_apply g _
      _ = g (stdFrame.e (σ.symm i)) := by rw [hg, Equiv.apply_symm_apply]
  change (((g * signEquiv stdFrame.e S * g⁻¹ : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F))) (stdFrame.e i)) =
    (signEquiv stdFrame.e (S.image σ) : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e i)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg_inv,
    signEquiv_apply_basis, map_smul, hg, signEquiv_apply_basis, Equiv.apply_symm_apply]
  by_cases hi : σ.symm i ∈ S
  · have hmem : i ∈ S.image σ := by
      refine Finset.mem_image.mpr ⟨σ.symm i, hi, ?_⟩; simp
    rw [if_pos hi, if_pos hmem]
  · have hnot : i ∉ S.image σ := by
      intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      have hji' : j = σ.symm i := by simpa using congrArg σ.symm hji
      exact hi (hji' ▸ hj)
    rw [if_neg hi, if_neg hnot]
private theorem sign_c4 :
    cycle124 * betaGi * cycle124⁻¹ = signEquiv stdFrame.e ({0, 4} : Finset (Fin 5)) := by
  rw [show betaGi = signEquiv stdFrame.e ({0, 2} : Finset (Fin 5)) from sign_beta.symm]
  rw [conj_signEquiv (g := cycle124) (σ := cPerm) cycle124_apply_basis]
  congr 1
private theorem c4_mem_derived : cycle124 * betaGi * cycle124⁻¹ ∈ derived :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ cycle124_mem_derived betaGi_mem_derived)
    (Subgroup.inv_mem _ cycle124_mem_derived)
local instance instFiniteLinearEquiv : Finite ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) :=
  Finite.of_injective (fun f : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) => f.toFun) (by
      intro f g h
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext
      intro x
      exact congrFun h x)
open CFSG.Open

private def genSet (a b c d : Bool) : Finset (Fin 5) :=
  symmDiff (symmDiff (symmDiff (if a then ({0, 1} : Finset (Fin 5)) else ∅)
    (if b then {0, 2} else ∅)) (if c then {0, 1, 2, 3} else ∅))
    (if d then {0, 4} else ∅)

private noncomputable def genProd (a b c d : Bool) : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) :=
  (((if a then stdFrame.t else 1) * (if b then betaGi else 1)) *
    (if c then stdFrame.z else 1)) * (if d then cycle124 * betaGi * cycle124⁻¹ else 1)

private theorem genProd_mem_derived (a b c d : Bool) : genProd a b c d ∈ derived := by
  have ht := t_mem_derived
  have hb := betaGi_mem_derived
  have hz := z_mem_derived
  have hc := c4_mem_derived
  have ht' := t_mem_derived
  have hb' : stdFrame.beta diagNegOneO2 diagNegOneO2 ∈ derived := by simpa [betaGi] using betaGi_mem_derived
  have hz' := z_mem_derived
  have hc' : cycle124 * stdFrame.beta diagNegOneO2 diagNegOneO2 * cycle124⁻¹ ∈ derived := by
    simpa [betaGi] using c4_mem_derived
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    simp only [genProd] <;>
    repeat' first | exact Subgroup.one_mem _ | exact ht' | exact hb' | exact hz' | exact hc' |
      apply Subgroup.mul_mem

private theorem signEquiv_genSet (a b c d : Bool) :
    signEquiv stdFrame.e (genSet a b c d) = genProd a b c d := by
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    simp [genSet, genProd, betaGi, ← signEquiv_mul, sign_t, sign_z, sign_beta, sign_c4,
      signEquiv_empty, sign_c4.symm]

private theorem even_finset_decomp (S : Finset (Fin 5)) (hS : Even S.card) :
    ∃ a b c d : Bool, S = genSet a b c d := by
  revert S
  decide

theorem even_sign_mem_derived (S : Finset (Fin 5)) (hS : Even S.card) :
    signEquiv stdFrame.e S ∈ derived := by
  obtain ⟨a, b, c, d, rfl⟩ := even_finset_decomp S hS
  rw [signEquiv_genSet]
  exact genProd_mem_derived a b c d

private theorem det_eq_one_of_mem_derived (g : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (hg : g ∈ derived) :
    LinearEquiv.det g = 1 := by
  let detHom : ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) →* Fˣ := LinearEquiv.det
  have hcomm : derived ≤ commutator ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) :=
    Subgroup.commutator_mono le_top le_top
  have hker : commutator ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) ≤ detHom.ker :=
    Abelianization.commutator_subset_ker detHom
  simpa [MonoidHom.mem_ker, detHom] using hker (hcomm hg)

theorem mem_frameSigns_iff {g : G} :
    g ∈ frameSigns ↔ ∃ S : Finset (Fin 5), Even S.card ∧
      (g : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) = signEquiv stdFrame.e S := by
  constructor
  · intro hg
    rw [frameSigns, Subgroup.mem_subgroupOf] at hg
    obtain ⟨S, hS⟩ := hg
    refine ⟨S, ?_, hS⟩
    have hdet : (LinearEquiv.det (signEquiv stdFrame.e S) : F) = 1 := by
      rw [← hS]
      exact congrArg Units.val (det_eq_one_of_mem_derived g.val g.2)
    rw [det_signEquiv] at hdet
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : F) ≠ 1)).mp hdet
  · rintro ⟨S, hEven, hval⟩
    rw [frameSigns, Subgroup.mem_subgroupOf]
    exact ⟨S, hval⟩

@[expose]
noncomputable def signMask (b : frameSigns) : Finset (Fin 5) :=
  Classical.choose (mem_frameSigns_iff.mp b.2)

theorem signMask_spec (b : frameSigns) :
    (b : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) = signEquiv stdFrame.e (signMask b) :=
  (Classical.choose_spec (mem_frameSigns_iff.mp b.2)).2

theorem signMask_unique {b : frameSigns} {S : Finset (Fin 5)}
    (h : (b : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) = signEquiv stdFrame.e S) :
    S = signMask b := by
  apply CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow.signEquiv_injective
    (by decide : (2 : F) ≠ 0) stdFrame.e
  change signEquiv stdFrame.e S = signEquiv stdFrame.e (signMask b)
  rw [← h, signMask_spec]

theorem even_card_signMask (b : frameSigns) : Even (signMask b).card :=
  (Classical.choose_spec (mem_frameSigns_iff.mp b.2)).1

theorem signMask_apply_basis (b : frameSigns) (i : Fin 5) :
    (b : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (e i) =
      (if i ∈ signMask b then (-1 : F) else 1) • e i := by
  rw [signMask_spec]
  exact signEquiv_apply_basis stdFrame.e (signMask b) i

@[expose]
noncomputable def frameSignsOfEven (S : Finset (Fin 5)) (hS : Even S.card) : frameSigns :=
  (⟨(⟨signEquiv stdFrame.e S, even_sign_mem_derived S hS⟩ : G),
    mem_frameSigns_iff.mpr ⟨S, hS, rfl⟩⟩ : frameSigns)

theorem frameSignsOfEven_val (S : Finset (Fin 5)) (hS : Even S.card) :
    (frameSignsOfEven S hS : G) = (⟨signEquiv stdFrame.e S, even_sign_mem_derived S hS⟩ : G) := rfl

theorem mem_coordinateEight_iff {b : frameSigns} {i : Fin 5} :
    (b : G) ∈ coordinateEight i ↔
      (b : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (e i) = e i := by
  rw [coordinateEight, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, h⟩
    simpa [Subgroup.smul_def] using h
  · intro h
    exact ⟨b.2, by simpa [Subgroup.smul_def] using h⟩

theorem not_mem_signMask_of_mem_coordinateEight {b : frameSigns} {i : Fin 5}
    (hb : (b : G) ∈ coordinateEight i) : i ∉ signMask b := by
  intro hi
  have hact : (b : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (e i) = e i :=
    (mem_coordinateEight_iff.mp hb)
  have hcoord : (if i ∈ signMask b then (-1 : F) else 1) • e i = e i := by
    rw [← signMask_apply_basis b i]
    exact hact
  have hcoord_i := congrFun hcoord i
  simp only [Pi.smul_apply, if_true, smul_eq_mul, mul_one] at hcoord_i
  rw [if_pos hi] at hcoord_i
  simp [Generic.e_apply, Pi.single_apply] at hcoord_i
  exact (by decide : (-1 : F) ≠ 1) hcoord_i

@[expose]
noncomputable def coordinateEightOfEven (i : Fin 5) (S : Finset (Fin 5))
    (hS : Even S.card) (hi : i ∉ S) : coordinateEight i :=
  (⟨frameSignsOfEven S hS,
    mem_coordinateEight_iff.mpr (by
      change (signEquiv stdFrame.e S) (stdFrame.e i) = stdFrame.e i
      rw [signEquiv_apply_basis, if_neg hi, one_smul])⟩ : coordinateEight i)

private theorem frameSignsToEven_injective :
    Function.Injective (fun b : frameSigns =>
      (⟨signMask b, even_card_signMask b⟩ : {S : Finset (Fin 5) // Even S.card})) := by
  intro b1 b2 h
  have hsign : signMask b1 = signMask b2 := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  rw [signMask_spec b1, signMask_spec b2, hsign]

private theorem frameSignsOfEven_injective :
    Function.Injective (fun S : {S : Finset (Fin 5) // Even S.card} =>
      frameSignsOfEven S.1 S.2) := by
  intro S T h
  have hval : signEquiv stdFrame.e S.1 = signEquiv stdFrame.e T.1 := by
    have := congrArg (fun b : frameSigns => (b : G).val) h
    simpa [frameSignsOfEven] using this
  exact Subtype.ext (CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow.signEquiv_injective
    (by decide : (2 : F) ≠ 0) stdFrame.e hval)

theorem card_frameSigns : Nat.card frameSigns = 16 := by
  have hcard : Nat.card {S : Finset (Fin 5) // Even S.card} = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide
  apply le_antisymm
  · have h := Nat.card_le_card_of_injective _ frameSignsToEven_injective
    rwa [hcard] at h
  · have h := Nat.card_le_card_of_injective _ frameSignsOfEven_injective
    rwa [hcard] at h

private theorem isElemAbelian_signChangeSubgroup :
    CFSG.Open.IsElemAbelian 2 (signChangeSubgroup stdFrame.e) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨S, hS⟩ := a.2
    obtain ⟨T, hT⟩ := b.2
    apply Subtype.ext
    change (a : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) * b = b * a
    rw [hS, hT]
    exact signEquiv_comm stdFrame.e S T
  · obtain ⟨S, hS⟩ := hx
    rw [hS]
    exact signEquiv_mul_self stdFrame.e S

theorem isElemAbelian_frameSigns : CFSG.Open.IsElemAbelian 2 frameSigns :=
  isElemAbelian_signChangeSubgroup.subgroupOf derived

private theorem coordinateEightToEven_injective (i : Fin 5) :
    Function.Injective (fun b : coordinateEight i =>
      let bF : frameSigns := ⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩
      (⟨signMask bF, even_card_signMask bF,
        not_mem_signMask_of_mem_coordinateEight (b := bF) b.2⟩ :
        {S : Finset (Fin 5) // Even S.card ∧ i ∉ S})) := by
  intro b1 b2 h
  let bF1 : frameSigns := ⟨b1.1, (Subgroup.mem_inf.mp b1.2).1⟩
  let bF2 : frameSigns := ⟨b2.1, (Subgroup.mem_inf.mp b2.2).1⟩
  have hsign : signMask bF1 = signMask bF2 := congrArg Subtype.val h
  have hbF : bF1 = bF2 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [signMask_spec bF1, signMask_spec bF2, hsign]
  apply Subtype.ext
  exact congrArg (fun b : frameSigns => (b : G)) hbF

private theorem coordinateEightOfEven_injective (i : Fin 5) :
    Function.Injective (fun S : {S : Finset (Fin 5) // Even S.card ∧ i ∉ S} =>
      coordinateEightOfEven i S.1 S.2.1 S.2.2) := by
  intro S T h
  have hval : signEquiv stdFrame.e S.1 = signEquiv stdFrame.e T.1 := by
    have := congrArg (fun b : coordinateEight i => (b : G).val) h
    simpa [coordinateEightOfEven, frameSignsOfEven] using this
  exact Subtype.ext (CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow.signEquiv_injective
    (by decide : (2 : F) ≠ 0) stdFrame.e hval)

theorem card_coordinateEight (i : Fin 5) : Nat.card (coordinateEight i) = 8 := by
  have hcard : Nat.card {S : Finset (Fin 5) // Even S.card ∧ i ∉ S} = 8 := by
    rw [Nat.card_eq_fintype_card]
    fin_cases i <;> decide
  apply le_antisymm
  · have h := Nat.card_le_card_of_injective _ (coordinateEightToEven_injective i)
    rwa [hcard] at h
  · have h := Nat.card_le_card_of_injective _ (coordinateEightOfEven_injective i)
    rwa [hcard] at h

theorem isElemAbelian_coordinateEight (i : Fin 5) : CFSG.Open.IsElemAbelian 2 (coordinateEight i) :=
  CFSG.Open.IsElemAbelian.mono isElemAbelian_frameSigns inf_le_left

theorem coordinateEight_mem_rankThreeOrbit : coordinateEight 4 ∈ rankThreeOrbit :=
  ⟨1, by rw [CFSG.Quasithin.A1b.conjSub_one]⟩

theorem isInvColl_rankThreeOrbit : E1.IsInvColl (⊤ : Subgroup G) rankThreeOrbit := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    exact le_top
  · rintro A ⟨g, rfl⟩
    exact (isElemAbelian_coordinateEight 4).map (MulAut.conj g).toMonoidHom
  · rintro A ⟨g, rfl⟩ h _
    refine ⟨h * g, ?_⟩
    exact (CFSG.Quasithin.A1b.conjSub_mul h g (coordinateEight 4)).symm

theorem isElemAbelian_of_mem_rankThreeOrbit {A : Subgroup G} (hA : A ∈ rankThreeOrbit) :
    CFSG.Open.IsElemAbelian 2 A :=
  isInvColl_rankThreeOrbit.isElemAbelian A hA

theorem card_of_mem_rankThreeOrbit {A : Subgroup G} (hA : A ∈ rankThreeOrbit) :
    Nat.card A = 8 := by
  obtain ⟨g, rfl⟩ := hA
  rw [CFSG.Quasithin.A1b.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact card_coordinateEight 4

theorem coordinateEight_one_mem_rankThreeOrbit :
    coordinateEight 1 ∈ rankThreeOrbit := by
  let c : G := ⟨cycle124, cycle124_mem_derived⟩
  have hle : CFSG.Quasithin.A1b.conjSub c (coordinateEight 4) ≤ coordinateEight 1 := by
    intro x hx
    change x ∈ (coordinateEight 4).map (MulAut.conj c).toMonoidHom at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
    rw [← hxy]
    let yF : frameSigns := ⟨y, (Subgroup.mem_inf.mp hy).1⟩
    let S : Finset (Fin 5) := signMask yF
    have hyval : (y : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) = signEquiv stdFrame.e S := by
      simpa [yF, S] using signMask_spec yF
    have hEven : Even (S.image cPerm).card := by
      rw [Finset.card_image_of_injective S cPerm.injective]
      simpa [S] using even_card_signMask yF
    have h4not : (4 : Fin 5) ∉ S := by
      simpa [S] using not_mem_signMask_of_mem_coordinateEight (b := yF) hy
    have hwval : ((MulAut.conj c y : G) : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) =
        signEquiv stdFrame.e (S.image cPerm) := by
      have hconj : ((MulAut.conj c y : G) : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) =
          cycle124 * (y : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) * cycle124⁻¹ := by
        rw [MulAut.conj_apply]
        rfl
      rw [hconj, hyval]
      exact conj_signEquiv (g := cycle124) (σ := cPerm) cycle124_apply_basis S
    have h1not : (1 : Fin 5) ∉ S.image cPerm := by
      intro h
      obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp h
      have h4 : cPerm 4 = 1 := by
        rw [cPerm_apply]
        decide
      have hs4 : s = 4 := cPerm.injective (by rw [hsp, h4])
      exact h4not (hs4 ▸ hs)
    have hwframe : MulAut.conj c y ∈ frameSigns :=
      mem_frameSigns_iff.mpr ⟨S.image cPerm, hEven, hwval⟩
    let wF : frameSigns := ⟨MulAut.conj c y, hwframe⟩
    have hfix : (wF : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (e 1) = e 1 := by
      change ((MulAut.conj c y : G) : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (e 1) = e 1
      rw [hwval]
      change (signEquiv stdFrame.e (S.image cPerm)) (stdFrame.e 1) = stdFrame.e 1
      rw [signEquiv_apply_basis, if_neg h1not, one_smul]
    exact mem_coordinateEight_iff.mpr hfix
  have hcard : Nat.card (CFSG.Quasithin.A1b.conjSub c (coordinateEight 4)) = 8 := by
    change Nat.card ((coordinateEight 4).map (MulAut.conj c).toMonoidHom) = 8
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, card_coordinateEight]
  have heq : CFSG.Quasithin.A1b.conjSub c (coordinateEight 4) = coordinateEight 1 :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_coordinateEight, hcard])
  exact ⟨c, heq.symm⟩

private theorem d01_eq_tD :
    ((frameSignsOfEven ({0, 1} : Finset (Fin 5)) (by decide) : frameSigns) : G) =
      (⟨stdFrame.t, t_mem_derived⟩ : G) := by
  apply Subtype.ext
  change (signEquiv stdFrame.e ({0, 1} : Finset (Fin 5))) = stdFrame.t
  exact sign_t

private theorem d02_eq_betaD :
    ((frameSignsOfEven ({0, 2} : Finset (Fin 5)) (by decide) : frameSigns) : G) =
      (⟨betaGi, betaGi_mem_derived⟩ : G) := by
  apply Subtype.ext
  change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) = betaGi
  exact sign_beta

private theorem frameSignsOfEven_three_eq_zD :
    ((frameSignsOfEven ({0, 1, 2, 3} : Finset (Fin 5)) (by decide) : frameSigns) : G) =
      FiveSquareFrameGeneration.zD := by
  apply Subtype.ext
  change (signEquiv stdFrame.e ({0, 1, 2, 3} : Finset (Fin 5))) = stdFrame.z
  exact sign_z

private theorem tD_mem_coordinateEight_four :
    (⟨stdFrame.t, t_mem_derived⟩ : G) ∈ coordinateEight 4 := by
  rw [← d01_eq_tD]
  exact (coordinateEightOfEven 4 ({0, 1} : Finset (Fin 5)) (by decide) (by decide)).2

private theorem betaD_mem_coordinateEight_four :
    (⟨betaGi, betaGi_mem_derived⟩ : G) ∈ coordinateEight 4 := by
  rw [← d02_eq_betaD]
  exact (coordinateEightOfEven 4 ({0, 2} : Finset (Fin 5)) (by decide) (by decide)).2

private theorem zD_mem_coordinateEight_four :
    FiveSquareFrameGeneration.zD ∈ coordinateEight 4 := by
  rw [← frameSignsOfEven_three_eq_zD]
  exact (coordinateEightOfEven 4 ({0, 1, 2, 3} : Finset (Fin 5)) (by decide) (by decide)).2

private theorem c4D_mem_coordinateEight_one :
    (⟨cycle124 * betaGi * cycle124⁻¹, c4_mem_derived⟩ : G) ∈ coordinateEight 1 := by
  have hc4 : (⟨cycle124 * betaGi * cycle124⁻¹, c4_mem_derived⟩ : G) =
      (coordinateEightOfEven 1 ({0, 4} : Finset (Fin 5)) (by decide) (by decide) : G) := by
    apply Subtype.ext
    change cycle124 * betaGi * cycle124⁻¹ =
      signEquiv stdFrame.e ({0, 4} : Finset (Fin 5))
    exact sign_c4
  rw [hc4]
  exact (coordinateEightOfEven 1 ({0, 4} : Finset (Fin 5)) (by decide) (by decide)).2

private theorem genProd_coe (a b c d : Bool) :
    (⟨genProd a b c d, genProd_mem_derived a b c d⟩ : G) =
      (((if a then (⟨stdFrame.t, t_mem_derived⟩ : G) else 1) *
        (if b then (⟨betaGi, betaGi_mem_derived⟩ : G) else 1)) *
        (if c then (⟨stdFrame.z, z_mem_derived⟩ : G) else 1)) *
        (if d then (⟨cycle124 * betaGi * cycle124⁻¹, c4_mem_derived⟩ : G) else 1) := by
  apply Subtype.ext
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    rfl

private theorem genProd_mem_sup (a b c d : Bool) :
    (⟨genProd a b c d, genProd_mem_derived a b c d⟩ : G) ∈
      coordinateEight 1 ⊔ coordinateEight 4 := by
  have ht : (⟨stdFrame.t, t_mem_derived⟩ : G) ∈ coordinateEight 1 ⊔ coordinateEight 4 :=
    Subgroup.mem_sup_right tD_mem_coordinateEight_four
  have hb : (⟨betaGi, betaGi_mem_derived⟩ : G) ∈ coordinateEight 1 ⊔ coordinateEight 4 :=
    Subgroup.mem_sup_right betaD_mem_coordinateEight_four
  have hz : (⟨stdFrame.z, z_mem_derived⟩ : G) ∈ coordinateEight 1 ⊔ coordinateEight 4 :=
    Subgroup.mem_sup_right zD_mem_coordinateEight_four
  have hc : (⟨cycle124 * betaGi * cycle124⁻¹, c4_mem_derived⟩ : G) ∈
      coordinateEight 1 ⊔ coordinateEight 4 :=
    Subgroup.mem_sup_left c4D_mem_coordinateEight_one
  rw [genProd_coe]
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    repeat' first
      | apply Subgroup.mul_mem
      | exact Subgroup.one_mem _
      | exact ht
      | exact hb
      | exact hz
      | exact hc

theorem frameSigns_eq_coordinateEight_one_sup_four :
    frameSigns = coordinateEight 1 ⊔ coordinateEight 4 := by
  apply le_antisymm
  · intro x hx
    let xF : frameSigns := ⟨x, hx⟩
    obtain ⟨a, b, c, d, hS⟩ := even_finset_decomp (signMask xF) (even_card_signMask xF)
    have hxval : (x : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) = genProd a b c d := by
      have h := signMask_spec xF
      rw [hS, signEquiv_genSet] at h
      simpa [xF] using h
    have hxG : x = (⟨genProd a b c d, genProd_mem_derived a b c d⟩ : G) := Subtype.ext hxval
    rw [hxG]
    exact genProd_mem_sup a b c d
  · intro x hx
    exact sup_le (show coordinateEight 1 ≤ frameSigns from inf_le_left)
      (show coordinateEight 4 ≤ frameSigns from inf_le_left) hx

private theorem mem_four_genSet (a b c d : Bool) :
    (4 : Fin 5) ∈ genSet a b c d ↔ d = true := by
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    decide

private theorem genProd_false_mem_zpowers_sup (a b c : Bool) :
    (⟨genProd a b c false, genProd_mem_derived a b c false⟩ : G) ∈
      (Subgroup.zpowers
          ((frameSignsOfEven ({0, 1} : Finset (Fin 5)) (by decide) : frameSigns) : G) ⊔
        Subgroup.zpowers
          ((frameSignsOfEven ({0, 2} : Finset (Fin 5)) (by decide) : frameSigns) : G)) ⊔
        Subgroup.zpowers FiveSquareFrameGeneration.zD := by
  have ht : (⟨stdFrame.t, t_mem_derived⟩ : G) ∈
      (Subgroup.zpowers
          ((frameSignsOfEven ({0, 1} : Finset (Fin 5)) (by decide) : frameSigns) : G) ⊔
        Subgroup.zpowers
          ((frameSignsOfEven ({0, 2} : Finset (Fin 5)) (by decide) : frameSigns) : G)) ⊔
        Subgroup.zpowers FiveSquareFrameGeneration.zD := by
    rw [← d01_eq_tD]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hb : (⟨betaGi, betaGi_mem_derived⟩ : G) ∈
      (Subgroup.zpowers
          ((frameSignsOfEven ({0, 1} : Finset (Fin 5)) (by decide) : frameSigns) : G) ⊔
        Subgroup.zpowers
          ((frameSignsOfEven ({0, 2} : Finset (Fin 5)) (by decide) : frameSigns) : G)) ⊔
        Subgroup.zpowers FiveSquareFrameGeneration.zD := by
    rw [← d02_eq_betaD]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hz : (⟨stdFrame.z, z_mem_derived⟩ : G) ∈
      (Subgroup.zpowers
          ((frameSignsOfEven ({0, 1} : Finset (Fin 5)) (by decide) : frameSigns) : G) ⊔
        Subgroup.zpowers
          ((frameSignsOfEven ({0, 2} : Finset (Fin 5)) (by decide) : frameSigns) : G)) ⊔
        Subgroup.zpowers FiveSquareFrameGeneration.zD := by
    change FiveSquareFrameGeneration.zD ∈
      (Subgroup.zpowers
          ((frameSignsOfEven ({0, 1} : Finset (Fin 5)) (by decide) : frameSigns) : G) ⊔
        Subgroup.zpowers
          ((frameSignsOfEven ({0, 2} : Finset (Fin 5)) (by decide) : frameSigns) : G)) ⊔
        Subgroup.zpowers FiveSquareFrameGeneration.zD
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rw [genProd_coe]
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;>
    repeat' first
      | apply Subgroup.mul_mem
      | exact Subgroup.one_mem _
      | exact ht
      | exact hb
      | exact hz

theorem coordinateEight_four_eq_zpowers :
    coordinateEight 4 =
      (Subgroup.zpowers
          (frameSignsOfEven ({0, 1} : Finset (Fin 5)) (by decide) : G) ⊔
        Subgroup.zpowers
          (frameSignsOfEven ({0, 2} : Finset (Fin 5)) (by decide) : G)) ⊔
        Subgroup.zpowers FiveSquareFrameGeneration.zD := by
  apply le_antisymm
  · intro x hx
    let xF : frameSigns := ⟨x, (Subgroup.mem_inf.mp hx).1⟩
    obtain ⟨a, b, c, d, hS⟩ := even_finset_decomp (signMask xF) (even_card_signMask xF)
    have h4not : (4 : Fin 5) ∉ signMask xF :=
      not_mem_signMask_of_mem_coordinateEight (b := xF) hx
    have hd : d = false := by
      rw [hS] at h4not
      cases d with
      | false => rfl
      | true => exact absurd ((mem_four_genSet a b c true).mpr rfl) h4not
    have hxval : (x : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) = genProd a b c false := by
      have h := signMask_spec xF
      rw [hS, hd, signEquiv_genSet] at h
      simpa [xF] using h
    have hxG : x = (⟨genProd a b c false, genProd_mem_derived a b c false⟩ : G) := Subtype.ext hxval
    rw [hxG]
    exact genProd_false_mem_zpowers_sup a b c
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr
        (coordinateEightOfEven 4 ({0, 1} : Finset (Fin 5)) (by decide) (by decide)).2
    · exact Subgroup.zpowers_le.mpr
        (coordinateEightOfEven 4 ({0, 2} : Finset (Fin 5)) (by decide) (by decide)).2
    · exact Subgroup.zpowers_le.mpr zD_mem_coordinateEight_four

end CFSG.ClassicalGroups.Orthogonal.FiveSquareSignOrbit

end
