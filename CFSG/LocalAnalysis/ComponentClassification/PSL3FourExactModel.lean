module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Adapters.LinearFieldTransport
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public noncomputable section

namespace CFSG.ComponentClassification.PSL3Four

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

instance : CharP F4 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by decide)

theorem natCard_F4 : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card, F4.card_eq]

theorem natCard_F4' : Nat.card F4 = 2 ^ 2 := natCard_F4

theorem pow_three_eq_one (c : F4ˣ) : c ^ 3 = 1 := by
  have h : ∀ x : F4, x ≠ 0 → x ^ 3 = 1 := by decide
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h _ c.ne_zero)

@[expose] def aSL : SpecialLinearGroup (Fin 3) F4 := ⟨aMat, det_aMat⟩

@[expose] def bSL : SpecialLinearGroup (Fin 3) F4 := ⟨bMat, det_bMat⟩

@[expose] def cSL : SpecialLinearGroup (Fin 3) F4 := ⟨cMat, det_cMat⟩

theorem toGL_aSL : SpecialLinearGroup.toGL aSL = aGL := Units.ext rfl

theorem toGL_bSL : SpecialLinearGroup.toGL bSL = bGL := Units.ext rfl

theorem toGL_cSL : SpecialLinearGroup.toGL cSL = cGL := Units.ext rfl

@[expose] def rhoSL : SpecialLinearGroup (Fin 3) F4 →* Equiv.Perm (Fin 42) :=
  rho.comp SpecialLinearGroup.toGL

theorem rhoSL_apply (A : SpecialLinearGroup (Fin 3) F4) :
    rhoSL A = rho (SpecialLinearGroup.toGL A) := rfl

theorem S_le_range : S ≤ rhoSL.range := by
  rw [S, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨aSL, by rw [rhoSL_apply, toGL_aSL]; rfl⟩
  · exact ⟨bSL, by rw [rhoSL_apply, toGL_bSL]; rfl⟩
  · exact ⟨cSL, by rw [rhoSL_apply, toGL_cSL]; rfl⟩

theorem scalar_mulVec (c : F4) (v : Vec) : scalar (Fin 3) c *ᵥ v = c • v := by
  funext i
  rw [scalar_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

theorem inv_scalar {B : GL (Fin 3) F4} {c : F4} (hc : c ≠ 0)
    (hB : (B : Matrix (Fin 3) (Fin 3) F4) = scalar (Fin 3) c) :
    ((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = scalar (Fin 3) c⁻¹ := by
  have h1 : (B : Matrix (Fin 3) (Fin 3) F4) * ((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
      = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hB] at h1
  calc ((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
      = scalar (Fin 3) c⁻¹ * (scalar (Fin 3) c *
          ((B⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    _ = scalar (Fin 3) c⁻¹ := by rw [h1, mul_one]

theorem rhoFun_scalar {B : GL (Fin 3) F4} {c : F4} (hc : c ≠ 0)
    (hB : (B : Matrix (Fin 3) (Fin 3) F4) = scalar (Fin 3) c) (i : Fin 42) : rhoFun B i = i := by
  apply Fin.ext
  by_cases hi : i.val < 21
  · simp only [rhoFun, hi, ↓reduceIte]
    rw [hB, scalar_mulVec, vIdx_smul hc, vIdx_vecOf]
    omega
  · simp only [rhoFun, hi, ↓reduceIte]
    rw [inv_scalar hc hB, scalar_apply, diagonal_transpose, ← scalar_apply, scalar_mulVec,
      vIdx_smul (inv_ne_zero hc), vIdx_vecOf]
    omega

theorem scalars_le_ker : LinearFlag.scalars 3 F4 ≤ rhoSL.ker := by
  intro A hA
  obtain ⟨c, -, hAc⟩ := LinearFlag.mem_scalars.1 hA
  rw [MonoidHom.mem_ker]
  exact Equiv.ext fun i => rhoFun_scalar c.ne_zero hAc i

theorem mem_scalars_iff (A : SpecialLinearGroup (Fin 3) F4) :
    A ∈ LinearFlag.scalars 3 F4 ↔
      ∃ c : F4ˣ, (A : Matrix (Fin 3) (Fin 3) F4) = scalar (Fin 3) (c : F4) := by
  rw [LinearFlag.mem_scalars]
  exact ⟨fun ⟨c, _, hc⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨c, pow_three_eq_one c, hc⟩⟩

theorem card_scalars : Nat.card (LinearFlag.scalars 3 F4) = 3 := by
  let f : F4ˣ → LinearFlag.scalars 3 F4 := fun c =>
    ⟨LinearFlag.scalarElement c (pow_three_eq_one c),
      LinearFlag.scalarElement_mem_scalars c (pow_three_eq_one c)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c d hcd
      have h := congrArg (fun A : LinearFlag.scalars 3 F4 =>
        ((A : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) 0 0) hcd
      simp only [f, LinearFlag.coe_scalarElement, scalar_apply, diagonal_apply_eq] at h
      exact Units.ext h
    · rintro ⟨A, hA⟩
      obtain ⟨c, hc, hAc⟩ := LinearFlag.mem_scalars.1 hA
      refine ⟨c, Subtype.ext (Subtype.ext ?_)⟩
      simp only [f, LinearFlag.coe_scalarElement]
      exact hAc.symm
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_units, natCard_F4]

theorem card_SL : Nat.card (SpecialLinearGroup (Fin 3) F4) = 60480 := by
  rw [(LinearFlag.linear_order (K := F4) 2 4 natCard_F4 (n := 3) (by norm_num)).2.1]
  decide

theorem range_rhoSL : rhoSL.range = S ∧ rhoSL.ker = LinearFlag.scalars 3 F4 := by
  have h := Subgroup.card_ker_mul_card_range rhoSL
  rw [card_SL] at h
  have h1 : 20160 ≤ Nat.card rhoSL.range :=
    card_S.symm.le.trans (Subgroup.card_le_of_le S_le_range)
  have h2 : 3 ≤ Nat.card rhoSL.ker :=
    card_scalars.symm.le.trans (Subgroup.card_le_of_le scalars_le_ker)
  have hr : Nat.card rhoSL.range ≤ 20160 := by nlinarith
  have hk : Nat.card rhoSL.ker ≤ 3 := by nlinarith
  exact ⟨(Subgroup.eq_of_le_of_card_ge S_le_range (by rw [card_S]; exact hr)).symm,
    (Subgroup.eq_of_le_of_card_ge scalars_le_ker (by rw [card_scalars]; exact hk)).symm⟩

@[expose] def theta : LinearFlag.projectiveSL 3 F4 ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq range_rhoSL.2.symm).trans
    ((QuotientGroup.quotientKerEquivRange rhoSL).trans (MulEquiv.subgroupCongr range_rhoSL.1))

theorem theta_proj (A : SpecialLinearGroup (Fin 3) F4) :
    (theta (LinearFlag.proj 3 F4 A) : Equiv.Perm (Fin 42)) =
      rho (SpecialLinearGroup.toGL A) := rfl

@[expose] def projectiveSLEquivStated :
    LinearFlag.projectiveSL 3 F4 ≃* StatedProj (StatedSL 3 F4) :=
  (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 F4)).trans
    (projectiveSpecialLinearGroupEquivStatedProj 3 F4)

@[expose] def equivStated : S ≃* StatedProj (StatedSL 3 F4) :=
  theta.symm.trans projectiveSLEquivStated

theorem admissible : StatedLieAdmissible .PSL 3 2 2 :=
  ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩

theorem statedClassicalModel_S : StatedClassicalModel S .PSL 3 2 2 :=
  ⟨admissible, F4, inferInstance, inferInstance, natCard_F4', ⟨equivStated⟩⟩

theorem nonempty_equiv_of_stated (H : Type) [Group H] (h : StatedClassicalModel H .PSL 3 2 2) :
    Nonempty (H ≃* S) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  exact ⟨e.trans ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 3 2 2 (by norm_num)
    hcard).trans ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F4 3 2 2 (by norm_num)
      natCard_F4').symm.trans equivStated.symm))⟩

theorem classicalModel_S : Assembly.ComponentType.ClassicalModel S .PSL 3 2 2 :=
  ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩,
    ⟨equivStated.trans ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F4 3 2 2
      (by norm_num) natCard_F4').trans
      ((projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 2 2)).trans
        (ComponentClassification.ClassicalModelStatedBridge.pslModelEquiv 3 2 2).symm))⟩⟩


theorem exact_model :
    (∀ A : SpecialLinearGroup (Fin 3) F4, A ∈ LinearFlag.scalars 3 F4 ↔
        ∃ c : F4ˣ, (A : Matrix (Fin 3) (Fin 3) F4) = scalar (Fin 3) (c : F4)) ∧
      (∃ θ : LinearFlag.projectiveSL 3 F4 ≃* S, ∀ A : SpecialLinearGroup (Fin 3) F4,
        (θ (LinearFlag.proj 3 F4 A) : Equiv.Perm (Fin 42)) = rho (SpecialLinearGroup.toGL A)) ∧
      StatedClassicalModel S .PSL 3 2 2 ∧
      (∀ (H : Type) [Group H], StatedClassicalModel H .PSL 3 2 2 → Nonempty (H ≃* S)) ∧
      Assembly.ComponentType.ClassicalModel S .PSL 3 2 2 ∧
      ∀ (H : Type) [Group H], Assembly.ComponentType.ClassicalModel H .PSL 3 2 2 →
        Nonempty (H ≃* S) :=
  ⟨mem_scalars_iff, ⟨theta, theta_proj⟩, statedClassicalModel_S, nonempty_equiv_of_stated,
    classicalModel_S, fun H _ h => nonempty_equiv_of_stated H
      (ComponentClassification.ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel
        .PSL 3 2 2 h)⟩

end CFSG.ComponentClassification.PSL3Four
