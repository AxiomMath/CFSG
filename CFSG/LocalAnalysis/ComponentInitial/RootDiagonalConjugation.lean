module

public import CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
public import CFSG.LieType.Chevalley.RootOps.Groups
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem mapsLabelWt_yCoeff (j : Fin τ.rank) {k : ℕ} (hk : 1 ≤ k) :
    MapsLabelWt (yCoeff τ K j k) (· - k • Pi.single j 1) := by
  intro a b hab
  rcases b with l | ⟨β, hβ⟩
  · change yCoeff τ K j k (hVec τ K l) a ≠ 0 at hab
    rw [yCoeff_hVec, ite_eq_right (by omega)] at hab
    split_ifs at hab with hk1
    · subst hk1
      rw [Finsupp.smul_apply, smul_eq_mul] at hab
      rw [labelWt_of_rootVec_apply_ne_zero (right_ne_zero_of_mul hab)]
      simp [labelWt]
    · exact absurd rfl hab
  · rw [← rootVec_eq_single' hβ] at hab
    by_cases h₂ : β = -Pi.single j 1
    · subst h₂
      rw [yCoeff_rootVec_neg_single, ite_eq_right (by omega)] at hab
      exact absurd rfl hab
    by_cases h₁ : β = Pi.single j 1
    · subst h₁
      rw [yCoeff_rootVec_single, ite_eq_right (by omega)] at hab
      split_ifs at hab with hk1 hk2
      · subst hk1
        rw [labelWt_of_hVec_apply_ne_zero hab]
        simp [labelWt]
      · subst hk2
        rw [labelWt_of_rootVec_apply_ne_zero hab]
        simp only [labelWt]
        rw [two_nsmul]
        abel
      · exact absurd rfl hab
    · rw [yCoeff_rootVec_of_ne j k hβ h₁ h₂, Finsupp.smul_apply, smul_eq_mul] at hab
      rw [labelWt_of_rootVec_apply_ne_zero (right_ne_zero_of_mul hab), natCast_zsmul]
      rfl

@[expose] def rootChar (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) : Kˣ :=
  ∏ i, a i ^ v i

theorem rootChar_add (a : Fin τ.rank → Kˣ) (u v : Fin τ.rank → ℤ) :
    rootChar a (u + v) = rootChar a u * rootChar a v := by
  simp only [rootChar, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem rootChar_zero (a : Fin τ.rank → Kˣ) : rootChar a 0 = 1 := by
  simp [rootChar]

theorem rootChar_nsmul_single (a : Fin τ.rank → Kˣ) (j : Fin τ.rank) (k : ℕ) :
    rootChar a (k • Pi.single j 1) = a j ^ k := by
  rw [rootChar, Finset.prod_eq_single j (fun i _ hij => by simp [hij])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

theorem rootChar_sub (a : Fin τ.rank → Kˣ) (u v : Fin τ.rank → ℤ) :
    rootChar a (u - v) = rootChar a u * (rootChar a v)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← rootChar_add, sub_add_cancel]

theorem rootDiag_single (a : Fin τ.rank → Kˣ) (b : Label τ) :
    rootDiag a (Finsupp.single b 1) =
      ((rootChar a (labelWt τ b) : Kˣ) : K) • Finsupp.single b 1 := by
  rcases b with i | α
  · rw [rootDiag_single_inl]
    simp [labelWt, rootChar_zero]
  · rw [rootDiag_single_inr]
    rfl

theorem rootDiag_mul_of_mapsLabelWt (a : Fin τ.rank → Kˣ) {f : Module.End K (RootModule τ K)}
    {v : Fin τ.rank → ℤ} (hf : MapsLabelWt f (· + v)) :
    rootDiag a * f = ((rootChar a v : Kˣ) : K) • (f * rootDiag a) := by
  refine end_ext_single fun b => Finsupp.ext fun c => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply, rootDiag_single, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  rw [← Finsupp.sum_single (f (Finsupp.single b 1))]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finsupp.smul_single_one, map_smul, rootDiag_single, smul_smul, Finsupp.smul_apply,
    Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases hdc : d = c
  · subst hdc
    rw [hf d b (Finsupp.mem_support_iff.1 hd), rootChar_add, Units.val_mul]
    simp only [Finsupp.single_eq_same]
    ring
  · simp [Finsupp.single_eq_of_ne (Ne.symm hdc)]

theorem rootDiag_mul_xOp (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) (c : K) :
    rootDiag a * xOp τ K i c = xOp τ K i ((a i : K) * c) * rootDiag a := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [xCoeff_zero, mul_one, one_mul, pow_zero, pow_zero]
  · rw [rootDiag_mul_of_mapsLabelWt a (mapsLabelWt_xCoeff i hk), rootChar_nsmul_single,
      smul_smul]
    congr 1
    rw [mul_pow, Units.val_pow_eq_pow_val]
    ring

theorem rootDiag_mul_yOp (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) (c : K) :
    rootDiag a * yOp τ K i c = yOp τ K i (((a i)⁻¹ : Kˣ) * c) * rootDiag a := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [yCoeff_zero, mul_one, one_mul, pow_zero, pow_zero]
  · have hf : MapsLabelWt (yCoeff τ K i k) (· + (-(k • Pi.single i 1))) :=
      (mapsLabelWt_yCoeff i hk).congr fun μ => sub_eq_add_neg _ _
    rw [rootDiag_mul_of_mapsLabelWt a hf, smul_smul]
    congr 1
    rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul, rootChar_nsmul_single]
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, mul_pow, inv_pow]
    ring

theorem rootDiag_mul_rootDiag (a b : Fin τ.rank → Kˣ) :
    rootDiag a * rootDiag b = rootDiag (a * b) := by
  refine end_ext_single fun c => ?_
  rw [Module.End.mul_apply, rootDiag_single, map_smul, rootDiag_single, rootDiag_single, smul_smul,
    ← Units.val_mul]
  congr 2
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, mul_comm]

theorem rootDiag_one : rootDiag (1 : Fin τ.rank → Kˣ) = 1 := by
  refine end_ext_single fun c => ?_
  rw [rootDiag_single]
  simp [rootChar]

variable (τ) in
@[expose] def rootDiagUnit (a : Fin τ.rank → Kˣ) : ModGL τ K where
  val := rootDiag a
  inv := rootDiag a⁻¹
  val_inv := by rw [rootDiag_mul_rootDiag, mul_inv_cancel, rootDiag_one]
  inv_val := by rw [rootDiag_mul_rootDiag, inv_mul_cancel, rootDiag_one]

theorem root_diagonal_conjugation (τ : Tag) (K : Type) [Field K] (a : Fin τ.rank → Kˣ) :
    (∀ (i : Fin τ.rank) (c : K), rootDiagUnit τ a * xUnit τ K i c * (rootDiagUnit τ a)⁻¹ =
      xUnit τ K i ((a i : K) * c)) ∧
    (∀ (i : Fin τ.rank) (c : K), rootDiagUnit τ a * yUnit τ K i c * (rootDiagUnit τ a)⁻¹ =
      yUnit τ K i (((a i)⁻¹ : Kˣ) * c)) ∧
    rootDiagUnit τ a ∈ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K)) := by
  have hx : ∀ (b : Fin τ.rank → Kˣ) (i : Fin τ.rank) (c : K),
      rootDiagUnit τ b * xUnit τ K i c * (rootDiagUnit τ b)⁻¹ = xUnit τ K i ((b i : K) * c) :=
    fun b i c => Units.ext (by
      rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_xUnit]
      change rootDiag b * xOp τ K i c * rootDiag b⁻¹ = _
      rw [rootDiag_mul_xOp, mul_assoc, rootDiag_mul_rootDiag, mul_inv_cancel, rootDiag_one,
        mul_one])
  have hy : ∀ (b : Fin τ.rank → Kˣ) (i : Fin τ.rank) (c : K),
      rootDiagUnit τ b * yUnit τ K i c * (rootDiagUnit τ b)⁻¹ =
        yUnit τ K i (((b i)⁻¹ : Kˣ) * c) :=
    fun b i c => Units.ext (by
      rw [Units.val_mul, Units.val_mul, coe_yUnit, coe_yUnit]
      change rootDiag b * yOp τ K i c * rootDiag b⁻¹ = _
      rw [rootDiag_mul_yOp, mul_assoc, rootDiag_mul_rootDiag, mul_inv_cancel, rootDiag_one,
        mul_one])
  have hle : ∀ b : Fin τ.rank → Kˣ, ∀ g ∈ adjointGroup τ K,
      rootDiagUnit τ b * g * (rootDiagUnit τ b)⁻¹ ∈ adjointGroup τ K := by
    intro b g hg
    have hmap : adjointGroup τ K ≤ (adjointGroup τ K).comap
        (MulAut.conj (rootDiagUnit τ b)).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨i, c, hg | hg⟩
      · rw [show g = xUnit τ K i c from Units.ext hg]
        simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, hx]
        exact xUnit_mem_adjointGroup i _
      · rw [show g = yUnit τ K i c from Units.ext hg]
        simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, hy]
        exact yUnit_mem_adjointGroup i _
    exact hmap hg
  have hinv : (rootDiagUnit τ a)⁻¹ = rootDiagUnit τ a⁻¹ := by
    refine Units.ext ?_
    rfl
  refine ⟨hx a, hy a, Subgroup.mem_normalizer_iff.2 fun g => ⟨hle a g, fun h => ?_⟩⟩
  have := hle a⁻¹ _ h
  rw [← hinv, inv_inv] at this
  simpa [mul_assoc] using this

end FourGroupChevalley

end CFSG.LocalAnalysis.ComponentInitial
