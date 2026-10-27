module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

public section

namespace CFSG.LinearAlgebra

open Matrix

variable {K : Type*} [Field K] {n r : ℕ}

@[expose] noncomputable def gramProjection (F : Matrix (Fin n) (Fin n) K)
    (U : Matrix (Fin n) (Fin r) K) : Matrix (Fin n) (Fin n) K :=
  U * (Uᵀ * F * U)⁻¹ * Uᵀ * F

theorem mulVec_dotProduct_of_transpose_mul_eq {F E : Matrix (Fin n) (Fin n) K}
    (hE : Eᵀ * F = F * E) (x y : Fin n → K) :
    (E *ᵥ x) ⬝ᵥ F *ᵥ y = x ⬝ᵥ F *ᵥ (E *ᵥ y) := by
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, hE, ← mulVec_mulVec]

theorem mulVec_eq_self_of_mem_range {E : Matrix (Fin n) (Fin n) K} (hE : E * E = E)
    {x : Fin n → K} (hx : x ∈ LinearMap.range E.mulVecLin) : E *ᵥ x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [mulVecLin_apply, mulVec_mulVec, hE]

theorem eq_zero_of_forall_dotProduct_mulVec_eq_zero {F : Matrix (Fin n) (Fin n) K}
    (hF : IsUnit F) {y : Fin n → K} (hy : ∀ z, z ⬝ᵥ F *ᵥ y = 0) : y = 0 := by
  have h1 : F *ᵥ y = 0 := dotProduct_eq_zero_iff.mp fun z => by rw [dotProduct_comm]; exact hy z
  exact mulVec_injective_iff_isUnit.mpr hF (h1.trans (mulVec_zero F).symm)

theorem eq_zero_of_forall_dotProduct_mulVec_eq_zero' {F : Matrix (Fin n) (Fin n) K}
    (hF : IsUnit F) {x : Fin n → K} (hx : ∀ z, x ⬝ᵥ F *ᵥ z = 0) : x = 0 := by
  have h1 : x ᵥ* F = 0 := dotProduct_eq_zero_iff.mp fun z => by
    rw [← dotProduct_mulVec]
    exact hx z
  exact vecMul_injective_iff_isUnit.mpr hF (h1.trans (zero_vecMul F).symm)

theorem exists_mul_eq_of_range_le {m p : ℕ} {A : Matrix (Fin n) (Fin m) K}
    {B : Matrix (Fin n) (Fin p) K}
    (h : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    ∃ M : Matrix (Fin p) (Fin m) K, B * M = A := by
  have hv : ∀ j, ∃ v, B *ᵥ v = A *ᵥ Pi.single j 1 := fun j => h ⟨Pi.single j 1, rfl⟩
  choose v hv using hv
  refine ⟨Matrix.of fun i j => v j i, Matrix.ext fun i j => ?_⟩
  have h1 := congrFun (hv j) i
  rw [mulVec_single_one, col_apply] at h1
  rw [← h1, Matrix.mul_apply, mulVec, dotProduct]
  rfl

theorem range_mul_le (A : Matrix (Fin n) (Fin r) K) {m : ℕ} (B : Matrix (Fin r) (Fin m) K) :
    LinearMap.range (A * B).mulVecLin ≤ LinearMap.range A.mulVecLin := by
  rw [mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem ker_eq_orthogonalBilin_range {F E : Matrix (Fin n) (Fin n) K} (hF : IsUnit F)
    (hE : Eᵀ * F = F * E) :
    LinearMap.ker E.mulVecLin =
      (LinearMap.range E.mulVecLin).orthogonalBilin (Matrix.toBilin' F) := by
  ext y
  rw [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_orthogonalBilin]
  constructor
  · rintro hy _ ⟨u, rfl⟩
    rw [toBilin'_apply', mulVecLin_apply, mulVec_dotProduct_of_transpose_mul_eq hE, hy,
      mulVec_zero, dotProduct_zero]
  · intro hy
    refine eq_zero_of_forall_dotProduct_mulVec_eq_zero hF fun z => ?_
    have h1 := hy (E *ᵥ z) ⟨z, rfl⟩
    rwa [toBilin'_apply', mulVec_dotProduct_of_transpose_mul_eq hE] at h1

theorem nondegenerate_restrict_range {F E : Matrix (Fin n) (Fin n) K} (hF : IsUnit F)
    (hE2 : E * E = E) (hE : Eᵀ * F = F * E) :
    ((Matrix.toBilin' F).restrict (LinearMap.range E.mulVecLin)).Nondegenerate := by
  refine ⟨fun x hx => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩
  · refine eq_zero_of_forall_dotProduct_mulVec_eq_zero' hF fun z => ?_
    have h1 := hx ⟨E *ᵥ z, z, rfl⟩
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, toBilin'_apply'] at h1
    rw [← mulVec_eq_self_of_mem_range hE2 x.2, mulVec_dotProduct_of_transpose_mul_eq hE]
    exact h1
  · refine eq_zero_of_forall_dotProduct_mulVec_eq_zero hF fun z => ?_
    have h1 := hy ⟨E *ᵥ z, z, rfl⟩
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, toBilin'_apply'] at h1
    rw [← mulVec_eq_self_of_mem_range hE2 y.2, ← mulVec_dotProduct_of_transpose_mul_eq hE]
    exact h1

theorem eq_gramProjection {F E : Matrix (Fin n) (Fin n) K} {U : Matrix (Fin n) (Fin r) K}
    (hE2 : E * E = E) (hE : Eᵀ * F = F * E)
    (hUE : LinearMap.range U.mulVecLin = LinearMap.range E.mulVecLin)
    (hG : IsUnit (Uᵀ * F * U)) : E = gramProjection F U := by
  obtain ⟨V, hV⟩ := exists_mul_eq_of_range_le hUE.le
  obtain ⟨M, hM⟩ := exists_mul_eq_of_range_le hUE.ge
  have hEU : E * U = U := by rw [← hV, ← Matrix.mul_assoc, hE2]
  have hUFE : Uᵀ * F * E = Uᵀ * F := by
    rw [Matrix.mul_assoc, ← hE, ← Matrix.mul_assoc, ← transpose_mul, hEU]
  have hGM : M = (Uᵀ * F * U)⁻¹ * (Uᵀ * F) := by
    have h1 : (Uᵀ * F * U) * M = Uᵀ * F := by rw [Matrix.mul_assoc, hM, hUFE]
    calc M = (Uᵀ * F * U)⁻¹ * ((Uᵀ * F * U) * M) := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hG),
            Matrix.one_mul]
      _ = (Uᵀ * F * U)⁻¹ * (Uᵀ * F) := by rw [h1]
  rw [← hM, hGM, gramProjection]
  simp only [Matrix.mul_assoc]

theorem isUnit_gram_of_range_eq {F E : Matrix (Fin n) (Fin n) K} (hF : IsUnit F)
    (hE2 : E * E = E) (hE : Eᵀ * F = F * E) {U : Matrix (Fin n) (Fin r) K}
    (hU : Function.Injective U.mulVec)
    (hUE : LinearMap.range U.mulVecLin = LinearMap.range E.mulVecLin) :
    IsUnit (Uᵀ * F * U) := by
  refine mulVec_injective_iff_isUnit.mp fun c c' hcc' => hU ?_
  have h0 : (Uᵀ * F * U) *ᵥ (c - c') = 0 := by rw [mulVec_sub, hcc', sub_self]
  have hUc : U *ᵥ (c - c') ∈ LinearMap.range E.mulVecLin := hUE ▸ ⟨c - c', rfl⟩
  suffices U *ᵥ (c - c') = 0 by rwa [mulVec_sub, sub_eq_zero] at this
  refine eq_zero_of_forall_dotProduct_mulVec_eq_zero hF fun z => ?_
  obtain ⟨d, hd⟩ : E *ᵥ z ∈ LinearMap.range U.mulVecLin := hUE ▸ ⟨z, rfl⟩
  rw [← mulVec_eq_self_of_mem_range hE2 hUc, ← mulVec_dotProduct_of_transpose_mul_eq hE, ← hd,
    mulVecLin_apply, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h0,
    dotProduct_zero]

theorem gramProjection_spec {F : Matrix (Fin n) (Fin n) K} (hFsymm : Fᵀ = F)
    {U : Matrix (Fin n) (Fin r) K} (hG : IsUnit (Uᵀ * F * U)) :
    gramProjection F U * gramProjection F U = gramProjection F U ∧
      (gramProjection F U)ᵀ * F = F * gramProjection F U ∧
      LinearMap.range (gramProjection F U).mulVecLin = LinearMap.range U.mulVecLin ∧
      (gramProjection F U).rank = r := by
  have hdet := (isUnit_iff_isUnit_det _).mp hG
  have hGT : (Uᵀ * F * U)ᵀ = Uᵀ * F * U := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hFsymm, Matrix.mul_assoc]
  have hGiT : ((Uᵀ * F * U)⁻¹)ᵀ = (Uᵀ * F * U)⁻¹ := by rw [transpose_nonsing_inv, hGT]
  have hPU : gramProjection F U * U = U := by
    calc gramProjection F U * U = U * ((Uᵀ * F * U)⁻¹ * (Uᵀ * F * U)) := by
          simp only [gramProjection, Matrix.mul_assoc]
      _ = U := by rw [nonsing_inv_mul _ hdet, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc gramProjection F U * gramProjection F U =
        gramProjection F U * U * ((Uᵀ * F * U)⁻¹ * Uᵀ * F) := by
          simp only [gramProjection, Matrix.mul_assoc]
      _ = gramProjection F U := by
          rw [hPU, gramProjection]
          simp only [Matrix.mul_assoc]
  · rw [gramProjection, transpose_mul, transpose_mul, transpose_mul, transpose_transpose, hFsymm,
      hGiT]
    simp only [Matrix.mul_assoc]
  · refine le_antisymm ?_ ?_
    · rw [gramProjection, Matrix.mul_assoc, Matrix.mul_assoc]
      exact range_mul_le _ _
    · calc LinearMap.range U.mulVecLin = LinearMap.range (gramProjection F U * U).mulVecLin := by
            rw [hPU]
        _ ≤ _ := range_mul_le _ _
  · have hGr : (Uᵀ * F * U).rank = r := by
      rw [rank_of_isUnit _ hG, Fintype.card_fin]
    have hG' : Uᵀ * F * U = Uᵀ * F * gramProjection F U * U := by
      rw [Matrix.mul_assoc _ (gramProjection F U), hPU]
    refine le_antisymm ?_ ?_
    · calc (gramProjection F U).rank ≤ U.rank := by
            rw [gramProjection, Matrix.mul_assoc, Matrix.mul_assoc]
            exact rank_mul_le_left _ _
        _ ≤ r := rank_le_width U
    · calc r = (Uᵀ * F * gramProjection F U * U).rank := by rw [← hG', hGr]
        _ ≤ (Uᵀ * F * gramProjection F U).rank := rank_mul_le_left _ _
        _ ≤ (gramProjection F U).rank := rank_mul_le_right _ _

theorem eq_of_range_eq {F E₁ E₂ : Matrix (Fin n) (Fin n) K} (hF : IsUnit F)
    (h1 : E₁ * E₁ = E₁) (h1F : E₁ᵀ * F = F * E₁) (h2 : E₂ * E₂ = E₂) (h2F : E₂ᵀ * F = F * E₂)
    (h : LinearMap.range E₁.mulVecLin = LinearMap.range E₂.mulVecLin) : E₁ = E₂ := by
  obtain ⟨M₁, hM₁⟩ := exists_mul_eq_of_range_le h.le
  obtain ⟨M₂, hM₂⟩ := exists_mul_eq_of_range_le h.ge
  have h21 : E₂ * E₁ = E₁ := by rw [← hM₁, ← Matrix.mul_assoc, h2]
  have h12 : E₁ * E₂ = E₂ := by rw [← hM₂, ← Matrix.mul_assoc, h1]
  refine hF.mul_left_cancel ?_
  calc F * E₁ = F * (E₂ * E₁) := by rw [h21]
    _ = E₂ᵀ * E₁ᵀ * F := by
        rw [← Matrix.mul_assoc, ← h2F, Matrix.mul_assoc, ← h1F, Matrix.mul_assoc]
    _ = F * E₂ := by rw [← transpose_mul, h12, h2F]

section Conj

variable {F E gm gi : Matrix (Fin n) (Fin n) K} (h1 : gm * gi = 1) (h2 : gi * gm = 1)
include h2

theorem conj_mul_self (hE2 : E * E = E) : gm * E * gi * (gm * E * gi) = gm * E * gi := by
  calc gm * E * gi * (gm * E * gi) = gm * E * (gi * gm) * E * gi := by
        simp only [Matrix.mul_assoc]
    _ = gm * E * gi := by rw [h2, Matrix.mul_one, Matrix.mul_assoc gm, hE2]

omit h2 in
include h1 in
theorem transpose_mul_eq_mul_inv (hg : gmᵀ * F * gm = F) : gmᵀ * F = F * gi := by
  calc gmᵀ * F = gmᵀ * F * (gm * gi) := by rw [h1, Matrix.mul_one]
    _ = F * gi := by rw [← Matrix.mul_assoc, hg]

omit h2 in
include h1 in
theorem inv_transpose_mul_eq (hg : gmᵀ * F * gm = F) : giᵀ * F = F * gm := by
  calc giᵀ * F = giᵀ * (gmᵀ * F * gm) := by rw [hg]
    _ = (gm * gi)ᵀ * F * gm := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = F * gm := by rw [h1, transpose_one, Matrix.one_mul]

omit h2 in
include h1 in
theorem conj_transpose_mul (hg : gmᵀ * F * gm = F) (hE : Eᵀ * F = F * E) :
    (gm * E * gi)ᵀ * F = F * (gm * E * gi) := by
  calc (gm * E * gi)ᵀ * F = giᵀ * (Eᵀ * (gmᵀ * F)) := by
        rw [transpose_mul, transpose_mul]; simp only [Matrix.mul_assoc]
    _ = giᵀ * F * E * gi := by
        rw [transpose_mul_eq_mul_inv h1 hg, ← Matrix.mul_assoc Eᵀ, hE]
        simp only [Matrix.mul_assoc]
    _ = F * (gm * E * gi) := by rw [inv_transpose_mul_eq h1 hg]; simp only [Matrix.mul_assoc]

theorem range_conj :
    LinearMap.range (gm * E * gi).mulVecLin = (LinearMap.range E.mulVecLin).map gm.mulVecLin := by
  have htop : LinearMap.range gi.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr fun v => ⟨gm *ᵥ v, by rw [mulVecLin_apply, mulVec_mulVec, h2,
      one_mulVec]⟩
  rw [Matrix.mul_assoc, mulVecLin_mul, LinearMap.range_comp, mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top _ htop]

omit h2 in
include h1 in
theorem rank_conj : (gm * E * gi).rank = E.rank := by
  rw [rank_mul_eq_left_of_isUnit_det gi _ (isUnit_det_of_left_inverse h1),
    rank_mul_eq_right_of_isUnit_det gm _ (isUnit_det_of_right_inverse h1)]

omit h2 in
theorem range_mul_eq_map (U : Matrix (Fin n) (Fin r) K) :
    LinearMap.range (gm * U).mulVecLin = (LinearMap.range U.mulVecLin).map gm.mulVecLin := by
  rw [mulVecLin_mul, LinearMap.range_comp]

theorem mul_mulVec_injective {U : Matrix (Fin n) (Fin r) K} (hU : Function.Injective U.mulVec) :
    Function.Injective (gm * U).mulVec := by
  intro c c' hcc'
  refine hU ?_
  have h3 := congrArg (fun v => gi *ᵥ v) hcc'
  simp only [mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul] at h3
  exact h3

omit h2 in
theorem gram_mul (hg : gmᵀ * F * gm = F) (U : Matrix (Fin n) (Fin r) K) :
    (gm * U)ᵀ * F * (gm * U) = Uᵀ * F * U := by
  calc (gm * U)ᵀ * F * (gm * U) = Uᵀ * (gmᵀ * F * gm) * U := by
        rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = Uᵀ * F * U := by rw [hg]

omit h2 in
include h1 in
theorem gramProjection_mul (hg : gmᵀ * F * gm = F) (U : Matrix (Fin n) (Fin r) K) :
    gramProjection F (gm * U) = gm * gramProjection F U * gi := by
  rw [gramProjection, gramProjection, gram_mul hg, transpose_mul]
  calc gm * U * (Uᵀ * F * U)⁻¹ * (Uᵀ * gmᵀ) * F =
      gm * U * (Uᵀ * F * U)⁻¹ * Uᵀ * (gmᵀ * F) := by simp only [Matrix.mul_assoc]
    _ = gm * (U * (Uᵀ * F * U)⁻¹ * Uᵀ * F) * gi := by
        rw [transpose_mul_eq_mul_inv h1 hg]
        simp only [Matrix.mul_assoc]

end Conj

theorem selfadjoint_idempotent_determined_by_image {F : Matrix (Fin n) (Fin n) K}
    (hFsymm : Fᵀ = F) (hF : IsUnit F) {E : Matrix (Fin n) (Fin n) K} (hE2 : E * E = E)
    (hEF : Eᵀ * F = F * E) (hrank : E.rank = r) :
    ((Matrix.toBilin' F).restrict (LinearMap.range E.mulVecLin)).Nondegenerate ∧
    LinearMap.ker E.mulVecLin =
      (LinearMap.range E.mulVecLin).orthogonalBilin (Matrix.toBilin' F) ∧
    (∀ U : Matrix (Fin n) (Fin r) K, LinearIndependent K U.col →
      Submodule.span K (Set.range U.col) = LinearMap.range E.mulVecLin →
        IsUnit (Uᵀ * F * U) ∧ E = gramProjection F U) ∧
    (∀ U : Matrix (Fin n) (Fin r) K, IsUnit (Uᵀ * F * U) →
      gramProjection F U * gramProjection F U = gramProjection F U ∧
      (gramProjection F U)ᵀ * F = F * gramProjection F U ∧
      LinearMap.range (gramProjection F U).mulVecLin = LinearMap.range U.mulVecLin ∧
      (gramProjection F U).rank = r ∧
      ∀ E' : Matrix (Fin n) (Fin n) K, E' * E' = E' → E'ᵀ * F = F * E' →
        LinearMap.range E'.mulVecLin = LinearMap.range U.mulVecLin → E' = gramProjection F U) ∧
    (∀ E₁ E₂ : Matrix (Fin n) (Fin n) K, E₁ * E₁ = E₁ → E₁ᵀ * F = F * E₁ → E₂ * E₂ = E₂ →
      E₂ᵀ * F = F * E₂ →
        (LinearMap.range E₁.mulVecLin = LinearMap.range E₂.mulVecLin ↔ E₁ = E₂)) ∧
    ∀ g : GL (Fin n) K, (g : Matrix (Fin n) (Fin n) K)ᵀ * F * (g : Matrix (Fin n) (Fin n) K) = F →
      ∀ E' : Matrix (Fin n) (Fin n) K, E' = (g : Matrix (Fin n) (Fin n) K) * E *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
        E' * E' = E' ∧ E'ᵀ * F = F * E' ∧ E'.rank = r ∧
        LinearMap.range E'.mulVecLin =
          (LinearMap.range E.mulVecLin).map (g : Matrix (Fin n) (Fin n) K).mulVecLin ∧
        ∀ U : Matrix (Fin n) (Fin r) K, LinearIndependent K U.col →
          Submodule.span K (Set.range U.col) = LinearMap.range E.mulVecLin →
            LinearIndependent K ((g : Matrix (Fin n) (Fin n) K) * U).col ∧
            Submodule.span K (Set.range ((g : Matrix (Fin n) (Fin n) K) * U).col) =
              LinearMap.range E'.mulVecLin ∧
            ((g : Matrix (Fin n) (Fin n) K) * U)ᵀ * F * ((g : Matrix (Fin n) (Fin n) K) * U) =
              Uᵀ * F * U ∧
            E' = gramProjection F ((g : Matrix (Fin n) (Fin n) K) * U) := by
  have hbasis : ∀ U : Matrix (Fin n) (Fin r) K, LinearIndependent K U.col →
      Submodule.span K (Set.range U.col) = LinearMap.range E.mulVecLin →
        IsUnit (Uᵀ * F * U) ∧ E = gramProjection F U := by
    intro U hU hspan
    have hUE : LinearMap.range U.mulVecLin = LinearMap.range E.mulVecLin := by
      rw [range_mulVecLin, hspan]
    have hG := isUnit_gram_of_range_eq hF hE2 hEF (mulVec_injective_iff.mpr hU) hUE
    exact ⟨hG, eq_gramProjection hE2 hEF hUE hG⟩
  refine ⟨nondegenerate_restrict_range hF hE2 hEF, ker_eq_orthogonalBilin_range hF hEF, hbasis,
    fun U hG => ?_, fun E₁ E₂ h1 h1F h2 h2F => ⟨eq_of_range_eq hF h1 h1F h2 h2F,
      fun h => by rw [h]⟩, fun g hg E' hE' => ?_⟩
  · obtain ⟨hP2, hPF, hPU, hPr⟩ := gramProjection_spec hFsymm hG
    exact ⟨hP2, hPF, hPU, hPr, fun E' h1 h1F hE'U => eq_gramProjection h1 h1F hE'U.symm hG⟩
  · have h1 : (g : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    subst hE'
    refine ⟨conj_mul_self h2 hE2, conj_transpose_mul h1 hg hEF, (rank_conj h1).trans hrank,
      range_conj h2, fun U hU hspan => ?_⟩
    obtain ⟨-, hEU⟩ := hbasis U hU hspan
    have hUE : LinearMap.range U.mulVecLin = LinearMap.range E.mulVecLin := by
      rw [range_mulVecLin, hspan]
    refine ⟨mulVec_injective_iff.mp (mul_mulVec_injective h2 (mulVec_injective_iff.mpr hU)), ?_,
      gram_mul hg U, ?_⟩
    · rw [← range_mulVecLin, range_mul_eq_map (gm := (g : Matrix (Fin n) (Fin n) K)) U, hUE,
        range_conj h2]
    · rw [gramProjection_mul h1 hg, ← hEU]

end CFSG.LinearAlgebra
