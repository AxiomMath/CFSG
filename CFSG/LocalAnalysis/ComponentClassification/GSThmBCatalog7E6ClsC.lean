module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6ClsA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6ClsB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6L0

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CatFactsSp4

namespace Cat7E6

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

abbrev smat (x : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

@[expose] def spG (x : StatedSp 2 K) : gsp 2 K := ⟨x, statedSp_le_gsp x.2⟩

theorem conjAut_spG (x : StatedSp 2 K) : conjAut 2 K (spG x) = MulAut.conj (proj 2 K x) :=
  (conj_proj x).symm

theorem spG_mul (x y : StatedSp 2 K) : spG (x * y) = spG x * spG y := rfl

theorem conj_similitude {A G : gsp 2 K} (hG : (mat G)ᵀ * formJ 2 K * mat G = formJ 2 K)
    (hGi : (mat G⁻¹)ᵀ * formJ 2 K * mat G⁻¹ = formJ 2 K) {d : K}
    (hμ : (mat A)ᵀ * formJ 2 K * mat A = d • formJ 2 K) :
    (mat (G⁻¹ * A * G))ᵀ * formJ 2 K * mat (G⁻¹ * A * G) = d • formJ 2 K := by
  rw [mat_mul, mat_mul]
  calc (mat G⁻¹ * mat A * mat G)ᵀ * formJ 2 K * (mat G⁻¹ * mat A * mat G) =
      (mat G)ᵀ * ((mat A)ᵀ * ((mat G⁻¹)ᵀ * formJ 2 K * mat G⁻¹) * mat A) * mat G := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = d • formJ 2 K := by
        rw [hGi, hμ, Matrix.mul_smul, Matrix.smul_mul, hG]

theorem symplectic_mat_spG (x : StatedSp 2 K) :
    (mat (spG x))ᵀ * formJ 2 K * mat (spG x) = formJ 2 K := symplectic_of_mem x

theorem exists_Y [Finite K] (hodd : Odd (Nat.card K)) {q : ℕ}
    (c : Cat8.QConf (StatedProj (StatedSp 2 K)) q) {A : gsp 2 K} (hA : c.a = conjAut 2 K A)
    {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d) (hAA : mat A * mat A = d • 1)
    (hμ : (mat A)ᵀ * formJ 2 K * mat A = d • formJ 2 K) :
    ∃ Y : StatedSp 2 K, c.tau = conjAut 2 K (spG Y) ∧ smat Y * smat Y = -1 ∧
      smat Y * mat A = -(mat A * smat Y) := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨x, hx⟩ := c.g_inn
  obtain ⟨G₀, rfl⟩ := proj_surjective x
  set G := spG G₀ with hG
  have hg : c.g = conjAut 2 K G := by rw [← hx, hG, conjAut_spG]
  set A' := G⁻¹ * A * G with hA'
  set M := mat A with hM
  set M' := mat A' with hM'
  have hGs : (mat G)ᵀ * formJ 2 K * mat G = formJ 2 K := symplectic_mat_spG G₀
  have hGis : (mat G⁻¹)ᵀ * formJ 2 K * mat G⁻¹ = formJ 2 K := symplectic_mat_spG G₀⁻¹
  have hμ' : M'ᵀ * formJ 2 K * M' = d • formJ 2 K := conj_similitude hGs hGis hμ
  have hM'2 : M' * M' = d • 1 := by
    rw [hM', mat_mul, mat_mul]
    calc mat G⁻¹ * mat A * mat G * (mat G⁻¹ * mat A * mat G) =
        mat G⁻¹ * (mat A * mat A) * mat G := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (mat G) (mat G⁻¹), mat_mul_mat_inv, Matrix.one_mul]
      _ = d • 1 := by
          rw [hAA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, mat_inv_mul_mat]
  have htau : c.tau = conjAut 2 K (A * A') := by
    rw [Cat8.QConf.tau, hA, hg, hA', map_mul, map_mul, map_mul, map_inv]
  have hcomm := a_comm_conj c
  rw [hA, hg, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at hcomm
  have hk : conjAut 2 K ((A * A') * (A' * A)⁻¹) = 1 := by
    rw [map_mul, map_inv, hcomm, mul_inv_cancel]
  rw [conjAut_eq_one_iff] at hk
  obtain ⟨l, hl⟩ := hk
  have hlM : M * M' = (l : K) • (M' * M) := by
    have h1 : ((A * A' : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) l * ((A' * A : gsp 2 K) : GL _ K) := by
      rw [← hl]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    have h3 := congrArg (fun X : GL (Fin 2 ⊕ Fin 2) K =>
      (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h1
    simp only [Units.val_mul] at h3
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Matrix.smul_mul, Matrix.one_mul] at h3
    exact h3
  have hM'0 : M' ≠ 0 := by
    intro h
    rw [h, Matrix.zero_mul] at hM'2
    have := congrFun (congrFun hM'2 (Sum.inl 0)) (Sum.inl 0)
    simp at this
    exact hd0 this.symm
  have hl2 : (l : K) * l = 1 := by
    have e1 : M * (M * M') = d • M' := by
      rw [← Matrix.mul_assoc, hAA, Matrix.smul_mul, Matrix.one_mul]
    have e2 : M * (M * M') = ((l : K) * l * d) • M' := by
      rw [hlM, Matrix.mul_smul, ← Matrix.mul_assoc, hlM, Matrix.smul_mul, Matrix.mul_assoc,
        hAA, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
    have e3 : (d - (l : K) * l * d) • M' = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    have e4 := (smul_eq_zero.mp e3).resolve_right hM'0
    have e5 : (1 - (l : K) * l) * d = 0 := by linear_combination e4
    linear_combination -((mul_eq_zero.mp e5).resolve_right hd0)
  set Ym := d⁻¹ • (M * M') with hYm
  have hYs : Ymᵀ * formJ 2 K * Ym = formJ 2 K := by
    rw [hYm, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    calc (d⁻¹ * d⁻¹) • ((M * M')ᵀ * formJ 2 K * (M * M')) =
        (d⁻¹ * d⁻¹) • (M'ᵀ * (Mᵀ * formJ 2 K * M) * M') := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = formJ 2 K := by
          rw [hμ, Matrix.mul_smul, Matrix.smul_mul, hμ', smul_smul, smul_smul]
          rw [show d⁻¹ * d⁻¹ * d * d = 1 by field_simp, one_smul]
  set Y := toSp Ym hYs
  have hsY : smat Y = Ym := coe_toSp _ _
  have hM'M : M' * M = (l : K) • (M * M') := by
    rw [hlM, smul_smul, hl2, one_smul]
  have hYY : Ym * Ym = (l : K) • 1 := by
    rw [hYm, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    calc (d⁻¹ * d⁻¹) • (M * M' * (M * M')) = (d⁻¹ * d⁻¹) • (M * (M' * M) * M') := by
          simp only [Matrix.mul_assoc]
      _ = (l : K) • 1 := by
          rw [hM'M, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hAA, Matrix.smul_mul,
            Matrix.one_mul, Matrix.smul_mul, hM'2, smul_smul, smul_smul, smul_smul]
          congr 1
          field_simp
  have hYM : Ym * M = (l : K) • (M * Ym) := by
    rw [hYm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hM'M, Matrix.mul_smul,
      ← Matrix.mul_assoc, smul_comm]
  have htauY : c.tau = conjAut 2 K (spG Y) := by
    rw [htau]
    apply conjAut_eq_of_smul _ _ (c := d)
    change mat (A * A') = d • smat Y
    rw [hsY, hYm, smul_smul, mul_inv_cancel₀ hd0, one_smul]
    rfl
  rcases mul_self_eq_one_iff.mp hl2 with h1 | h1
  ·
    exfalso
    rw [h1, one_smul] at hYY hYM
    have hYY' : smat Y * smat Y = 1 := by rw [hsY]; exact hYY
    have hYM' : smat Y * M = M * smat Y := by rw [hsY]; exact hYM
    rcases eq_one_or_neg_of_commute_typeII h2 hd0 hdsq hAA hμ Y hYY' hYM' with h3 | h3
    · apply tau_ne_one c
      rw [htauY]
      exact conjAut_eq_one_of_smul _ (c := 1) (by rw [one_smul]; exact h3)
    · apply tau_ne_one c
      rw [htauY]
      exact conjAut_eq_one_of_smul _ (c := -1) (by rw [neg_one_smul]; exact h3)
  · refine ⟨Y, htauY, ?_, ?_⟩
    · rw [hsY, hYY, h1, neg_one_smul]
    · rw [hsY, hYM, h1, neg_one_smul]

theorem smat_comm_of_mem_fixOf (A : gsp 2 K) {g : StatedSp 2 K} (hg : g ∈ fixOf (conjSp 2 K A)) :
    smat g * mat A = mat A * smat g := by
  have h1 : conjSp 2 K A g = g := hg
  have h3 : mat A * smat g * mat A⁻¹ = smat g := by
    have h4 := congrArg (fun x : StatedSp 2 K => smat x) h1
    simp only [smat, coe_conjSp, Units.val_mul] at h4
    exact h4
  calc smat g * mat A = mat A * smat g * mat A⁻¹ * mat A := by rw [h3]
    _ = mat A * smat g := by rw [Matrix.mul_assoc, mat_inv_mul_mat, Matrix.mul_one]

theorem exists_Z [Finite K] (hodd : Odd (Nat.card K)) {q : ℕ}
    (c : Cat8.QConf (StatedProj (StatedSp 2 K)) q) {A : gsp 2 K} (hA : c.a = conjAut 2 K A)
    {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d) (hAA : mat A * mat A = d • 1)
    (hμ : (mat A)ᵀ * formJ 2 K * mat A = d • formJ 2 K)
    (hperf : Group.IsPerfect (fixOf (conjSp 2 K A))) :
    ∃ Z : StatedSp 2 K, Z ∈ fixOf (conjSp 2 K A) ∧ c.z = conjAut 2 K (spG Z) ∧
      smat Z * smat Z = -1 := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hc : ∀ z : StatedProj (StatedSp 2 K), z ∈ center _ → z = 1 :=
    fun z hz => center_P_eq_one hodd hz
  have hzL : c.z ∈ Cat8.L0 (StatedProj (StatedSp 2 K)) c.a := c.z_mem.2
  rw [hA, L0_eq_map hodd A hperf] at hzL
  obtain ⟨_, ⟨Z, hZ, rfl⟩, hzZ⟩ := hzL
  have hzc : c.z = conjAut 2 K (spG Z) := by rw [← hzZ, conjAut_spG]
  refine ⟨Z, hZ, hzc, ?_⟩
  have hZ2 : Z * Z ∈ spScalars 2 K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul]
    have h1 : MulAut.conj (proj 2 K Z * proj 2 K Z) = 1 := by
      rw [map_mul, ← conjAut_spG, ← hzc, c.z_sq]
    exact conj_injective_of_center hc (h1.trans (map_one _).symm)
  rw [mem_spScalars_iff] at hZ2
  simp only [Subgroup.coe_mul, Units.val_mul] at hZ2
  rcases hZ2 with h | h
  · exfalso
    have hZA := smat_comm_of_mem_fixOf A hZ
    apply c.z_ne
    rw [hzc]
    rcases eq_one_or_neg_of_commute_typeII h2 hd0 hdsq hAA hμ Z h hZA with h3 | h3
    · exact conjAut_eq_one_of_smul _ (c := 1) (by rw [one_smul]; exact h3)
    · exact conjAut_eq_one_of_smul _ (c := -1) (by rw [neg_one_smul]; exact h3)
  · exact h

end Cat7E6

end CFSG.ComponentClassification.GSThmB
