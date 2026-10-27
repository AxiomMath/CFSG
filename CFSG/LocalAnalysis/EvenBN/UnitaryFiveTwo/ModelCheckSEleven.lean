module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSSeven
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada
open scoped commutatorElement

theorem uSU_mul_self : uSU * uSU = 1 :=
  ext_mat (by rw [mat_mul, mat_uSU, mat_one]; decide)

theorem uSU_inv : uSU⁻¹ = uSU :=
  inv_eq_of_mul_eq_one_right uSU_mul_self

theorem vSU_mul_self : vSU * vSU = 1 := by
  rw [← mul_inv_cancel vSU, vSU_inv]

theorem uMat_conj_apply (M : Matrix (Fin 5) (Fin 5) F4) (i j : Fin 5) :
    (uMat * M * uMat) i j = M (![0, 3, 2, 1, 4] i) (![0, 3, 2, 1, 4] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_five, Matrix.vecMul, dotProduct]

theorem mem_map_vSU {H : Subgroup SU52} {x : SU52} :
    x ∈ H.map (MulAut.conj vSU).toMonoidHom ↔ vSU * x * vSU ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, vSU_inv]

theorem mem_map_uSU {H : Subgroup SU52} {x : SU52} :
    x ∈ H.map (MulAut.conj uSU).toMonoidHom ↔ uSU * x * uSU ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, uSU_inv]

theorem mat_vSU_conj (x : SU52) : mat (vSU * x * vSU) = vMat * mat x * vMat := by
  rw [mat_mul, mat_mul, mat_vSU]

theorem mat_uSU_conj (x : SU52) : mat (uSU * x * uSU) = uMat * mat x * uMat := by
  rw [mat_mul, mat_mul, mat_uSU]

theorem vSU_conj_x₃SU (a : F4) : vSU * x₃SU a * vSU = x₃SU (bar a) := by
  refine ext_mat ?_
  rw [mat_vSU_conj, mat_x₃SU, mat_x₃SU]
  ext i j
  rw [vMat_conj_apply]
  fin_cases i <;> fin_cases j <;> simp [x₃Mat, bar_bar]

theorem uSU_conj_x₃SU (a : F4) : uSU * x₃SU a * uSU = x₂SU a := by
  refine ext_mat ?_
  rw [mat_uSU_conj, mat_x₃SU, mat_x₂SU]
  ext i j
  rw [uMat_conj_apply]
  fin_cases i <;> fin_cases j <;> simp [x₃Mat, x₂Mat]

theorem A₁sub_inf_map_vSU : A₁sub ⊓ A₁sub.map (MulAut.conj vSU).toMonoidHom = X₃sub := by
  refine le_antisymm (fun x hx => ?_) (le_inf X₃sub_le_A₁sub fun x hx => ?_)
  · obtain ⟨hxA, hxv⟩ := mem_inf.1 hx
    rw [mem_map_vSU] at hxv
    obtain ⟨a₂, a₃, a₄, b₄, hv, e⟩ := exists_nf_of_mem_A₁sub hxA
    obtain ⟨hvS, h21, h31⟩ := mem_A₁sub.1 hxv
    have h01 := (mem_Ssub.1 hvS).1 0 1 (by decide)
    rw [mat_vSU_conj, vMat_conj_apply, e] at h01 h21 h31
    simp [x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] at h01 h21 h31
    subst h01 h21
    simp at h31
    subst h31
    refine mem_X₃sub.2 ⟨a₃, ?_⟩
    rw [e, x₂Mat_zero, x₄Mat_zero, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨a, hxm⟩ := mem_X₃sub.1 hx
    rw [mem_map_vSU, show x = x₃SU a from ext_mat hxm, vSU_conj_x₃SU]
    exact X₃sub_le_A₁sub (x₃SU_mem _)

theorem map_uSU_X₃sub : X₃sub.map (MulAut.conj uSU).toMonoidHom = X₂sub := by
  ext x
  rw [mem_map_uSU]
  constructor
  · intro h
    obtain ⟨a, hm⟩ := mem_X₃sub.1 h
    have e : uSU * (uSU * x * uSU) * uSU = x := by
      rw [show uSU * (uSU * x * uSU) * uSU = (uSU * uSU) * x * (uSU * uSU) by group,
        uSU_mul_self, one_mul, mul_one]
    rw [← e, show uSU * x * uSU = x₃SU a from ext_mat hm, uSU_conj_x₃SU]
    exact x₂SU_mem a
  · intro h
    obtain ⟨a, hm⟩ := mem_X₂sub.1 h
    have e : x = uSU * x₃SU a * uSU := by
      rw [uSU_conj_x₃SU]
      exact ext_mat (by rw [hm, mat_x₂SU])
    rw [e, show uSU * (uSU * x₃SU a * uSU) * uSU = x₃SU a by
      rw [show uSU * (uSU * x₃SU a * uSU) * uSU = (uSU * uSU) * x₃SU a * (uSU * uSU) by group,
        uSU_mul_self, one_mul, mul_one]]
    exact x₃SU_mem a

theorem mat_e₁e₂ : mat (e₁SU * e₂SU) =
    Matrix.diagonal ![F4.ω, F4.ω * F4.ω, 1, F4.ω * F4.ω, F4.ω] := by
  rw [mat_mul, mat_e₁SU, mat_e₂SU, e₁Mat, e₂Mat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp only [bar_apply] <;> decide

theorem e₁e₂_comm_zSU : e₁SU * e₂SU * zSU = zSU * (e₁SU * e₂SU) :=
  ext_mat (by rw [mat_mul, mat_e₁e₂, mat_mul, mat_e₁e₂, mat_zSU]; decide)

theorem mat_e₁e₂_inv : mat (e₁SU * e₂SU)⁻¹ =
    Matrix.diagonal ![F4.ω * F4.ω, F4.ω, 1, F4.ω, F4.ω * F4.ω] :=
  mat_inv_eq (by rw [mat_e₁e₂]; decide)

theorem x₂_e₁e₂_check : ∀ a : F4, x₂Mat a = x₂Mat (F4.ω * a) *
    Matrix.diagonal ![F4.ω, F4.ω * F4.ω, 1, F4.ω * F4.ω, F4.ω] * x₂Mat (F4.ω * a) *
      Matrix.diagonal ![F4.ω * F4.ω, F4.ω, 1, F4.ω, F4.ω * F4.ω] := by
  unfold x₂Mat
  simp only [bar_apply]
  decide

theorem x₃_e₁e₂_check : ∀ a : F4, x₃Mat a = x₃Mat (F4.ω * a) *
    Matrix.diagonal ![F4.ω, F4.ω * F4.ω, 1, F4.ω * F4.ω, F4.ω] * x₃Mat (F4.ω * a) *
      Matrix.diagonal ![F4.ω * F4.ω, F4.ω, 1, F4.ω, F4.ω * F4.ω] := by
  unfold x₃Mat
  simp only [bar_apply]
  decide

theorem x₄_e₁e₂_check : ∀ a d : F4,
    F4.ω * F4.ω * a * bar (F4.ω * F4.ω * a) = d + bar d →
    x₄Mat (F4.ω * F4.ω * a) d * Matrix.diagonal ![F4.ω, F4.ω * F4.ω, 1, F4.ω * F4.ω, F4.ω] *
      x₄Mat (F4.ω * F4.ω * a) (d + F4.ω * F4.ω * a * bar (F4.ω * F4.ω * a)) *
      Matrix.diagonal ![F4.ω * F4.ω, F4.ω, 1, F4.ω, F4.ω * F4.ω] =
    x₄Mat a (F4.ω * a * bar a) := by
  unfold x₄Mat
  simp only [bar_apply]
  decide

theorem commutator_A₁sub_zpowers_e₁e₂ : ⁅A₁sub, zpowers (e₁SU * e₂SU)⁆ = A₁sub := by
  have hez : e₁SU * e₂SU * zSU = zSU * (e₁SU * e₂SU) := e₁e₂_comm_zSU
  have hKA : ⁅A₁sub, zpowers (e₁SU * e₂SU)⁆ ≤ A₁sub := by
    rw [commutator_le]
    intro a ha g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    have hgz : (e₁SU * e₂SU) ^ k * zSU = zSU * (e₁SU * e₂SU) ^ k :=
      (Commute.zpow_left (hez : Commute (e₁SU * e₂SU) zSU) k).eq
    rw [show ⁅a, (e₁SU * e₂SU) ^ k⁆ = a * ((e₁SU * e₂SU) ^ k * a⁻¹ * ((e₁SU * e₂SU) ^ k)⁻¹) by
      rw [commutatorElement_def]
      group]
    exact mul_mem ha (conj_mem_A₁sub_of_comm_z hgz (inv_mem ha))
  set K := ⁅A₁sub, zpowers (e₁SU * e₂SU)⁆ with hK
  have hcomm : ∀ {g : SU52}, g ∈ A₁sub → ⁅g, e₁SU * e₂SU⁆ ∈ K := fun hg =>
    commutator_mem_commutator hg (mem_zpowers _)
  have hmat : ∀ g : SU52, mat ⁅g, e₁SU * e₂SU⁆ =
      mat g * mat (e₁SU * e₂SU) * mat g⁻¹ * mat (e₁SU * e₂SU)⁻¹ := fun g => by
    rw [commutatorElement_def, mat_mul, mat_mul, mat_mul]
  have hX₂ : X₂sub ≤ K := fun x hx => by
    obtain ⟨a, hm⟩ := mem_X₂sub.1 hx
    have e : x = ⁅x₂SU (F4.ω * a), e₁SU * e₂SU⁆ := ext_mat (by
      rw [hmat, mat_x₂SU, mat_inv_of_x₂ (mat_x₂SU _), mat_e₁e₂, mat_e₁e₂_inv, hm]
      exact x₂_e₁e₂_check a)
    rw [e]
    exact hcomm (X₂sub_le_A₁sub (x₂SU_mem _))
  have hX₃ : X₃sub ≤ K := fun x hx => by
    obtain ⟨a, hm⟩ := mem_X₃sub.1 hx
    have e : x = ⁅x₃SU (F4.ω * a), e₁SU * e₂SU⁆ := ext_mat (by
      rw [hmat, mat_x₃SU, mat_inv_of_x₃ (mat_x₃SU _), mat_e₁e₂, mat_e₁e₂_inv, hm]
      exact x₃_e₁e₂_check a)
    rw [e]
    exact hcomm (X₃sub_le_A₁sub (x₃SU_mem _))
  have hz : zSU ∈ K := by
    rw [show zSU = ⁅x₂SU 1, x₃SU F4.ω⁆ from commutator_x₂_x₃_eq.symm, commutatorElement_def]
    have h2 := hX₂ (x₂SU_mem 1)
    have h3 := hX₃ (x₃SU_mem F4.ω)
    exact mul_mem (mul_mem (mul_mem h2 h3) (inv_mem h2)) (inv_mem h3)
  have hZ : ZX₄sub ≤ K := fun w hw => by
    obtain ⟨a, b, ha, hwm⟩ := mem_x₄Sub.1 hw
    subst ha
    rcases eq_zero_or_one_of_valid b (x₄_coord_rel hwm) with rfl | rfl
    · rw [show w = 1 from ext_mat (by rw [hwm, x₄Mat_zero, mat_one])]
      exact one_mem _
    · rw [show w = zSU from ext_mat (by rw [hwm, mat_zSU])]
      exact hz
  have hX₄ : X₄sub ≤ K := fun x hx => by
    obtain ⟨a, b, hm⟩ := mem_X₄sub.1 hx
    obtain ⟨d, hd⟩ := exists_valid (F4.ω * F4.ω * a)
    set c := ⁅x₄SU (F4.ω * F4.ω * a) d hd, e₁SU * e₂SU⁆ with hc
    have hcm : mat c = x₄Mat a (F4.ω * a * bar a) := by
      rw [hc, hmat, mat_x₄SU, mat_inv_of_x₄ (mat_x₄SU _ _ hd), mat_e₁e₂, mat_e₁e₂_inv]
      exact x₄_e₁e₂_check a d hd
    have hw : c⁻¹ * x ∈ ZX₄sub := by
      refine mem_x₄Sub.2 ⟨a + a, F4.ω * a * bar a + a * bar a + b + bar a * a,
        CharTwo.add_self_eq_zero a, ?_⟩
      rw [mat_mul, mat_inv_of_x₄ hcm, hm, x₄Mat_mul]
    rw [show x = c * (c⁻¹ * x) by group]
    exact mul_mem (hcomm (X₄sub_le_A₁sub' (x₄SU_mem _ _ _))) (hZ hw)
  exact le_antisymm hKA (sup_le (sup_le hX₂ hX₃) hX₄)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
