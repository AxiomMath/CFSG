module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSFour
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckS
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada
open scoped commutatorElement

theorem vSU_conj_mem_Fsub {f : SU52} (hf : f ∈ Fsub) : vSU * f * vSU⁻¹ ∈ Fsub := by
  have hA := vSU_conj_mem_A₂sub (Fsub_le_A₂sub hf)
  obtain ⟨-, h21, h10, h20⟩ := mem_Fsub.1 hf
  have hm : mat (vSU * f * vSU⁻¹) = vMat * mat f * vMat := by
    rw [mat_mul, mat_mul, mat_vSU, mat_inv_vSU]
  obtain ⟨hS, -⟩ := mem_A₂sub.1 hA
  obtain ⟨hl, -⟩ := mem_Ssub.1 (A₂sub_le_Ssub (Fsub_le_A₂sub hf))
  refine mem_Fsub.2 ⟨hS, ?_, ?_, ?_⟩ <;> rw [hm, vMat_conj_apply]
  · exact h20
  · exact hl 0 1 (by decide)
  · exact h21

theorem mem_Fsub_of_mem_commutator_of_conj_vSU {x : SU52} (hx : x ∈ ⁅Ssub, Ssub⁆)
    (hv : vSU * x * vSU⁻¹ ∈ ⁅Ssub, Ssub⁆) : x ∈ Fsub := by
  rw [commutator_Ssub, mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff] at hx hv
  obtain ⟨hxS, h21, h10⟩ := hx
  have h20 := hv.2.1
  rw [mat_mul, mat_mul, mat_vSU, mat_inv_vSU, vMat_conj_apply] at h20
  exact mem_Fsub.2 ⟨hxS, h21, h10, h20⟩

theorem commutator_Ssub_inf_comap_vSU :
    ⁅Ssub, Ssub⁆ ⊓ (⁅Ssub, Ssub⁆ : Subgroup SU52).comap (MulAut.conj vSU).toMonoidHom = Fsub := by
  refine le_antisymm (fun x hx => mem_Fsub_of_mem_commutator_of_conj_vSU (mem_inf.1 hx).1
    (mem_inf.1 hx).2) (le_inf Fsub_le_commutator_Ssub fun f hf => ?_)
  exact Fsub_le_commutator_Ssub (vSU_conj_mem_Fsub hf)

theorem vSU_inv : vSU⁻¹ = vSU :=
  inv_eq_of_mul_eq_one_right (ext_mat (by rw [mat_mul, mat_vSU, mat_one]; decide))

theorem commutator_Ssub_inf_map_vSU :
    ⁅Ssub, Ssub⁆ ⊓ (⁅Ssub, Ssub⁆ : Subgroup SU52).map (MulAut.conj vSU).toMonoidHom = Fsub := by
  rw [← commutator_Ssub_inf_comap_vSU]
  congr 1
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, MulAut.conj_symm_apply]
  change vSU⁻¹ * x * vSU ∈ _ ↔ vSU * x * vSU⁻¹ ∈ _
  rw [vSU_inv]

theorem mem_X₂sub_sup_Fsub_iff {x : SU52} :
    x ∈ X₂sub ⊔ Fsub ↔ x ∈ Ssub ∧ mat x 2 1 = 0 ∧ mat x 2 0 = 0 := by
  constructor
  · intro hx
    let T : Subgroup SU52 :=
      { carrier := {g | g ∈ Ssub ∧ mat g 2 1 = 0 ∧ mat g 2 0 = 0}
        mul_mem' := fun {g h} ⟨hg, hg1, hg0⟩ ⟨hh, hh1, hh0⟩ =>
          ⟨mul_mem hg hh, by rw [mat_mul_two_one hg hh, hg1, hh1, add_zero],
            by rw [mat_mul_two_zero hg hh, hg0, hg1, hh0, zero_mul, add_zero, add_zero]⟩
        one_mem' := ⟨one_mem _, rfl, rfl⟩
        inv_mem' := fun {g} ⟨hg, hg1, hg0⟩ => by
          have hi1 := inv_entry_eq_zero (by decide) (mat_mul_two_one hg (inv_mem hg)) hg1
          refine ⟨inv_mem hg, hi1, inv_entry_eq_zero (by decide) ?_ hg0⟩
          rw [mat_mul_two_zero hg (inv_mem hg), hg1, zero_mul, add_zero] }
    have hle : X₂sub ⊔ Fsub ≤ T := by
      refine sup_le (fun g hg => ?_) fun g hg => ⟨(mem_Fsub.1 hg).1, (mem_Fsub.1 hg).2.1,
        (mem_Fsub.1 hg).2.2.2⟩
      obtain ⟨a, hgm⟩ := mem_X₂sub.1 hg
      exact ⟨X₂sub_le_Ssub hg, by rw [hgm]; rfl, by rw [hgm]; rfl⟩
    exact hle hx
  · rintro ⟨hx, h21, h20⟩
    obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, -, k₁, -, k₄⟩ :=
      exists_eq_nf_coord hx
    rw [h21] at k₁
    rw [← k₁, zero_mul, zero_add] at k₄
    rw [h20] at k₄
    rw [← k₁] at e₁
    rw [← k₄] at e₄
    have h₁ : g₁ ∈ Fsub := mem_sup_left (mem_sup_left (mem_x₁Sub.2 ⟨0, b₁, rfl, e₁⟩))
    have h₂ : g₂ ∈ X₂sub := mem_X₂sub.2 ⟨a₂, e₂⟩
    have h₃ : g₃ ∈ Fsub := mem_sup_left (mem_sup_right (mem_X₃sub.2 ⟨a₃, e₃⟩))
    have h₄ : g₄ ∈ Fsub := mem_sup_right (mem_x₄Sub.2 ⟨0, b₄, rfl, e₄⟩)
    exact mul_mem (mul_mem (mul_mem (mem_sup_right h₁) (mem_sup_left h₂)) (mem_sup_right h₃))
      (mem_sup_right h₄)

theorem mat_conj_e₂ (x : SU52) (i j : Fin 5) :
    mat (e₂SU * x * e₂SU⁻¹) i j = (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) i *
      mat x i j * ((![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) j)⁻¹ := by
  have hd : ∀ i, (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simp only [bar_apply] <;> decide
  exact mat_conj_diag hd (by rw [mat_e₂SU, e₂Mat]) i j

theorem Ssub_inf_centralizer_e₂SU :
    Ssub ⊓ centralizer ({e₂SU} : Set SU52) = X₂sub ⊔ Fsub := by
  refine le_antisymm (fun s hs => ?_) (le_inf (sup_le X₂sub_le_Ssub (Fsub_le_A₂sub.trans
    A₂sub_le_Ssub)) (sup_le (fun x hx => ?_) fun f hf => ?_))
  · obtain ⟨hsS, hsC⟩ := mem_inf.1 hs
    have hc : e₂SU * s * e₂SU⁻¹ = s := by
      rw [← mem_centralizer_singleton_iff.1 hsC, mul_inv_cancel_right]
    have e21 := mat_conj_e₂ s 2 1
    have e20 := mat_conj_e₂ s 2 0
    rw [hc] at e21 e20
    change mat s 2 1 = bar F4.ω * mat s 2 1 * F4.ω⁻¹ at e21
    change mat s 2 0 = bar F4.ω * mat s 2 0 * F4.ω⁻¹ at e20
    have key : ∀ t : F4, t = bar F4.ω * t * F4.ω⁻¹ → t = 0 := by
      simp only [bar_apply]
      decide
    exact mem_X₂sub_sup_Fsub_iff.2 ⟨hsS, key _ e21, key _ e20⟩
  · obtain ⟨a, hxm⟩ := mem_X₂sub.1 hx
    refine mem_centralizer_singleton_iff.2 (ext_mat ?_)
    rw [mat_mul, mat_mul, hxm, mat_e₂SU]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e₂Mat, x₂Mat, Matrix.mul_apply, Matrix.diagonal, bar_apply] <;>
      ring
  · exact mem_centralizer_singleton_iff.2 (e₂SU_comm_Fsub hf).symm

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
