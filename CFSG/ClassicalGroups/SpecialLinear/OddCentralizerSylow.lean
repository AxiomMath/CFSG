module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem odd_centralizer_sylow_le_center (hm : 2 ≤ m)
    (U : Sylow 2 (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {x : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hxodd : Odd (orderOf x))
    (hxc : x ∈ Subgroup.centralizer
      ((U : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) : Set _)) :
    x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
  classical
  let n := m + 1
  let S := Matrix.SpecialLinearGroup (Fin n) F
  have hn : 2 ≤ n := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) (p := 2) (n := n) (by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P₀ U
  have hg' : P₀ = g⁻¹ • U := by
    rw [← hg, inv_smul_smul]
  have hmem : ∀ u : S, u ∈ unitriangular n F ↔ g * u * g⁻¹ ∈ (U : Subgroup S) := by
    intro u
    rw [← hP₀, hg', Sylow.coe_subgroup_smul]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_apply]
  let y : S := g⁻¹ * (x : S) * g
  have himg : (MulAut.conj g⁻¹).toMonoidHom '' ((U : Subgroup S) : Set S) =
      ((unitriangular n F : Subgroup S) : Set S) := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : v ∈ (U : Subgroup S) := hv
      refine (hmem ((MulAut.conj g⁻¹) v)).mpr ?_
      simpa [MulAut.conj_apply, mul_assoc] using hv'
    · intro hu
      refine ⟨g * u * g⁻¹, (hmem u).mp hu, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hyc : y ∈ Subgroup.centralizer ((unitriangular n F : Subgroup S) : Set S) := by
    have hmap := Subgroup.map_centralizer_le_centralizer_image
      ((U : Subgroup S) : Set S) (MulAut.conj g⁻¹).toMonoidHom
    have hy : y ∈ (Subgroup.centralizer ((U : Subgroup S) : Set S)).map
        (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨(x : S), hxc, by simp [y, MulAut.conj_apply, mul_assoc]⟩
    exact himg ▸ hmap hy
  have hM : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) →
      (y : Matrix (Fin n) (Fin n) F) * single i j (1 : F) =
        single i j (1 : F) * (y : Matrix (Fin n) (Fin n) F) := by
    intro i j hij
    have hlt : i < j := by
      rw [Fin.lt_def]
      omega
    have hmemU : Matrix.SpecialLinearGroup.transvection hlt.ne (1 : F) ∈ unitriangular n F :=
      CFSG.QuasithinUnique.K1.transvection_mem_unitriangular hlt 1
    have hcomm := (Subgroup.mem_centralizer_iff.mp hyc)
      (Matrix.SpecialLinearGroup.transvection hlt.ne (1 : F)) hmemU
    have h' : (1 + single i j (1 : F) : Matrix (Fin n) (Fin n) F) *
        (y : Matrix (Fin n) (Fin n) F) =
        (y : Matrix (Fin n) (Fin n) F) * (1 + single i j (1 : F)) := by
      have h := congrArg (fun z : S => (z : Matrix (Fin n) (Fin n) F)) hcomm
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe] at h
      exact h
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at h'
    exact (add_left_cancel h').symm
  obtain ⟨a, b, hab⟩ :=
    CFSG.QuasithinUnique.K1.eq_smul_one_add_single_of_commute (n := n) hn
      (y : Matrix (Fin n) (Fin n) F) hM
  have hyconj : y = (MulAut.conj g⁻¹) (x : S) := by
    simp only [y, MulAut.conj_apply]
    simp [mul_assoc]
    exact (inv_inv g).symm
  have hyodd : Odd (orderOf y) := by
    rw [hyconj, MulEquiv.orderOf_eq]
    exact hxodd
  obtain ⟨k, hk⟩ := hyodd
  have hypow : y ^ (2 * k + 1) = 1 := by
    simpa [hk] using pow_orderOf_eq_one y
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨n - 1, by omega⟩
  have hi₁₀ : i₁ ≠ i₀ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [i₁, i₀] at hv
    omega
  have hN2 : (single i₀ i₁ (1 : F) : Matrix (Fin n) (Fin n) F) *
      single i₀ i₁ (1 : F) = 0 := by
    simp [hi₁₀]
  have hsq : (y : Matrix (Fin n) (Fin n) F) ^ 2 = (a ^ 2) • 1 := by
    simp only [i₀, i₁] at hN2
    rw [hab, pow_two]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      smul_smul, hN2, smul_zero, add_zero]
    have h2b : a * b + b * a = 0 := by
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      rw [mul_comm b a, ← two_mul, h2, zero_mul]
    rw [show (a * a) • 1 + (b * a) • single i₀ i₁ (1 : F) +
        (a * b) • single i₀ i₁ (1 : F) =
        (a * a) • 1 + ((b * a) • single i₀ i₁ (1 : F) +
          (a * b) • single i₀ i₁ (1 : F)) by abel]
    rw [← add_smul, add_comm (b * a) (a * b), h2b, zero_smul, add_zero, pow_two]
  have hgroup : y ^ (2 * (k + 1)) = y := by
    have h : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h, pow_succ, hypow, one_mul]
  have hy_scalar : (y : Matrix (Fin n) (Fin n) F) = ((a ^ 2) ^ (k + 1)) • 1 := by
    have hmat : (y : Matrix (Fin n) (Fin n) F) ^ (2 * (k + 1)) =
        (y : Matrix (Fin n) (Fin n) F) := by
      have h := congrArg (fun z : S => (z : Matrix (Fin n) (Fin n) F)) hgroup
      rwa [Matrix.SpecialLinearGroup.coe_pow] at h
    rw [← hmat, pow_mul, hsq]
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_pow, Matrix.smul_one_eq_diagonal]
    congr 1
  have hycenter : y ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hmat : (z : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F) =
        (y : Matrix (Fin n) (Fin n) F) * (z : Matrix (Fin n) (Fin n) F) := by
      rw [hy_scalar]
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
    exact Subtype.ext hmat
  have hxeq : x = g * y * g⁻¹ := by
    have h : (MulAut.conj g) y = (x : S) := by
      rw [hyconj]
      simp [MulAut.conj_apply, mul_assoc]
    simpa [MulAut.conj_apply] using h.symm
  have hxcenter : x ∈ Subgroup.center S := by
    rw [hxeq]
    exact (inferInstance : (Subgroup.center S).Normal).conj_mem y hycenter g
  exact hxcenter

end CFSG.ClassicalGroups.SpecialLinear
