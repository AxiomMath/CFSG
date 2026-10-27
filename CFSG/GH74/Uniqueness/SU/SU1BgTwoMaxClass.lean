module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.GH74.Uniqueness.SU.SU1MaxClassShape

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

theorem nonempty_mulEquiv_semidihedral {P : Type} [Group P] [Finite P] {n : ℕ} (hn : 4 ≤ n)
    (hP : Nat.card P = 2 ^ n) {a y : P} (ha1 : a ^ (2 ^ (n - 1)) = 1) (hy2 : y * y = 1)
    (hconj : y * a * y⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, y} : Set P) = ⊤) :
    Nonempty (P ≃* CFSG.Open.SemidihedralGroup n) := by
  have hn3 : 3 ≤ n := by omega
  have := CFSG.Semidihedral.presentation_finite n hn3
  let φ : CFSG.Open.SemidihedralGroup n →* P :=
    PresentedGroup.toGroup (f := ![a, y]) (by
      intro w hw
      simp only [CFSG.Open.semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero] using ha1
      · have hy2' : y ^ 2 = 1 := by rw [pow_two]; exact hy2
        simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
          Matrix.cons_val_zero] using hy2'
      · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        rw [hconj, mul_inv_cancel])
  have hφa : φ (PresentedGroup.of 0) = a := PresentedGroup.toGroup.of _
  have hφy : φ (PresentedGroup.of 1) = y := PresentedGroup.toGroup.of _
  have hsurj : Function.Surjective φ := by
    have hle : Subgroup.closure ({a, y} : Set P) ≤ φ.range := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact ⟨PresentedGroup.of 0, hφa⟩
      · exact ⟨PresentedGroup.of 1, hφy⟩
    rw [hgen] at hle
    intro g
    exact (eq_top_iff.mpr hle ▸ Subgroup.mem_top g : g ∈ φ.range)
  have hcard : Nat.card (CFSG.Open.SemidihedralGroup n) ≤ Nat.card P := by
    rw [CFSG.Semidihedral.card n hn3, hP]
  exact ⟨(MulEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le hcard)).symm⟩

theorem b_two_maximalClass_shape : CFSG.GH74.GLS.Bg.B_two_maximalClass_shape := by
  intro P _ _ hP h8 m hm hγ
  have hn : 4 ≤ m := by
    by_contra hcon
    have : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right two_pos (by omega)
    omega
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hcl : m - 1 ≤ Group.nilpotencyClass P := by
    by_contra hcon
    apply hγ
    rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
    omega
  obtain ⟨a, y, ha, hy, hgen, hD | hQ | hSD⟩ := exists_shape_of_maxClass hn hm hcl
  · left
    refine ⟨m - 1, by omega, ?_⟩
    have hgen' : ⊤ = zpowers a ⊔ zpowers y := by
      rw [← hgen, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        ← Subgroup.closure_union]
      rfl
    have := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem a y hgen'
      (by rw [pow_two]; exact hD.1) hD.2 hy
    rwa [ha] at this
  · right; left
    refine ⟨m - 2, by omega, ?_⟩
    have hm2 : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    obtain ⟨e, -⟩ := (CFSG.Semidihedral.Local.quaternion_normal_form_isomorphism
      (m := 2 ^ (m - 2)) Nat.one_le_two_pow hgen (by rw [hm2]; exact ha) hy
      (by rw [pow_two]; exact hQ.1) hQ.2).1
    exact ⟨e.symm⟩
  · right; right
    refine ⟨m, hn, ?_⟩
    exact nonempty_mulEquiv_semidihedral hn hm (by rw [← ha]; exact pow_orderOf_eq_one a)
      hSD.1 hSD.2 hgen

theorem ig10_25 : CFSG.GH74.GLS.Bg.B_two_maximalClass_shape := b_two_maximalClass_shape

end CFSG.GH74.Uniqueness.SU.SU1
