module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Module QuadraticMap CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G]

theorem polar_map_O (S : Setting G) (φ : S.O) (x y : S.Qt) :
    polar S.q ((φ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) ((φ : S.Qt ≃ₗ[ZMod 2] S.Qt) y) = polar S.q x y := by
  have h := fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 φ.2 v
  simp only [polar, ← map_add, h]

theorem eq_one_of_fix_perp (S : Setting G) {φ : S.O} {w : S.Qt} (hw0 : w ≠ 0) (hw : S.q w = 0)
    (hfix : ∀ v, polar S.q v w = 0 → (φ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : φ = 1 := by
  classical
  have hB : ∀ x y, S.q.polarBilin x y = polar S.q x y := fun _ _ => rfl
  have hsymm : ∀ x y, polar S.q x y = polar S.q y x := fun x y => polar_comm _ x y
  set P : Submodule (ZMod 2) S.Qt := Submodule.span (ZMod 2) {w}
  have hPdim : finrank (ZMod 2) P = 1 := finrank_span_singleton hw0
  have hPP : LinearMap.BilinForm.orthogonal S.q.polarBilin (LinearMap.BilinForm.orthogonal S.q.polarBilin P) = P := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · intro x hx y hy
      show S.q.polarBilin y x = 0
      rw [hB, hsymm]
      exact hy x hx
    · rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate,
        LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, hPdim]
      have : 1 ≤ finrank (ZMod 2) S.Qt := hPdim ▸ Submodule.finrank_le P
      omega
  have hmemPerp : ∀ v, polar S.q v w = 0 → v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin P := by
    intro v hv y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    show S.q.polarBilin (c • w) v = 0
    rw [map_smul, LinearMap.smul_apply, hB, hsymm, hv, smul_zero]
  have hd : ∀ u, (φ : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ P := by
    intro u
    rw [← hPP]
    intro x hx
    show S.q.polarBilin x ((φ : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) = 0
    have hxw : polar S.q x w = 0 := by
      have := hx w (Submodule.mem_span_singleton_self w)
      rwa [hB, hsymm] at this
    rw [map_sub, hB, hB]
    have h1 : polar S.q x ((φ : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
        polar S.q ((φ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) ((φ : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
      rw [hfix x hxw]
    rw [h1, polar_map_O, sub_self]
  have hq : ∀ v, S.q ((φ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = S.q v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 φ.2 v
  have hall : ∀ u, (φ : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    intro u
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hd u)
    have hφu : (φ : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + c • w := by rw [hc]; abel
    by_cases hu : polar S.q u w = 0
    · exact hfix u hu
    · have hc0 : c = 0 := by
        by_contra hc1
        have hc1' : c = 1 := by
          rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) c with h | h
          · exact absurd h hc1
          · exact h
        have h1 := hq u
        rw [hφu, hc1', one_smul, QuadraticMap.map_add (⇑S.q) u w, hw, add_zero] at h1
        exact hu (by simpa using h1)
      rw [hφu, hc0, zero_smul, add_zero]
  exact Subtype.ext (LinearEquiv.ext hall)

theorem ncard_le_of_pairwise_polar (S : Setting G) {A : Set S.Qt} (h0 : (0 : S.Qt) ∉ A)
    (hA : ∀ x ∈ A, ∀ y ∈ A, polar S.q x y = 0) : A.ncard ≤ 2 ^ S.width - 1 := by
  classical
  set W : Submodule (ZMod 2) S.Qt := Submodule.span (ZMod 2) A
  have hAW : A ⊆ W := Submodule.subset_span
  have hW : W ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W := by
    refine Submodule.span_le.mpr fun x hx => ?_
    show ∀ y ∈ W, S.q.polarBilin y x = 0
    intro y hy
    have hker : W ≤ LinearMap.ker (S.q.polarBilin.flip x) :=
      Submodule.span_le.mpr fun y' hy' => by
        show S.q.polarBilin y' x = 0
        exact hA y' hy' x hx
    exact hker hy
  have hdim : finrank (ZMod 2) W ≤ S.width := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
    have h2 := Submodule.finrank_mono hW
    rw [S.finrank_Qt_eq_two_mul_width] at h1
    omega
  have hsub : A ⊆ (W : Set S.Qt) \ {0} := fun x hx => ⟨hAW hx, fun h => h0 (h ▸ hx)⟩
  calc A.ncard ≤ ((W : Set S.Qt) \ {0}).ncard := Set.ncard_le_ncard hsub
    _ = (W : Set S.Qt).ncard - 1 := Set.ncard_diff_singleton_of_mem W.zero_mem
    _ = 2 ^ finrank (ZMod 2) W - 1 := by
        rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, S.card_submodule]
    _ ≤ 2 ^ S.width - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hdim) 1

end CFSG.GF2Type.Smith1979.IdxFour
