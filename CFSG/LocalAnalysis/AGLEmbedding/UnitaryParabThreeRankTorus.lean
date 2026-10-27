module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUOddK

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits

theorem shortTorusFun_lowIdx_apply {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}
    {j : Fin (n / 2)} (hj : j.val + 1 < n / 2) (x : F) {i : ℕ} (hi : i < n / 2) :
    shortTorusFun σ (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) x ⟨i, by omega⟩ =
      if i = j.val then x else if i = j.val + 1 then x⁻¹ else 1 := by
  have h1 : (⟨i, by omega⟩ : Fin n) ≠ Fin.rev (lowIdx j) := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_rev, val_lowIdx] at this
    omega
  have h2 : (⟨i, by omega⟩ : Fin n) ≠ Fin.rev (lowIdx ⟨j.val + 1, hj⟩) := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_rev, val_lowIdx] at this
    omega
  simp only [shortTorusFun, h1, h2, Fin.ext_iff, val_lowIdx, ite_false]

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

omit [Finite F] [CharP F 2] in
theorem mat_shortTorus_lowIdx {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {j : Fin (n / 2)}
    (hj : j.val + 1 < n / 2) (u : Fˣ) :
    mat σ n (shortTorus σ hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _)
      (u : F)) = diagonal (shortTorusFun σ (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) (u : F)) :=
  coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) u.ne_zero

noncomputable def torusFourElt (hσ : ∀ c, unitaryInvolution F 2 1 (unitaryInvolution F 2 1 c) = c)
    (hn : 12 ≤ n) (c : Fin 4 → Fˣ) : SU (unitaryInvolution F 2 1) n :=
  shortTorus (unitaryInvolution F 2 1) hσ (lowIdx_ne_succ (k := ⟨0, by omega⟩) (by simp; omega))
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (c 0 : F) *
    shortTorus (unitaryInvolution F 2 1) hσ (lowIdx_ne_succ (k := ⟨1, by omega⟩) (by simp; omega))
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (c 1 : F) *
    shortTorus (unitaryInvolution F 2 1) hσ (lowIdx_ne_succ (k := ⟨2, by omega⟩) (by simp; omega))
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (c 2 : F) *
    shortTorus (unitaryInvolution F 2 1) hσ (lowIdx_ne_succ (k := ⟨3, by omega⟩) (by simp; omega))
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (c 3 : F)

include hF in
theorem pow_four_le_card_map_torus_su (hn : 12 ≤ n) {W : Type*} [Group W] [Finite W]
    {π : SU (unitaryInvolution F 2 1) n →* W}
    (hker : π.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n)) :
    3 ^ 4 ≤ Nat.card ((⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i).map π) := by
  have hσ := unitaryInvolution_involutive hF
  set P := torusFourElt (F := F) hσ hn with hP
  have hPT : ∀ c, P c ∈ ⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i := fun c =>
    mul_mem (mul_mem (mul_mem
      (Subgroup.mem_iSup_of_mem _ (shortTorus_mem_levelTorus hσ _ _))
      (Subgroup.mem_iSup_of_mem _ (shortTorus_mem_levelTorus hσ _ _)))
      (Subgroup.mem_iSup_of_mem _ (shortTorus_mem_levelTorus hσ _ _)))
      (Subgroup.mem_iSup_of_mem _ (shortTorus_mem_levelTorus hσ _ _))
  set Φ : (Fin 4 → Fˣ) → ((⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i).map π) :=
    fun c => ⟨π (P c), P c, hPT c, rfl⟩ with hΦ
  have hinj : Function.Injective Φ := by
    intro c c' h
    have h1 : π ((P c')⁻¹ * P c) = 1 := by
      have h' := congrArg Subtype.val h
      simp only [hΦ] at h'
      rw [map_mul, map_inv, h', inv_mul_cancel]
    obtain ⟨u, hu⟩ := exists_scalar_eq_mat_of_mem_center hF (by omega)
      (fun h => by simp at h; omega) (hker h1)
    have hm : mat _ n (P c) = mat _ n (P c') * Matrix.scalar (Fin n) u := by
      rw [← hu, ← map_mul, mul_inv_cancel_left]
    simp only [hP, torusFourElt, map_mul, mat_shortTorus_lowIdx, Matrix.scalar_apply,
      diagonal_mul_diagonal] at hm
    have hd := diagonal_injective hm
    have e5 := congrFun hd ⟨5, by omega⟩
    have e0 := congrFun hd ⟨0, by omega⟩
    have e1 := congrFun hd ⟨1, by omega⟩
    have e2 := congrFun hd ⟨2, by omega⟩
    have e3 := congrFun hd ⟨3, by omega⟩
    simp (disch := omega) only [shortTorusFun_lowIdx_apply] at e5 e0 e1 e2 e3
    norm_num at e5 e0 e1 e2 e3
    subst e5
    simp only [mul_one] at e0 e1 e2 e3
    have k1 : (c 1 : F) = c' 1 := by
      rw [e0] at e1
      exact mul_left_cancel₀ (inv_ne_zero (c' 0).ne_zero) e1
    have k2 : (c 2 : F) = c' 2 := by
      rw [k1] at e2
      exact mul_left_cancel₀ (inv_ne_zero (c' 1).ne_zero) e2
    have k3 : (c 3 : F) = c' 3 := by
      rw [k2] at e3
      exact mul_left_cancel₀ (inv_ne_zero (c' 2).ne_zero) e3
    funext j
    fin_cases j
    · exact Units.ext e0
    · exact Units.ext k1
    · exact Units.ext k2
    · exact Units.ext k3
  have hcard : Nat.card (Fin 4 → Fˣ) = 3 ^ 4 := by
    rw [Nat.card_fun, Nat.card_units, hF, Nat.card_fin]
    norm_num
  calc 3 ^ 4 = Nat.card (Fin 4 → Fˣ) := hcard.symm
    _ ≤ _ := Nat.card_le_card_of_injective Φ hinj

end CFSG.AGLEmbedding
