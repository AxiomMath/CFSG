module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofULevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviInner
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

section Proj

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ}

omit [CharP K 2] in
theorem glAut_refl (g : GL (Fin (2 + k)) K) : glAut (RingEquiv.refl K) g = g :=
  Units.ext (by rw [coe_glAut]; rfl)

theorem eq_one_of_sq_of_blk_diagonal (hk : 1 ≤ k) {A : GL (Fin (2 + k)) K}
    {α : MulAut (StatedProj (StatedSU (2 + k) (2 ^ f) K))}
    (hα : ∀ g : StatedSU (2 + k) (2 ^ f) K,
      ∃ hg : A * glAut (RingEquiv.refl K) (g : GL (Fin (2 + k)) K) * A⁻¹ ∈
        StatedSU (2 + k) (2 ^ f) K, α (uProj K (2 + k) f g) = uProj K (2 + k) f ⟨_, hg⟩)
    (h2 : α * α = 1) {a : K} {d : Fin k → K} (hA : A.val = blk (a • 1) (diagonal d)) :
    α = 1 := by
  have hsq : ∀ g : StatedSU (2 + k) (2 ^ f) K, g * g = 1 →
      A.val * A.val * (g : GL (Fin (2 + k)) K).val =
        (g : GL (Fin (2 + k)) K).val * (A.val * A.val) := by
    intro g hg2
    obtain ⟨hg1, hαg1⟩ := hα g
    obtain ⟨hg2', hαg2⟩ := hα ⟨_, hg1⟩
    have e0 : α (α (uProj K (2 + k) f g)) = uProj K (2 + k) f g := by
      rw [← MulAut.mul_apply, h2, MulAut.one_apply]
    rw [hαg1, hαg2] at e0
    have hgg : (g : GL (Fin (2 + k)) K) * g = 1 := by
      rw [← Subgroup.coe_mul, hg2, Subgroup.coe_one]
    have hinv : (⟨_, hg2'⟩ : StatedSU (2 + k) (2 ^ f) K) * ⟨_, hg2'⟩ = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_one, glAut_refl]
      calc A * (A * (g : GL (Fin (2 + k)) K) * A⁻¹) * A⁻¹ *
            (A * (A * (g : GL (Fin (2 + k)) K) * A⁻¹) * A⁻¹) =
          A * A * ((g : GL (Fin (2 + k)) K) * g) * A⁻¹ * A⁻¹ := by group
        _ = 1 := by rw [hgg, mul_one]; group
    have e1 := congrArg Subtype.val (eq_of_uProj_eq_of_mul_self (by omega) e0 hinv hg2)
    simp only [glAut_refl] at e1
    have e2 : A * A * (g : GL (Fin (2 + k)) K) = (g : GL (Fin (2 + k)) K) * (A * A) :=
      calc A * A * (g : GL (Fin (2 + k)) K) =
            A * (A * (g : GL (Fin (2 + k)) K) * A⁻¹) * A⁻¹ * (A * A) := by group
        _ = (g : GL (Fin (2 + k)) K) * (A * A) := by rw [e1]
    have e3 := congrArg Units.val e2
    simpa only [Units.val_mul] using e3
  have hd : ∀ j : Fin k, d j = a := by
    intro j
    obtain ⟨P, hP⟩ := exists_permMatrix_mem (K := K) (f := f)
      (Equiv.swap (finSumFinEquiv (Sum.inl (1 : Fin 2)) : Fin (2 + k)) (finSumFinEquiv (Sum.inr j)))
    have e := hsq P (mul_self_eq_one_of_val hP (permMatrix_swap_mul_self _ _))
    rw [hP] at e
    have e' := apply_eq_of_mul_permMatrix_swap e
    rw [hA, blk_mul, smul_one_mul_smul_one, diagonal_mul_diagonal, blk_apply_inl,
      blk_apply_inr] at e'
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      diagonal_apply_eq] at e'
    exact (eq_of_mul_self_eq e').symm
  have hAs : A.val = scalar (Fin (2 + k)) a := by
    rw [hA, scalar_eq_blk]
    congr 1
    rw [smul_one_eq_diagonal]
    congr 1
    funext j
    exact hd j
  ext x
  obtain ⟨g, rfl⟩ := uProj_surjective (K := K) (f := f) (2 + k) x
  obtain ⟨hg, hαg⟩ := hα g
  rw [hαg, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  simp only [glAut_refl]
  have hc : A * (g : GL (Fin (2 + k)) K) = (g : GL (Fin (2 + k)) K) * A :=
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, hAs]
      exact (scalar_commute a (fun _ => Commute.all _ _) _).eq)
  calc A * (g : GL (Fin (2 + k)) K) * A⁻¹ = (g : GL (Fin (2 + k)) K) * A * A⁻¹ := by rw [hc]
    _ = (g : GL (Fin (2 + k)) K) := by group

theorem eq_one_of_fixes_u_refl (hk : 2 ≤ k) {ζ : K} (hζ : ζ ^ 2 ^ f * ζ = 1) (hζ1 : ζ ≠ 1)
    {A : GL (Fin (2 + k)) K} {α : MulAut (StatedProj (StatedSU (2 + k) (2 ^ f) K))}
    (hα : ∀ g : StatedSU (2 + k) (2 ^ f) K,
      ∃ hg : A * glAut (RingEquiv.refl K) (g : GL (Fin (2 + k)) K) * A⁻¹ ∈
        StatedSU (2 + k) (2 ^ f) K, α (uProj K (2 + k) f g) = uProj K (2 + k) f ⟨_, hg⟩)
    (h2 : α * α = 1) (hW : ∀ w ∈ uBarW K k f, α w = w) (hL : ∀ l ∈ uBarL K k f, α l = l)
    {A₁ : Matrix (Fin 2) (Fin 2) K} {D : Matrix (Fin k) (Fin k) K} (hA : A.val = blk A₁ D) :
    α = 1 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨J, hJ⟩ := exists_swapM_mem (K := K) f
  obtain ⟨J', hJ'⟩ := exists_twJ_mem hζ
  have e1 := mul_eq_of_fix_uBarW hα hA hW (mul_self_eq_one_of_val hJ swapM_mul_swapM)
  have e2 := mul_eq_of_fix_uBarW hα hA hW (mul_self_eq_one_of_val hJ' (twJ_mul_twJ hζ0))
  rw [hJ] at e1
  rw [hJ'] at e2
  have hA₁ := eq_smul_one_of_commute_twJ hζ0 hζ1 e1 e2
  have hD := eq_smul_one_of_commute_statedSU hk hζ hζ1 (D := D) fun S =>
    (mul_eq_of_fix_uBarL hα hA hL S).symm
  refine eq_one_of_sq_of_blk_diagonal (by omega) hα h2 (a := A₁ 0 0)
    (d := fun _ => D ⟨0, by omega⟩ ⟨0, by omega⟩) ?_
  rw [hA, ← smul_one_eq_diagonal, ← hA₁, ← hD]

theorem false_of_fix_uBarL_bar (h : UnitaryFieldData 2 f K) (hk : 3 ≤ k) {ζ : K}
    (hζ : ζ ^ 2 ^ f * ζ = 1) (hζ1 : ζ ≠ 1) {τ : K ≃+* K} {A : GL (Fin (2 + k)) K}
    {α : MulAut (StatedProj (StatedSU (2 + k) (2 ^ f) K))}
    (hα : ∀ g : StatedSU (2 + k) (2 ^ f) K,
      ∃ hg : A * glAut τ (g : GL (Fin (2 + k)) K) * A⁻¹ ∈ StatedSU (2 + k) (2 ^ f) K,
        α (uProj K (2 + k) f g) = uProj K (2 + k) f ⟨_, hg⟩)
    (hτ : ∀ c, τ c = h.bar c) (hL : ∀ l ∈ uBarL K k f, α l = l)
    {A₁ : Matrix (Fin 2) (Fin 2) K} {D : Matrix (Fin k) (Fin k) K} (hA : A.val = blk A₁ D) :
    False := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  have hq : ζ ^ 2 ^ f = ζ⁻¹ := eq_inv_of_mul_eq_one_left hζ
  set i₀ : Fin k := ⟨0, by omega⟩
  set i₁ : Fin k := ⟨1, by omega⟩
  set i₂ : Fin k := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  set s : Fin k → K :=
    Function.update (Function.update (Function.update 1 i₂ (ζ⁻¹ * ζ⁻¹)) i₁ ζ) i₀ ζ with hs_def
  have hs₀ : s i₀ = ζ := by simp [s]
  have hs₁ : s i₁ = ζ := by simp [s, Ne.symm h01]
  have hs₂ : s i₂ = ζ⁻¹ * ζ⁻¹ := by simp [s, Ne.symm h02, Ne.symm h12]
  have hs : ∀ i, s i = ζ ∨ s i = ζ⁻¹ * ζ⁻¹ ∨ s i = 1 := by
    intro i
    by_cases hi0 : i = i₀
    · exact Or.inl (hi0 ▸ hs₀)
    by_cases hi1 : i = i₁
    · exact Or.inl (hi1 ▸ hs₁)
    by_cases hi2 : i = i₂
    · exact Or.inr (Or.inl (hi2 ▸ hs₂))
    · exact Or.inr (Or.inr (by simp [s, hi0, hi1, hi2]))
  have hsu : ∀ i, s i ^ 2 ^ f * s i = 1 := by
    intro i
    rcases hs i with h1 | h1 | h1 <;> rw [h1]
    · exact hζ
    · rw [mul_pow, inv_pow, hq, inv_inv]
      field_simp
    · rw [one_pow, one_mul]
  have hdet : ∏ i, s i = 1 := by
    rw [hs_def, Finset.prod_update_of_mem (Finset.mem_univ i₀),
      Finset.prod_update_of_mem (show i₁ ∈ Finset.univ \ {i₀} by simp [Ne.symm h01]),
      Finset.prod_update_of_mem
        (show i₂ ∈ (Finset.univ \ {i₀}) \ {i₁} by simp [Ne.symm h02, Ne.symm h12])]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    rw [← mul_assoc, ← mul_assoc, mul_assoc ζ ζ ζ⁻¹, mul_inv_cancel₀ hζ0, mul_one,
      mul_inv_cancel₀ hζ0]
  obtain ⟨S, hS⟩ := exists_diagonal_mem hsu hdet
  have e := mul_eq_of_fix_uBarL hα hA hL S
  rw [hS, diagonal_map (map_zero τ)] at e
  refine false_of_mul_diagonal (det_ne_zero_of_blk hA).2 e.symm (j := i₂) fun i => ?_
  rw [hs₂, map_mul, map_inv₀, hτ, h.bar_apply, hq, inv_inv]
  rcases hs i with h1 | h1 | h1 <;> rw [h1]
  · intro h3
    apply hζ1
    have h4 : ζ * 1 = ζ * ζ := by rw [mul_one]; exact h3
    exact (mul_left_cancel₀ hζ0 h4).symm
  · intro h3
    apply hζ1
    have h4 : ζ⁻¹ = ζ := eq_of_mul_self_eq h3
    exact eq_of_mul_self_eq (by rw [one_mul]; nth_rewrite 1 [← h4]; exact inv_mul_cancel₀ hζ0)
  · intro h3
    exact hζ1 (eq_of_mul_self_eq (by rw [one_mul]; exact h3.symm)).symm.symm

end Proj

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k f : ℕ}

theorem eq_one_of_fixes_u_of_three_le (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hk : 3 ≤ k)
    (α : MulAut (StatedProj (StatedSU (2 + k) (2 ^ f) K))) (h2 : α * α = 1)
    (hW : ∀ w ∈ uBarW K k f, α w = w) (hL : ∀ l ∈ uBarL K k f, α l = l) : α = 1 := by
  have h := unitaryFieldData_of_card hK hf
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  obtain ⟨τ, A, -, hα⟩ := exists_unitary_semilinear_statedProj h (n := 2 + k) (by omega)
    (fun h3 => by have := h3.1; omega) α
  obtain ⟨A₁, D, hA⟩ := exists_blk_of_fix_uBarW hα hζ hζ1 hW
  rcases eq_refl_or_bar_of_fix_uBarW hα h hA hW with rfl | hτ
  · exact eq_one_of_fixes_u_refl (by omega) hζ hζ1 hα h2 hW hL hA
  · exact (false_of_fix_uBarL_bar h hk hζ hζ1 hα hτ hL hA).elim

theorem eq_one_of_fixes_u_two (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K))) (h2 : α * α = 1)
    (hW : ∀ w ∈ uBarW K 2 f, α w = w) (hL : ∀ l ∈ uBarL K 2 f, α l = l)
    (hT : ∀ t ∈ uBarT K f, α t = t) : α = 1 := by
  have h := unitaryFieldData_of_card hK hf
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  obtain ⟨τ, A, -, hα⟩ := exists_unitary_semilinear_statedProj h (n := 2 + 2) (by norm_num)
    (fun h3 => by have := h3.1; omega) α
  obtain ⟨A₁, D, hA⟩ := exists_blk_of_fix_uBarW hα hζ hζ1 hW
  rcases eq_refl_or_bar_of_fix_uBarW hα h hA hW with rfl | hτ
  · exact eq_one_of_fixes_u_refl le_rfl hζ hζ1 hα h2 hW hL hA
  · obtain ⟨c, -, hc⟩ := exists_rootsOfUnity_ne_one hζ hζ1
    exact (false_of_fix_torus_bar h hα hτ hA hc (hT _ ⟨c, rfl⟩)).elim

omit [Finite K] [CharP K 2] in
theorem exists_smul_statedSU_two (h : UnitaryFieldData 2 f K) {D : Matrix (Fin 2) (Fin 2) K}
    (hDu : (D.map h.bar)ᵀ * D = 1) :
    ∃ (d : K) (S : StatedSU 2 (2 ^ f) K), d ≠ 0 ∧ D = d • (S : GL (Fin 2) K).val := by
  have hf := h.one_le
  set δ := D.det with hδ_def
  have hδ : δ ^ 2 ^ f * δ = 1 := by
    have h1 := congrArg det hDu
    rw [det_mul, det_transpose, det_one,
      show (D.map h.bar).det = h.bar D.det from (RingHom.map_det h.bar D).symm, h.bar_apply] at h1
    exact h1
  have hδ0 : δ ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hδ
    exact zero_ne_one hδ
  set d := δ ^ (2 ^ (f - 1) + 1) with hd_def
  have hpow : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hd2 : d * d = δ := by
    rw [hd_def, ← pow_add, show 2 ^ (f - 1) + 1 + (2 ^ (f - 1) + 1) = 2 ^ f + 1 + 1 by omega,
      pow_succ, pow_succ, hδ, one_mul]
  have hd0 : d ≠ 0 := fun h0 => hδ0 (by rw [← hd2, h0, mul_zero])
  have hdq : d ^ 2 ^ f * d = 1 := by
    rw [hd_def, ← pow_mul, mul_comm (2 ^ (f - 1) + 1), pow_mul, ← mul_pow, hδ, one_pow]
  have hdet : (d⁻¹ • D).det = 1 := by
    rw [det_smul, Fintype.card_fin, ← hδ_def, ← hd2, sq, ← mul_assoc, mul_assoc d⁻¹,
      inv_mul_cancel₀ hd0, mul_one, inv_mul_cancel₀ hd0]
  have hu : ((d⁻¹ • D).map h.bar)ᵀ * (d⁻¹ • D) = 1 := by
    have hmap : (d⁻¹ • D).map h.bar = h.bar d⁻¹ • D.map h.bar := by
      ext i j
      simp [map_mul]
    rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hDu, smul_smul, map_inv₀,
      h.bar_apply, ← mul_inv, hdq, inv_one, one_smul]
  obtain ⟨S, hS⟩ := exists_statedSU_eq_of_bar h hdet hu
  refine ⟨d, S, hd0, ?_⟩
  rw [hS, smul_smul, mul_inv_cancel₀ hd0, one_smul]

theorem exists_inner_of_fixes_u_two (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K)))
    (hW : ∀ w ∈ uBarW K 2 f, α w = w) (hT : ∀ t ∈ uBarT K f, α t = t) :
    ∃ l ∈ uBarL K 2 f, ∀ x ∈ uBarL K 2 f, α x = l * x * l⁻¹ := by
  have h := unitaryFieldData_of_card hK hf
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨τ, A, hAu, hα⟩ := exists_unitary_semilinear_statedProj h (n := 2 + 2) (by norm_num)
    (fun h3 => by have := h3.1; omega) α
  obtain ⟨A₁, D, hA⟩ := exists_blk_of_fix_uBarW hα hζ hζ1 hW
  rcases eq_refl_or_bar_of_fix_uBarW hα h hA hW with rfl | hτ
  swap
  · obtain ⟨c, -, hc⟩ := exists_rootsOfUnity_ne_one hζ hζ1
    exact (false_of_fix_torus_bar h hα hτ hA hc (hT _ ⟨c, rfl⟩)).elim
  obtain ⟨J, hJ⟩ := exists_swapM_mem (K := K) f
  obtain ⟨J', hJ'⟩ := exists_twJ_mem hζ
  have e1 := mul_eq_of_fix_uBarW hα hA hW (mul_self_eq_one_of_val hJ swapM_mul_swapM)
  have e2 := mul_eq_of_fix_uBarW hα hA hW (mul_self_eq_one_of_val hJ' (twJ_mul_twJ hζ0))
  rw [hJ] at e1
  rw [hJ'] at e2
  have hA₁ := eq_smul_one_of_commute_twJ hζ0 hζ1 e1 e2
  have hDu : (D.map h.bar)ᵀ * D = 1 := by
    rw [hA, blk_map_fun _ (map_zero h.bar), transpose_blk, blk_mul, ← blk_one] at hAu
    exact (blk_injective hAu).2
  obtain ⟨d, S, hd0, hDS⟩ := exists_smul_statedSU_two h hDu
  refine ⟨uProj K (2 + 2) f (uL K 2 f S), ⟨S, rfl⟩, ?_⟩
  rintro _ ⟨X, rfl⟩
  simp only [MonoidHom.comp_apply]
  obtain ⟨hg, hαg⟩ := hα (uL K 2 f X)
  have hαg' : α (uProj K (2 + 2) f (uL K 2 f X)) = uProj K (2 + 2) f ⟨_, hg⟩ := hαg
  rw [hαg', ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [glAut_refl, Subgroup.coe_mul, Subgroup.coe_inv]
  set B : GL (Fin (2 + 2)) K := (uL K 2 f S : GL (Fin (2 + 2)) K)
  set Xg : GL (Fin (2 + 2)) K := (uL K 2 f X : GL (Fin (2 + 2)) K)
  have hB : B.val = blk 1 (S : GL (Fin 2) K).val := coe_uL S
  obtain ⟨hBi, -, -, hS1, -⟩ := inv_val_of_blk hB
  have hC : (A * B⁻¹).val = blk (A₁ 0 0 • 1) (d • 1) := by
    rw [Units.val_mul, hA, hBi, blk_mul, inv_one, Matrix.mul_one, ← hA₁, hDS, Matrix.smul_mul,
      hS1]
  have hBX : (B * Xg * B⁻¹).val =
      blk 1 ((S : GL (Fin 2) K).val * (X : GL (Fin 2) K).val * (S : GL (Fin 2) K).val⁻¹) := by
    rw [Units.val_mul, Units.val_mul, hB, hBi, coe_uL, blk_mul, blk_mul, inv_one, Matrix.mul_one,
      Matrix.mul_one]
  have hcomm : A * B⁻¹ * (B * Xg * B⁻¹) = B * Xg * B⁻¹ * (A * B⁻¹) :=
    Units.ext (by
      rw [Units.val_mul (A * B⁻¹), Units.val_mul (B * Xg * B⁻¹) (A * B⁻¹), hC, hBX,
        blk_mul_smul_one_comm])
  calc A * Xg * A⁻¹ = A * B⁻¹ * (B * Xg * B⁻¹) * (A * B⁻¹)⁻¹ := by group
    _ = B * Xg * B⁻¹ * (A * B⁻¹) * (A * B⁻¹)⁻¹ := by rw [hcomm]
    _ = B * Xg * B⁻¹ := by group

end Main

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {G : Type} [Group G]
  {A : Subgroup G}

theorem noInv_u_of_three_le {k : ℕ} {θ : ↥A →* StatedProj (StatedSU (2 + k) (2 ^ f) K)}
    (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hk : 3 ≤ k) :
    NoInvolutoryCentralizing A (uLeviW θ ⊔ uLeviL θ) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hW := inducedAut_fix_of_levLift hθ (commutator_uBarW hK hf) le_sup_left hfix hα
  have hL := inducedAut_fix_of_levLift hθ (commutator_uBarL hK hf (by omega)) le_sup_right hfix
    hα
  have h1 := eq_one_of_fixes_u_of_three_le hK (by omega) hk α (inducedAut_sq hθ hσ hα) hW hL
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

theorem noInv_u_two {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)}
    (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    NoInvolutoryCentralizing A (liftSub θ (uBarT K f) ⊔ uLeviW θ ⊔ uLeviL θ) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hT := inducedAut_fix_of_liftSub hθ (le_sup_left.trans le_sup_left) hfix hα
  have hW := inducedAut_fix_of_levLift hθ (commutator_uBarW hK hf)
    (le_sup_right.trans le_sup_left) hfix hα
  have hL := inducedAut_fix_of_levLift hθ (commutator_uBarL hK hf le_rfl) le_sup_right hfix hα
  have h1 := eq_one_of_fixes_u_two hK (by omega) α (inducedAut_sq hθ hσ hα) hW hL hT
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

theorem outerFree_u_two {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)}
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) (σ : MulAut ↥A)
    (hfix : ∀ y : ↥A, (y : G) ∈ liftSub θ (uBarT K f) ⊔ uLeviW θ → σ y = y) :
    ∃ l ∈ uLeviL θ, ∀ z : ↥A, (z : G) ∈ uLeviL θ → ((σ z : ↥A) : G) = l * z * l⁻¹ := by
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hT := inducedAut_fix_of_liftSub hθ le_sup_left hfix hα
  have hW := inducedAut_fix_of_levLift hθ (commutator_uBarW hK hf) le_sup_right hfix hα
  obtain ⟨lb, hlb, hinner⟩ := exists_inner_of_fixes_u_two hK (by omega) α hW hT
  exact exists_inner_levLift_of hker hθ (commutator_uBarL hK hf le_rfl) σ hα hlb hinner

end Lift

end CFSG.ComponentClassification.RankTwoClassical
