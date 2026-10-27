module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSp4E
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerH

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open CFSG.ComponentClassification.CatFactsSp4

variable {K : Type} [Field K]

theorem proj_eq_of_coe_eq_neg {x y : StatedSp 2 K}
    (h : ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    proj 2 K x = proj 2 K y :=
  (proj_eq_of_eq_or_neg (Or.inr h)).symm

theorem kron_one_eq_blk (g : Matrix (Fin 2) (Fin 2) K) : kron g 1 = blk g g := by
  simp only [kron, blk, diag2]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem T1_mul_diagSL (h2 : (2 : K) ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    T1 K * diagSL K g = diagSL K g * T1 K := by
  have hmem : diagSL K g ∈ centralizer {T1 K} := by
    rw [mem_centralizer_T1_iff h2]
    refine ⟨(g, g), sp_ext ?_⟩
    rw [coe_blkSL, coe_diagSL, kron_one_eq_blk]
  exact (mem_centralizer_singleton_iff.mp hmem).symm

theorem u1_commute_Lsub (h2 : (2 : K) ≠ 0) {l : StatedProj (StatedSp 2 K)} (hl : l ∈ Lsub K) :
    u1 K * l = l * u1 K := by
  obtain ⟨_, ⟨g, rfl⟩, rfl⟩ := hl
  rw [u1, ← map_mul, ← map_mul, T1_mul_diagSL h2]

theorem u2_commute_Lsub {l : StatedProj (StatedSp 2 K)} (hl : l ∈ Lsub K) :
    u2 K * l = l * u2 K :=
  (mem_centralizer_singleton_iff.mp (Lsub_le_centralizer hl)).symm

theorem diag2_mul_J₁ : diag2 (1 : K) (-1) * J₁ = -(J₁ * diag2 1 (-1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2, J₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem u1_mul_u2 : u1 K * u2 K = u2 K * u1 K := by
  rw [u1, u2, ← map_mul, ← map_mul]
  apply proj_eq_of_coe_eq_neg
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_T1', coe_T2, kron_mul,
    kron_mul, diag2_mul_J₁]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [kron]

theorem u2_mul_u2 : u2 K * u2 K = 1 := by
  rw [u2, ← map_mul, ← map_one (proj 2 K)]
  apply proj_eq_of_coe_eq_neg
  rw [Subgroup.coe_mul, Units.val_mul, coe_T2, kron_mul, Matrix.one_mul]
  have hJ : (J₁ : Matrix (Fin 2) (Fin 2) K) * J₁ = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J₁, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hJ]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [kron]

theorem u1_ne_u2 : u1 K ≠ u2 K := by
  intro h
  rcases eq_or_eq_neg_of_proj_eq h with h' | h' <;>
    · have := congrFun (congrFun h' (Sum.inl 0)) (Sum.inl 0)
      simp [coe_T1', coe_T2, kron, diag2, J₁] at this

theorem u2_ne_one'' : u2 K ≠ 1 := by
  intro h
  rw [u2, ← map_one (proj 2 K)] at h
  rcases eq_or_eq_neg_of_proj_eq h with h' | h' <;>
    · have := congrFun (congrFun h' (Sum.inl 0)) (Sum.inl 0)
      simp [coe_T2, kron, J₁] at this

theorem exists_elemTwo_u2 [Finite K] (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), E ≤ centralizer {u2 K} ∧ ElemTwo E ∧
      16 ≤ Nat.card E := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨E, hEr, hE, hE4⟩ := exists_E4_of_hom h2 hodd ((proj 2 K).comp (diagSL K))
    ker_proj_comp_diagSL
  have hER : E ≤ Lsub K := by
    rw [Lsub, ← MonoidHom.range_comp]
    exact hEr
  obtain ⟨hB, hB4⟩ := elemTwo_pair (u1_mul_u2 (K := K)) u1_mul_u1 u2_mul_u2 (u1_ne_one h2)
    u2_ne_one'' u1_ne_u2
  have hBR : ∀ b ∈ zpowers (u1 K) ⊔ zpowers (u2 K), ∀ r ∈ Lsub K, b * r = r * b := by
    intro b hb r hr
    have hle : zpowers (u1 K) ⊔ zpowers (u2 K) ≤ centralizer (Lsub K : Set _) := by
      refine sup_le ((zpowers_le).mpr ?_) ((zpowers_le).mpr ?_) <;>
        rw [mem_centralizer_iff] <;> intro l hl
      · exact (u1_commute_Lsub h2 hl).symm
      · exact (u2_commute_Lsub hl).symm
    exact (mem_centralizer_iff.mp (hle hb) r hr).symm
  have hLs := isSimpleGroup_Lsub (K := K) h4
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_ne_of_isQuasisimple (isQuasisimple_Lsub (K := K) h4)
  obtain ⟨hEB, hcard⟩ := elemTwo_of_centralizer hLs ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy
    (congrArg Subtype.val h)⟩ hER hE hB hBR
  refine ⟨_, sup_le (hER.trans Lsub_le_centralizer) ?_, hEB, ?_⟩
  · refine sup_le ((zpowers_le).mpr ?_) ((zpowers_le).mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr (u1_mul_u2 (K := K))
    · exact mem_centralizer_singleton_iff.mpr rfl
  · calc 16 = 4 * 4 := by norm_num
      _ ≤ Nat.card E * Nat.card ↥(zpowers (u1 K) ⊔ zpowers (u2 K)) := Nat.mul_le_mul hE4 hB4
      _ ≤ _ := hcard

theorem exists_elemTwo_alphaI [Finite K] (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) {a : K}
    (ha : a ≠ 0) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), E ≤ fixOf (alphaI ha) ∧ ElemTwo E ∧
      8 ≤ Nat.card E := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨E, hEr, hE, hE4⟩ := exists_E4_of_hom h2 hodd ((proj 2 K).comp (gI ha))
    (ker_proj_comp_gI ha)
  have hER : E ≤ JI ha := by
    rw [JI, ← MonoidHom.range_comp]
    exact hEr
  have hB := elemTwo_zpowers (u1_mul_u1 (K := K))
  have hB2 := card_zpowers_of_sq (u1_mul_u1 (K := K)) (u1_ne_one h2)
  have hBR : ∀ b ∈ zpowers (u1 K), ∀ r ∈ JI ha, b * r = r * b := by
    intro b hb r hr
    have hle : zpowers (u1 K) ≤ centralizer (JI ha : Set _) := by
      refine (zpowers_le).mpr ?_
      rw [mem_centralizer_iff]
      intro l hl
      exact (u1_commute_JI ha hl).symm
    exact (mem_centralizer_iff.mp (hle hb) r hr).symm
  have hJs := isSimpleGroup_JI ha h4
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_ne_of_isQuasisimple (isQuasisimple_JI ha h4)
  obtain ⟨hEB, hcard⟩ := elemTwo_of_centralizer hJs ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy
    (congrArg Subtype.val h)⟩ hER hE hB hBR
  refine ⟨_, sup_le (hER.trans (JI_le_fix ha)) ((zpowers_le).mpr (alphaI_u1 ha)), hEB, ?_⟩
  calc 8 = 4 * 2 := by norm_num
    _ ≤ Nat.card E * Nat.card (zpowers (u1 K)) := by rw [hB2]; exact Nat.mul_le_mul_right 2 hE4
    _ ≤ _ := hcard

end CFSG.ComponentClassification.HarrisLit.Hin
