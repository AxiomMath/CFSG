module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.GL2NonsplitTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.PSL2Dichotomy
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2Strong

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

variable {F : Type} [Field F] [Finite F]

theorem gl2NonsplitMax_of_mod (hq : Nat.card F % 3 = 2)
    (h5 : 5 ≤ Nat.card F) : GL2NonsplitMax F := by
  intro Y hY
  let _ : Fintype F := Fintype.ofFinite F
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_mod hq
  obtain ⟨p, f, hp, hf, hcard⟩ := (isPrimePow_nat_iff _).1 (FiniteField.isPrimePow_card F)
  have : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card F = p ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hcard.symm
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : 3 ∣ Nat.card F := hF ▸ dvd_pow_self 3 hf.ne'
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F := Matrix.SpecialLinearGroup.toGL
    with htoGL
  set Y₁ : Subgroup (SpecialLinearGroup (Fin 2) F) := Y.comap toGL with hY₁
  set A : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers (projPSL F (cSL (F := F))) with hAdef
  set W : Subgroup (PSL2MatrixGroup F) := Y₁.map (projPSL F) with hWdef
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers, orderOf_projPSL_cSL]
  have hmemY₁ : ∀ g : SpecialLinearGroup (Fin 2) F, toGL g ∈ Y → g ∈ Y₁ := fun g hg => hg
  have hKey : ∀ g : SpecialLinearGroup (Fin 2) F,
      projPSL F g * projPSL F cSL * (projPSL F g)⁻¹ ∈ A → projPSL F g ∈ W :=
    fun g hg => ⟨g, hmemY₁ g (hY (toGL_mem_Nt_of_projPSL hg)), rfl⟩
  have hNW : Subgroup.normalizer (A : Set (PSL2MatrixGroup F)) ≤ W := by
    intro a ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin 2) F)) a
    exact hKey g ((Subgroup.mem_normalizer_iff.mp ha _).mp (Subgroup.mem_zpowers _))
  have hcW : projPSL F (cSL (F := F)) ∈ W :=
    ⟨cSL, hmemY₁ _ (hY (by rw [htoGL, toGL_cSL]; exact cGL_mem_Nt)), rfl⟩
  have hAW : A ≤ W := (Subgroup.zpowers_le).mpr hcW
  obtain ⟨z, g, t, hz3, hg0, hg2, hzg, ht⟩ := exists_torus_element hF hp3
  have hzg' : z * g = Nat.card F + 1 := by
    rcases hzg with h | h
    · exfalso
      have := Dvd.dvd.mul_right hz3 g
      rw [h] at this
      omega
    · exact h
  obtain ⟨x, hxo, hxc⟩ := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj.exists_conj_mem_centralizer
    (isCyclic_of_isPGroup_three hF hp3) hA (t := t) (by rw [ht]; exact hz3)
  have hxW : x ∈ W :=
    hNW (Subgroup.centralizer_le_normalizer (A : Set (PSL2MatrixGroup F)) hxc)
  obtain ⟨s, hsdet, hsinv⟩ := exists_inverting_det_one h3
  let sSL : SpecialLinearGroup (Fin 2) F := ⟨(s : Matrix (Fin 2) (Fin 2) F), hsdet⟩
  have hsSL : toGL sSL = s := Units.ext rfl
  have hsY : s ∈ Y := hY (mem_Nt_of_inv hsinv)
  have hsW : projPSL F sSL ∈ W := ⟨sSL, hmemY₁ _ (by rw [hsSL]; exact hsY), rfl⟩
  have hsc : sSL * cSL * sSL⁻¹ = (cSL (F := F))⁻¹ := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv, map_inv, hsSL, toGL_cSL]
    exact hsinv
  have hsconj : projPSL F sSL * projPSL F cSL * (projPSL F sSL)⁻¹ = (projPSL F (cSL (F := F)))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hsc, map_inv]
  have hsN : projPSL F sSL ∈ Subgroup.normalizer (A : Set (PSL2MatrixGroup F)) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow, hsconj, _root_.inv_zpow]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers _ _)
  have hsA : projPSL F sSL ∉ A := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    set zz : SpecialLinearGroup (Fin 2) F := sSL * (cSL ^ k)⁻¹ with hzz
    have hzzc : zz ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
      rw [← projPSL_eq_one_iff]
      simp only [hzz, map_mul, map_inv, map_zpow]
      rw [hk]
      exact mul_inv_cancel _
    have hcomm : Commute sSL cSL := by
      have h1 : sSL = zz * cSL ^ k := by rw [hzz, inv_mul_cancel_right]
      rw [h1]
      exact Commute.mul_left (show Commute zz cSL from (Subgroup.mem_center_iff.mp hzzc cSL).symm)
        (Commute.zpow_left (Commute.refl _) k)
    have h2 : sSL * cSL * sSL⁻¹ = cSL := by
      rw [hcomm.eq]
      simp
    rw [hsc] at h2
    have h3' : (cSL (F := F)) ^ 2 = 1 := by
      rw [pow_two]
      exact (inv_eq_iff_mul_eq_one.mp h2)
    have := orderOf_dvd_of_pow_eq_one h3'
    rw [orderOf_cSL] at this
    omega
  rcases psl2_dichotomy hF hp3 h5 hz3 hg0 hg2 hzg' hA hAW hxW (hxo.trans ht) hsW hsN hsA with
    hW | hnormal
  ·
    right
    rintro _ ⟨g, rfl⟩
    have hgW : projPSL F g ∈ W := hW ▸ Subgroup.mem_top _
    obtain ⟨g', hg'Y, hg'⟩ := hgW
    have hcen : g⁻¹ * g' ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq.mp hg'.symm)
    have h1 : toGL g = toGL g' * (toGL (g⁻¹ * g'))⁻¹ := by
      simp [map_mul, map_inv]
    change toGL g ∈ Y
    rw [h1]
    exact Y.mul_mem hg'Y (Y.inv_mem (hY (toGL_mem_Nt_of_mem_center hcen)))
  ·
    left
    have hYNt : ∀ g : SpecialLinearGroup (Fin 2) F, g ∈ Y₁ → toGL g ∈ (Nt : Subgroup (GL (Fin 2) F)) := by
      intro g hg
      have hgW : projPSL F g ∈ W := ⟨g, hg, rfl⟩
      have hn : (⟨projPSL F cSL, hcW⟩ : W) ∈ A.subgroupOf W := Subgroup.mem_zpowers _
      have := hnormal.conj_mem _ hn ⟨projPSL F g, hgW⟩
      exact toGL_mem_Nt_of_projPSL this
    refine le_antisymm (fun y hy => ?_) hY
    obtain ⟨n, hn, hdn⟩ := exists_comm_det_eq h3 (GeneralLinearGroup.det y).ne_zero
    have hnNt : n ∈ (Nt : Subgroup (GL (Fin 2) F)) := mem_Nt_of_comm hn
    have hdet1 : GeneralLinearGroup.det (y * n⁻¹) = 1 := by
      have hdn' : GeneralLinearGroup.det n = GeneralLinearGroup.det y := by
        apply Units.ext
        rw [GeneralLinearGroup.val_det_apply, hdn, GeneralLinearGroup.val_det_apply]
      rw [map_mul, map_inv, hdn', mul_inv_cancel]
    let g : SpecialLinearGroup (Fin 2) F := ⟨((y * n⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
      have := congrArg Units.val hdet1
      simpa using this⟩
    have hg : toGL g = y * n⁻¹ := Units.ext rfl
    have hgY : g ∈ Y₁ := by
      change toGL g ∈ Y
      rw [hg]
      exact Y.mul_mem hy (Y.inv_mem (hY hnNt))
    have := hYNt g hgY
    rw [hg] at this
    have h4 : y = y * n⁻¹ * n := by simp
    rw [h4]
    exact Subgroup.mul_mem _ this hnNt

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
