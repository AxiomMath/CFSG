module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineE3Base

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix GenLocL3Good GenLocL3Pair GenLocL3Seven
  GenLocL3Nine GenLocL3NineR3 GenLocL3NineE3
open scoped MatrixGroups Classical

namespace GenLocL3NineE3

variable {K : Type} [Field K]

theorem adm_closure_pair {D : Type} [Group D] [Finite D] (hD : CFSG.IsElementaryAbelian 2 D)
    (h8 : Nat.card D = 8) (y1 y2 : D) (h1 : y1 ≠ 1) (h2 : y2 ≠ 1) (h12 : y1 ≠ y2) :
    pRank 2 D - 1 ≤ pRank 2 ↥(Subgroup.closure ({y1, y2} : Set D)) := by
  classical
  rw [GenLocBasic.adm_iff_index hD]
  have hsq : ∀ z : D, z * z = 1 := fun z => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD z
  have hinv : ∀ z : D, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (hsq z)
  set E := Subgroup.closure ({y1, y2} : Set D) with hE
  have h1E : y1 ∈ E := Subgroup.subset_closure (by simp)
  have h2E : y2 ∈ E := Subgroup.subset_closure (by simp)
  have hS : ({1, y1, y2, y1 * y2} : Finset D).card = 4 := by
    have n1 : (1 : D) ≠ y1 := h1.symm
    have n2 : (1 : D) ≠ y2 := h2.symm
    have n3 : (1 : D) ≠ y1 * y2 := by
      intro h
      apply h12
      have := eq_inv_of_mul_eq_one_right h.symm
      rw [hinv] at this
      exact this.symm
    have n4 : y1 ≠ y2 := h12
    have n5 : y1 ≠ y1 * y2 := fun h => h2 (by simpa using h)
    have n6 : y2 ≠ y1 * y2 := fun h => h1 (by simpa using h)
    simp [Finset.card_insert_of_notMem, n1, n2, n3, n4, n5, n6]
  have hsub : (({1, y1, y2, y1 * y2} : Finset D) : Set D) ⊆ (E : Set D) := by
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact h1E
    · exact h2E
    · exact E.mul_mem h1E h2E
  have h4 : 4 ≤ Nat.card E := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hS] at this
    rwa [← Nat.card_coe_set_eq] at this
  have h := Subgroup.card_mul_index E
  rw [h8] at h
  by_contra hlt
  push Not at hlt
  have : 4 * 3 ≤ Nat.card E * E.index := Nat.mul_le_mul h4 hlt
  omega


theorem e3_core [Finite K]
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K) (hA : IsRank23 ↥D)
    (h8 : Nat.card ↥D = 8) {t b : Fin 3} (hbt : b ≠ t) (hgood : GoodBlk D hfs t)
    (yf yr : D) (hyf1 : yf ≠ 1) (hyr1 : yr ≠ 1) (hyfr : yf ≠ yr)
    {uf v : Fin 3 → Kˣ} {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3)
    (hf : (yf : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 uf) *
      LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ 0)
    (hr : (yr : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 v) *
      LinearFlag.fieldAut 3 K 1 * LinearFlag.dualAut 3 K ^ 1)
    (hjk : (v (crd b 0) : K) * (uf (crd b 0) : K) = (v (crd b 1) : K) * (uf (crd b 1) : K))
    (hsq : IsSquare ((v (crd b 0) : K) * v (crd b 1))) : gammaAct D.subtype = ⊤ := by
  have hα : D.subtype.range ≤ frameStab 3 K := by rwa [Subgroup.range_subtype]
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  obtain ⟨r, hr0⟩ := hsq
  have hvj : ((v (crd b 0) : Kˣ) : K) ≠ 0 := (v _).ne_zero
  have hvk : ((v (crd b 1) : Kˣ) : K) ≠ 0 := (v _).ne_zero
  have hr00 : r ≠ 0 := by
    rintro rfl
    simp at hr0
  have hβ : r / (v (crd b 1) : K) ≠ 0 := div_ne_zero hr00 hvk
  have hrelR : (r / (v (crd b 1) : K)) * (r / (v (crd b 1) : K)) * (v (crd b 1) : K) =
      (v (crd b 0) : K) := by
    field_simp
    linear_combination -hr0
  have hrelF : (r / (v (crd b 1) : K)) * (r / (v (crd b 1) : K)) * (uf (crd b 0) : K) =
      (uf (crd b 1) : K) := by
    have h1 : (r / (v (crd b 1) : K)) * (r / (v (crd b 1) : K)) = (v (crd b 0) : K) / (v (crd b 1) : K) := by
      field_simp
      linear_combination -hr0
    rw [h1]
    field_simp
    linear_combination hjk
  have fixR := fixed_anti_of_reflection b (hfs yr.2) hr hβ hrelR
  have fixF := fixed_anti_of_field b (hfs yf.2) hσ hf hβ hrelF
  have hE := adm_closure_pair hA.1 h8 yf yr hyf1 hyr1 hyfr
  have hfix : ∀ e ∈ Subgroup.closure ({yf, yr} : Set ↥D),
      (D.subtype e) (phiM b (anti hβ)) = phiM b (anti hβ) := by
    intro e he
    refine Subgroup.closure_induction (p := fun e _ => (D.subtype e) (phiM b (anti hβ)) = phiM b (anti hβ))
      ?_ ?_ ?_ ?_ he
    · rintro x (rfl | rfl)
      · exact fixF
      · exact fixR
    · simp
    · intro x y _ _ hx hy
      rw [map_mul, MulAut.mul_apply, hy, hx]
    · intro x _ hx
      rw [map_inv]
      calc ((D.subtype x)⁻¹) (phiM b (anti hβ)) =
            ((D.subtype x)⁻¹) ((D.subtype x) (phiM b (anti hβ))) := by rw [hx]
        _ = phiM b (anti hβ) := by simp
  have hw : phiM b (anti hβ) ∈ gammaAct D.subtype :=
    le_gammaAct D.subtype hE ((GenLocBasic.mem_fixedIn_map _ _ _).2 hfix)
  exact gammaAct_eq_top_of_good_mono D.subtype hα hbt.symm hgood hβ hw


end GenLocL3NineE3

end CFSG.GH74.Generic.BProg.B2
