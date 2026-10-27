module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11a


public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open scoped Pointwise

variable {G : Type} [Group G]

theorem fzl59f_str
    [Finite G] [IsSimpleGroup G] {t : G} {L S T₂ : Subgroup G}
    {x₁ x₂ lam rho tau : G} (hr4 : FzAssumptionII G) (hctx : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) (hT : IsFzT2 t x₁ x₂ S T₂) :
    FzStr t tau lam rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂) (fzQ t x₁ x₂ rho)
      (fzR t x₁ x₂) T₂ := by
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  exact fzl_str hctx hK hT hF h37

private theorem fzl59f_zpow_cases {y : G} (hy : y ^ 2 = 1) (k : ℤ) : y ^ k = 1 ∨ y ^ k = y := by
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul]
    simp [hy]
  · right
    rw [zpow_add, zpow_mul, zpow_one]
    simp [hy]

private theorem fzl59f_comm_Z {a x₁ x₂ : G} (hc1 : Commute a (x₁ ^ 2))
    (hc2 : Commute a (x₂ ^ 2)) (hx : Commute x₁ x₂) :
    ∀ z ∈ fourGrp x₁ x₂, a * z = z * a := by
  intro z hz
  have hle : fourGrp x₁ x₂ ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [fourGrp, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl
    · exact hc1.symm.eq
    · rw [hx.mul_pow]
      exact (hc1.mul_right hc2).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hz)).symm

private theorem fzl59f_sq_eq {x t : G} (hc : Commute x t) (ht : t ^ 2 = 1) :
    (x * t) ^ 2 = x ^ 2 := by
  rw [hc.mul_pow, ht, mul_one]

private theorem fzl59f_mem_R6 {t x₁ x₂ a₁₂ a₂₂ a₃₂ g : G}
    (hg : g ∈ ({x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂} : Set G)) :
    g ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ :=
  Subgroup.subset_closure hg

variable {t x₁ x₂ lam tau rho : G} {T₂ Q R : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}

theorem fzl59f_lam_normalizes
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    lam ∈ normalizer ((fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ : Subgroup G) : Set G) := by
  have hl : lam * lam = 1 := by rw [← pow_two]; exact hsh.lam_sq
  have hcc : ∀ a : G, lam * (lam * a * lam⁻¹) * lam⁻¹ = a := fun a => by
    calc lam * (lam * a * lam⁻¹) * lam⁻¹ = (lam * lam) * a * (lam * lam)⁻¹ := by group
      _ = a := by rw [hl]; group
  have hfix : ∀ y : G, Commute lam y → lam * y * lam⁻¹ = y := fun y hy => by
    rw [hy.eq]; group
  have hconj : ∀ x ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂, lam * x * lam⁻¹ ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ := by
    refine fzl59c_conj_closure ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx | hx | hx <;> rw [hx]
    · rw [hsh.lam_a₁₁]
      exact fzl59f_mem_R6 (by simp)
    · rw [hsh.lam_a₁₂]
      exact fzl59f_mem_R6 (by simp)
    · have e : lam * (x₂ * t) * lam⁻¹ = x₁ * t := by
        rw [← hsh.lam_a₁₁]
        exact hcc _
      rw [e]
      exact fzl59f_mem_R6 (by simp)
    · have e : lam * a₂₂ * lam⁻¹ = a₁₂ := by
        rw [← hsh.lam_a₁₂]
        exact hcc _
      rw [e]
      exact fzl59f_mem_R6 (by simp)
    · rw [hfix _ hsh.lam_comm₃.1]
      exact fzl59f_mem_R6 (by simp)
    · rw [hfix _ hsh.lam_comm₃.2]
      exact fzl59f_mem_R6 (by simp)
  exact fzl59c_mem_normalizer_of_sq hconj (fun m _ => by rw [hsh.lam_sq, one_mul, mul_one])

theorem fzl59f_T₂_eq_R6
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    T₂ = fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ⊔ zpowers lam := by
  rw [hsh.gen, fzR6, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

section
variable [Finite G]

theorem fzl59f_R6_le
    (h : FzStr t tau lam rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂) Q R T₂)
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ≤ R := by
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₁W := h.EW hx₁
  have hx₂W := h.EW hx₂
  have hc₁ : Commute x₁ t := h.W_comm x₁ hx₁W t h.t_mem
  have hc₂ : Commute x₂ t := h.W_comm x₂ hx₂W t h.t_mem
  have hc₁₂ : Commute x₁ x₂ := h.W_comm x₁ hx₁W x₂ hx₂W
  have hsq₁ : (x₁ * t) ^ 2 = x₁ ^ 2 := fzl59f_sq_eq hc₁ h.t_sq
  have hsq₂ : (x₂ * t) ^ 2 = x₂ ^ 2 := fzl59f_sq_eq hc₂ h.t_sq
  have hgen : ∀ g ∈ ({x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂, lam} : Set G), g ∈ T₂ := by
    intro g hg
    rw [hsh.gen]
    exact Subgroup.subset_closure hg
  have hT₁₂ : a₁₂ ∈ T₂ := hgen _ (by simp)
  have hT₂₂ : a₂₂ ∈ T₂ := hgen _ (by simp)
  have hT₃₂ : a₃₂ ∈ T₂ := hgen _ (by simp)
  rw [fzR6, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact R.mul_mem (h.QR (h.WQ hx₁W)) (h.QR (h.WQ h.t_mem))
  · refine (fzl_R_eq_cent_Z h a₁₂).mpr ⟨hT₁₂, fzl59f_comm_Z ?_ ?_ hc₁₂⟩
    · rw [← hsq₁]
      exact hsh.quat₁.mul_comm_sq
    · rw [← hsq₂]
      exact (hsh.comm₁₂ a₁₂ (by simp) (x₂ * t) (by simp)).pow_right 2
  · exact R.mul_mem (h.QR (h.WQ hx₂W)) (h.QR (h.WQ h.t_mem))
  · refine (fzl_R_eq_cent_Z h a₂₂).mpr ⟨hT₂₂, fzl59f_comm_Z ?_ ?_ hc₁₂⟩
    · rw [← hsq₁]
      exact ((hsh.comm₁₂ (x₁ * t) (by simp) a₂₂ (by simp)).pow_left 2).symm
    · rw [← hsq₂]
      exact hsh.quat₂.mul_comm_sq
  · exact R.mul_mem (h.QR (h.WQ ((ctxW t x₁ x₂).inv_mem ((ctxW t x₁ x₂).mul_mem hx₁W hx₂W))))
      (h.QR (h.WQ h.t_mem))
  · refine (fzl_R_eq_cent_Z h a₃₂).mpr ⟨hT₃₂, fzl59f_comm_Z ?_ ?_ hc₁₂⟩
    · rw [← hsq₁]
      exact ((hsh.comm₁₃ (x₁ * t) (by simp) a₃₂ (by simp)).pow_left 2).symm
    · rw [← hsq₂]
      exact ((hsh.comm₂₃ (x₂ * t) (by simp) a₃₂ (by simp)).pow_left 2).symm

theorem fzl59f_R_le_R6
    (h : FzStr t tau lam rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂) Q R T₂)
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    R ≤ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ := by
  have hle : zpowers lam ≤ normalizer ((fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (fzl59f_lam_normalizes hsh)
  intro g hgR
  have hgT : g ∈ ((zpowers lam : Subgroup G) : Set G) *
      ((fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle, sup_comm,
      ← fzl59f_T₂_eq_R6 hsh]
    exact h.RT hgR
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hgT
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rcases fzl59f_zpow_cases hsh.lam_sq k with hk | hk
  · rw [hk, one_mul]
    exact hb
  · exfalso
    rw [hk] at hgR
    have hbR : b ∈ R := fzl59f_R6_le h hsh hb
    have hlamR : lam ∈ R := by
      have := R.mul_mem hgR (R.inv_mem hbR)
      simpa using this
    obtain ⟨z, hz, hz'⟩ := h.lam_Z
    exact hz' (h.R_Z lam hlamR z hz)

theorem fzl59f_R_eq_R6_of_str
    (h : FzStr t tau lam rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂) Q R T₂)
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    R = fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ∧ T₂ = R ⊔ zpowers lam := by
  have hR : R = fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ :=
    le_antisymm (fzl59f_R_le_R6 h hsh) (fzl59f_R6_le h hsh)
  exact ⟨hR, by rw [hR]; exact fzl59f_T₂_eq_R6 hsh⟩

end

theorem fzl59f_R_eq_R6
    [Finite G] [IsSimpleGroup G] {L S : Subgroup G}
    (hr4 : FzAssumptionII G) (hctx : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) (hT : IsFzT2 t x₁ x₂ S T₂)
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    fzR t x₁ x₂ = fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ∧ T₂ = fzR t x₁ x₂ ⊔ zpowers lam :=
  fzl59f_R_eq_R6_of_str (fzl59f_str hr4 hctx hK hT) hsh

end CFSG.OddStandard.SmallF3.FritzII
