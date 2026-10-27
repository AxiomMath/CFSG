module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial SymplecticHigher
  SymplecticFlag Subgroup
open CFSG.ComponentClassification.CatFactsSp4

section K2a

variable {K : Type} [Field K]

theorem k2a_T1_mul_T1 : T1 K * T1 K = 1 := by
  apply sp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_T1, blk_mul, Matrix.mul_one, Matrix.mul_neg,
    neg_neg, Subgroup.coe_one, Units.val_one]
  exact blk_one_one

theorem k2a_exists_lift_sq_one {t : StatedProj (StatedSp 2 K)} (c : ∃ g, g⁻¹ * t * g = u1 K) :
    ∃ T : StatedSp 2 K, proj 2 K T = t ∧ T * T = 1 := by
  obtain ⟨g, hg⟩ := c
  obtain ⟨G, rfl⟩ := proj_surjective g
  refine ⟨G * T1 K * G⁻¹, ?_, ?_⟩
  · have ht : t = proj 2 K G * u1 K * (proj 2 K G)⁻¹ := by
      rw [← hg]
      group
    have hu : proj 2 K (T1 K) = u1 K := rfl
    rw [ht, map_mul, map_mul, map_inv, hu]
  · calc G * T1 K * G⁻¹ * (G * T1 K * G⁻¹) = G * (T1 K * T1 K) * G⁻¹ := by group
      _ = 1 := by rw [k2a_T1_mul_T1]; group

theorem k2a_one_ne_neg_one (h2 : (2 : K) ≠ 0) :
    (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ -1 := by
  intro h
  have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
  simp only [one_apply_eq, Matrix.neg_apply] at this
  exact h2 (by linear_combination this)

theorem k2a_core (h2 : (2 : K) ≠ 0) {T : StatedSp 2 K} (hTT : T * T = 1)
    (hT1 : proj 2 K T ≠ 1) (hne : u1 K ≠ proj 2 K T)
    (hc : u1 K * proj 2 K T = proj 2 K T * u1 K) :
    ¬ ∃ g, g⁻¹ * (u1 K * proj 2 K T) * g = u1 K := by
  have hcomm : proj 2 K (T1 K) * proj 2 K T = proj 2 K T * proj 2 K (T1 K) := hc
  have hsc := conj_mem_spScalars_of_commute (A := T1 K) (T := T) hcomm
  have hT1inv : (T1 K)⁻¹ = T1 K := inv_eq_of_mul_eq_one_right k2a_T1_mul_T1
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right hTT
  rw [hT1inv, hTinv] at hsc
  rcases (mem_spScalars_iff _).mp hsc with hc1 | hc1
  ·
    exfalso
    have h1 : T1 K * T * T1 K * T = 1 := sp_ext hc1
    have hcent : T ∈ centralizer {T1 K} := by
      rw [mem_centralizer_singleton_iff]
      have h3 : T1 K * T = (T1 K * T)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by simpa only [mul_assoc] using h1)
      rw [_root_.mul_inv_rev, hTinv, hT1inv] at h3
      exact h3.symm
    obtain ⟨⟨g, h⟩, rfl⟩ := (mem_centralizer_T1_iff h2).mp hcent
    have hmat := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hTT
    simp only [Subgroup.coe_mul, Units.val_mul, coe_blkSL, blk_mul, Subgroup.coe_one,
      Units.val_one] at hmat
    rw [← blk_one_one] at hmat
    obtain ⟨hgg, hhh⟩ := blk_injective _ _ _ _ hmat
    rcases eq_one_or_neg_one_of_sq h2 g.2 hgg with hg1 | hg1 <;>
      rcases eq_one_or_neg_one_of_sq h2 h.2 hhh with hh1 | hh1
    · exact hT1 ((proj_blkSL_eq_one_iff _).mpr (Or.inl ⟨hg1, hh1⟩))
    · have e1 : g = 1 := Subtype.ext hg1
      have e2 : h = negOneSL := Subtype.ext hh1
      subst e1 e2
      exact hne u1_eq_proj_blkSL
    · have e1 : g = negOneSL := Subtype.ext hg1
      have e2 : h = 1 := Subtype.ext hh1
      subst e1 e2
      exact hne u1_eq_proj_blkSL'
    · exact hT1 ((proj_blkSL_eq_one_iff _).mpr (Or.inr ⟨hg1, hh1⟩))
  ·
    rintro ⟨g', hg'⟩
    obtain ⟨G, rfl⟩ := proj_surjective g'
    obtain ⟨a, ha⟩ : ∃ a : StatedSp 2 K, a = G⁻¹ * (T1 K * T) * G := ⟨_, rfl⟩
    have hprojx : proj 2 K (T1 K * T) = u1 K * proj 2 K T := by rw [map_mul]; rfl
    have hproj : proj 2 K a = proj 2 K (T1 K) := by
      rw [ha, map_mul, map_mul, map_inv, hprojx]
      exact hg'
    have hcen : G⁻¹ * (T1 K * T * T1 K * T) = (T1 K * T * T1 K * T) * G⁻¹ :=
      mem_center_iff.mp (mem_center_of_mem_spScalars hsc) G⁻¹
    have hsq : a * a = T1 K * T * T1 K * T := by
      rw [ha]
      calc G⁻¹ * (T1 K * T) * G * (G⁻¹ * (T1 K * T) * G)
          = G⁻¹ * (T1 K * T * T1 K * T) * G := by group
        _ = T1 K * T * T1 K * T := by rw [hcen]; group
    have hmat : (((a * a : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
      rw [hsq]
      exact hc1
    have hT1sq : (((T1 K * T1 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      rw [k2a_T1_mul_T1]
      rfl
    have key : (((T1 K * T1 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (((a * a : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      simp only [Subgroup.coe_mul, Units.val_mul]
      rcases eq_or_eq_neg_of_proj_eq hproj with h3 | h3
      · rw [h3]
      · rw [h3, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    exact k2a_one_ne_neg_one h2 (hT1sq.symm.trans (key.trans hmat))

theorem k2a_not_conj_u1_mul_u1 (h2 : (2 : K) ≠ 0) {t : StatedProj (StatedSp 2 K)}
    (hc : u1 K * t = t * u1 K) (hne : u1 K ≠ t) (c : ∃ g, g⁻¹ * t * g = u1 K) :
    ¬ ∃ g, g⁻¹ * (u1 K * t) * g = u1 K := by
  obtain ⟨T, rfl, hTT⟩ := k2a_exists_lift_sq_one c
  have hT1 : proj 2 K T ≠ 1 := by
    intro h
    obtain ⟨g, hg⟩ := c
    rw [h] at hg
    apply u1_ne_one h2
    rw [← hg]
    group
  exact k2a_core h2 hTT hT1 hne hc

end K2a

theorem not_conj_u1_mul {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    {t₁ t₂ : StatedProj (StatedSp 2 K)} (hc : t₁ * t₂ = t₂ * t₁) (hne : t₁ ≠ t₂)
    (h1 : orderOf t₁ = 2) (h2 : orderOf t₂ = 2)
    (c1 : ∃ g, g⁻¹ * t₁ * g = u1 K) (c2 : ∃ g, g⁻¹ * t₂ * g = u1 K) :
    ¬ ∃ g, g⁻¹ * (t₁ * t₂) * g = u1 K := by
  have h2K : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatFactsSp4.two_ne_zero_of_odd_card hodd
  obtain ⟨g₁, hg₁⟩ := c1
  obtain ⟨g₂, hg₂⟩ := c2
  have hct : u1 K * (g₁⁻¹ * t₂ * g₁) = (g₁⁻¹ * t₂ * g₁) * u1 K := by
    rw [← hg₁]
    calc g₁⁻¹ * t₁ * g₁ * (g₁⁻¹ * t₂ * g₁) = g₁⁻¹ * (t₁ * t₂) * g₁ := by group
      _ = g₁⁻¹ * (t₂ * t₁) * g₁ := by rw [hc]
      _ = g₁⁻¹ * t₂ * g₁ * (g₁⁻¹ * t₁ * g₁) := by group
  have hne' : u1 K ≠ g₁⁻¹ * t₂ * g₁ := by
    intro h
    apply hne
    rw [← hg₁] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hc' : ∃ g, g⁻¹ * (g₁⁻¹ * t₂ * g₁) * g = u1 K :=
    ⟨g₁⁻¹ * g₂, by rw [← hg₂]; group⟩
  rintro ⟨g, hg⟩
  refine k2a_not_conj_u1_mul_u1 h2K hct hne' hc' ⟨g₁⁻¹ * g, ?_⟩
  calc (g₁⁻¹ * g)⁻¹ * (u1 K * (g₁⁻¹ * t₂ * g₁)) * (g₁⁻¹ * g)
      = (g₁⁻¹ * g)⁻¹ * ((g₁⁻¹ * t₁ * g₁) * (g₁⁻¹ * t₂ * g₁)) * (g₁⁻¹ * g) := by rw [hg₁]
    _ = g⁻¹ * (t₁ * t₂) * g := by group
    _ = u1 K := hg

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
