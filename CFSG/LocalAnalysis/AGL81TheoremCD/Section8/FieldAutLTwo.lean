module

public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.RankThree.PartTwo.KFacts.K72L3Group
import CFSG.RankThree.PartTwo.KFacts.K72Invert
import CFSG.RankThree.PartTwo.KFacts.K72List

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.RankThree.PartTwo.KFacts

theorem fixedData_of_mulEquiv_psl2 {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    (h3 : (3 : F) ≠ 0) (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (α : MulAut X) (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∃ x₀ y₀ : X, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hβout : ¬ IsInnerAut (MulAut.congr e α) := by rwa [isInnerAut_congr]
  obtain ⟨σ, hσ3, ⟨c⟩⟩ := exists_eqLocus_mulEquiv_psl2 hβ3 hβout
  set F₀ := GH74.GLS.IVK.fixedField σ
  have hF : Nat.card F = Nat.card F₀ ^ 3 := by
    rw [← hσ3]
    exact (GH74.GLS.IVK.fixedField_card_pow σ).symm
  have h3₀ : (3 : F₀) ≠ 0 := fun h => h3 (by
    have h1 : F₀.subtype (3 : F₀) = F₀.subtype 0 := by rw [h]
    rwa [map_ofNat, map_zero] at h1)
  obtain ⟨d, hd⟩ := exists_orderOf_eq_three_psl2 F₀
  have hd3 : d ^ 3 = 1 := hd ▸ pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := fun h => by rw [h, orderOf_one] at hd; norm_num at hd
  obtain ⟨y, hy⟩ := exists_mul_mul_inv_eq_inv_psl2 h3₀ hd3 hd1
  have hc3 : c.symm d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hcinv : c.symm y * c.symm d * (c.symm y)⁻¹ = (c.symm d)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hy, map_inv]
  refine fixedData_of_congr e α ⟨Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀),
    fun T hT => ?_, three_mul_card_psl2_subfield_dvd F₀ rfl hF⟩
    ⟨c.symm d, c.symm y, (c.symm d).2, (c.symm y).2, ?_, ?_, ?_⟩
  ·
    have hle : T ≤ (MulAut.congr e α).toMonoidHom.eqLocus (MonoidHom.id _) := fun t ht => hT t ht
    rw [← Nat.card_congr c.toEquiv]
    exact Subgroup.card_dvd_of_le hle
  · rw [← Subgroup.coe_pow, hc3, Subgroup.coe_one]
  · intro h
    apply hd1
    have h1 : c.symm d = 1 := Subtype.ext h
    rw [← c.apply_symm_apply d, h1, map_one]
  · rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcinv, Subgroup.coe_inv]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
