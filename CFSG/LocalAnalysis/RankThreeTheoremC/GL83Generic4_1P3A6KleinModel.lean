module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Model

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6Model

open Matrix Subgroup CFSG.Quasithin

private def xm (p q r : GF9) (h : p * p + q * r = -1) : SL29 :=
  ⟨!![p, q; r, -p], by rw [Matrix.det_fin_two_of]; linear_combination (-1 : GF9) * h⟩

private def KleinCond (a : GF9) (x : SL29) : Prop :=
  IsCentral (x * x) ∧ IsCentral ((um a * x * (um a)⁻¹) * (um a * x * (um a)⁻¹)) ∧
    IsCentral ((x * (um a * x * (um a)⁻¹))⁻¹ * ((um a * x * (um a)⁻¹) * x)) ∧
    IsCentral ((um a * (um a * x * (um a)⁻¹) * (um a)⁻¹)⁻¹ * (x * (um a * x * (um a)⁻¹))) ∧
    ∀ c : GF9, ¬ IsCentral ((x * um 1 * x⁻¹)⁻¹ * um c)

private instance (a : GF9) (x : SL29) : Decidable (KleinCond a x) := by
  unfold KleinCond
  infer_instance

private theorem klein_exists : ∀ a : GF9, a ≠ 0 →
    ∃ p q r : GF9, ∃ h : p * p + q * r = -1, KleinCond a (xm p q r h) := by
  decide +kernel

theorem klein_model (a : GF9) (ha : a ≠ 0) :
    ∃ x y : PSL29, x * x = 1 ∧ y * y = 1 ∧ x * y = y * x ∧ ut a * x * (ut a)⁻¹ = y ∧
      ut a * y * (ut a)⁻¹ = x * y ∧ x ∉ normalizer (uHom.range : Set PSL29) := by
  obtain ⟨p, q, r, h, h1, h2, h3, h4, h5⟩ := klein_exists a ha
  refine ⟨QuotientGroup.mk (xm p q r h),
    QuotientGroup.mk (um a * xm p q r h * (um a)⁻¹), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul, mk_eq_one_iff]
    exact h1
  · rw [← QuotientGroup.mk_mul, mk_eq_one_iff]
    exact h2
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_iff.mpr h3
  · change (QuotientGroup.mk (um a) : PSL29) * QuotientGroup.mk (xm p q r h) *
      (QuotientGroup.mk (um a))⁻¹ = _
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  · change (QuotientGroup.mk (um a) : PSL29) * QuotientGroup.mk (um a * xm p q r h * (um a)⁻¹) *
      (QuotientGroup.mk (um a))⁻¹ = _
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    exact mk_eq_iff.mpr h4
  · intro hn
    have h6 : (ut 1 : PSL29) ∈ (uHom.range : Set PSL29) := mem_range_iff.mpr ⟨1, rfl⟩
    obtain ⟨c, hc⟩ := mem_range_iff.mp ((mem_normalizer_iff.mp hn (ut 1)).mp h6)
    refine h5 c (mk_eq_iff.mp ?_)
    change (QuotientGroup.mk (xm p q r h * um 1 * (xm p q r h)⁻¹) : PSL29) = ut c
    rw [← hc]
    change _ = (QuotientGroup.mk (xm p q r h) : PSL29) * QuotientGroup.mk (um 1) *
      (QuotientGroup.mk (xm p q r h))⁻¹
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]

end CFSG.LocalAnalysis.RankThreeTheoremC.A6Model
