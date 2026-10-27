module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LinePiece
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem sub_smul_mem_of_quotGL_eq {F F' : Submodule K V} {e : stabPair F F'} {c : K}
    (hc : ((quotGL F F' e : LinearMap.GeneralLinearGroup K (PieceQ F F')) :
      Module.End K (PieceQ F F')) = c • 1) :
    ∀ v ∈ F', ((e : LinearMap.GeneralLinearGroup K V) : Module.End K V) v - c • v ∈ F := by
  intro v hv
  have h1 := congrArg (fun T : Module.End K (PieceQ F F') =>
    T (Submodule.Quotient.mk (⟨v, hv⟩ : ↥F'))) hc
  simp only [coe_quotGL, quotEnd_mk, LinearMap.smul_apply, Module.End.one_apply] at h1
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h1
  simpa [Submodule.mem_comap] using h1

theorem exists_scalar_of_finrank_pieceQ_one {F F' : Submodule K V}
    (h1 : finrank K (PieceQ F F') = 1) (e : stabPair F F') :
    ∃ c : K, ∀ v ∈ F', ((e : LinearMap.GeneralLinearGroup K V) : Module.End K V) v - c • v ∈ F := by
  obtain ⟨c, hc⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
    ((quotGL F F' e : LinearMap.GeneralLinearGroup K (PieceQ F F')) :
      Module.End K (PieceQ F F'))).exists
  exact ⟨c, sub_smul_mem_of_quotGL_eq (e := e) (by rw [hc]; rfl)⟩

theorem trivial_on_piece_of_scalar {F F' : Submodule K V}
    {Δ : Subgroup (LinearMap.GeneralLinearGroup K V)} (hΔ : Δ ≤ stabPair F F')
    (hperf : ⁅Δ, Δ⁆ = Δ)
    (hs : ∀ (d : LinearMap.GeneralLinearGroup K V) (hd : d ∈ Δ), ∃ c : K,
      ((quotGL F F' ⟨d, hΔ hd⟩ : LinearMap.GeneralLinearGroup K (PieceQ F F')) :
      Module.End K (PieceQ F F')) = c • 1) :
    ∀ d ∈ Δ, ∀ v ∈ F', (d : Module.End K V) v - v ∈ F := by
  have : Group.IsPerfect Δ := Subgroup.isPerfect_iff.mpr hperf
  let φ : Δ →* LinearMap.GeneralLinearGroup K (PieceQ F F') :=
    (quotGL F F').comp (Subgroup.inclusion hΔ)
  have hcomm : ∀ a b : φ.range, a * b = b * a := by
    rintro ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩
    obtain ⟨c, hc⟩ := hs a.1 a.2
    obtain ⟨c', hc'⟩ := hs b.1 b.2
    refine Subtype.ext (Units.ext ?_)
    show ((φ a * φ b : LinearMap.GeneralLinearGroup K (PieceQ F F')) : Module.End K (PieceQ F F')) =
      ((φ b * φ a : LinearMap.GeneralLinearGroup K (PieceQ F F')) : Module.End K (PieceQ F F'))
    have e1 : ((φ a : LinearMap.GeneralLinearGroup K (PieceQ F F')) : Module.End K (PieceQ F F')) =
      c • 1 := hc
    have e2 : ((φ b : LinearMap.GeneralLinearGroup K (PieceQ F F')) : Module.End K (PieceQ F F')) =
      c' • 1 := hc'
    rw [Units.val_mul, Units.val_mul, e1, e2]
    simp only [mul_smul_comm, mul_one, smul_smul, mul_comm]
  have : Group.IsSolvable φ.range := Group.isSolvable_of_comm hcomm
  let φ' : Δ →* φ.range := φ.rangeRestrict
  intro d hd v hv
  have h2 : φ' ⟨d, hd⟩ = 1 := perfect_hom_eq_one φ' ⟨d, hd⟩
  have h3 : φ ⟨d, hd⟩ = 1 := congrArg Subtype.val h2
  have h4 := congrArg (fun g : LinearMap.GeneralLinearGroup K (PieceQ F F') =>
    (g : Module.End K (PieceQ F F')) (Submodule.Quotient.mk (⟨v, hv⟩ : ↥F'))) h3
  simp only [Units.val_one, Module.End.one_apply] at h4
  change quotEnd F F' ⟨d, hΔ hd⟩ (Submodule.Quotient.mk ⟨v, hv⟩) = _ at h4
  rw [quotEnd_mk, Submodule.Quotient.eq] at h4
  simpa [Submodule.mem_comap] using h4

end CFSG.HardMathSupport.Curtis.UnitaryLevi
