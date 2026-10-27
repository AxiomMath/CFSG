module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PieceAction
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem perfect_hom_eq_one {P S : Type*} [Group P] [Group.IsPerfect P] [Group S]
    [Group.IsSolvable S] (φ : P →* S) (x : P) : φ x = 1 := by
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  by_contra hx
  have : Nontrivial φ.range := ⟨⟨⟨φ x, x, rfl⟩, 1, fun h => hx (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable (G := φ.range) inferInstance

theorem generalLinearGroup_comm_of_finrank_eq_one {M : Type*} [AddCommGroup M] [Module K M]
    (h1 : finrank K M = 1) (a b : LinearMap.GeneralLinearGroup K M) : a * b = b * a := by
  obtain ⟨c, hc⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
    (a : Module.End K M)).exists
  obtain ⟨d, hd⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
    (b : Module.End K M)).exists
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hc, hd]
  ext x
  simp [Module.End.mul_apply, smul_comm d c x]

theorem perfect_trivial_on_piece_of_solvable {F F' : Submodule K V}
    [Group.IsSolvable (LinearMap.GeneralLinearGroup K (PieceQ F F'))]
    (Δ : Subgroup (LinearMap.GeneralLinearGroup K V))
    (hperf : ⁅Δ, Δ⁆ = Δ) (hF : ∀ d ∈ Δ, ∀ v ∈ F, (d : Module.End K V) v ∈ F)
    (hF' : ∀ d ∈ Δ, ∀ v ∈ F', (d : Module.End K V) v ∈ F') :
    ∀ d ∈ Δ, ∀ v ∈ F', (d : Module.End K V) v - v ∈ F := by
  have hmem : ∀ d ∈ Δ, d ∈ stabPair F F' := fun d hd =>
    ⟨hF d hd, hF' d hd, hF d⁻¹ (Δ.inv_mem hd), hF' d⁻¹ (Δ.inv_mem hd)⟩
  have hle : Δ ≤ stabPair F F' := hmem
  have : Group.IsPerfect Δ := Subgroup.isPerfect_iff.mpr hperf
  let ψ : Δ →* LinearMap.GeneralLinearGroup K (PieceQ F F') :=
    (quotGL F F').comp (Subgroup.inclusion hle)
  intro d hd v hv
  have h2 : ψ ⟨d, hd⟩ = 1 := perfect_hom_eq_one ψ ⟨d, hd⟩
  have h3 := congrArg (fun g : LinearMap.GeneralLinearGroup K (PieceQ F F') =>
    (g : Module.End K (PieceQ F F')) (Submodule.Quotient.mk (⟨v, hv⟩ : ↥F'))) h2
  simp only [Units.val_one, Module.End.one_apply] at h3
  change quotEnd F F' ⟨d, hmem d hd⟩ (Submodule.Quotient.mk ⟨v, hv⟩) = _ at h3
  rw [quotEnd_mk, Submodule.Quotient.eq] at h3
  simpa [Submodule.mem_comap] using h3

theorem perfect_trivial_on_line_piece {F F' : Submodule K V}
    (h1 : finrank K (PieceQ F F') = 1) (Δ : Subgroup (LinearMap.GeneralLinearGroup K V))
    (hperf : ⁅Δ, Δ⁆ = Δ) (hF : ∀ d ∈ Δ, ∀ v ∈ F, (d : Module.End K V) v ∈ F)
    (hF' : ∀ d ∈ Δ, ∀ v ∈ F', (d : Module.End K V) v ∈ F') :
    ∀ d ∈ Δ, ∀ v ∈ F', (d : Module.End K V) v - v ∈ F :=
  have : Group.IsSolvable (LinearMap.GeneralLinearGroup K (PieceQ F F')) :=
    Group.isSolvable_of_comm (generalLinearGroup_comm_of_finrank_eq_one h1)
  perfect_trivial_on_piece_of_solvable Δ hperf hF hF'

end CFSG.HardMathSupport.Curtis.UnitaryLevi
