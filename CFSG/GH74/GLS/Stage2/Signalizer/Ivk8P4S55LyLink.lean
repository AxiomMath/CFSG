module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CoverConj
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.LyLink

open Subgroup CFSG.Sporadic.Recognition.LyonsSims

theorem ly_conj_threeSeven
    {Y : Type} [Group Y] [Finite Y]
    (hY : Blueprint.NativeSporadic.IsSporadic Y .Ly) {τ y s τ' y' s' : Y}
    (hτ : orderOf τ = 2) (hy : orderOf y = 3) (hs : orderOf s = 7)
    (hyτ : y * τ = τ * y) (hsτ : s * τ = τ * s) (hys : y * s = s * y)
    (hτ' : orderOf τ' = 2) (hy' : orderOf y' = 3) (hs' : orderOf s' = 7)
    (hyτ' : y' * τ' = τ' * y') (hsτ' : s' * τ' = τ' * s') (hys' : y' * s' = s' * y') :
    ∃ g : Y, g * y * g⁻¹ = y' := by
  obtain ⟨e⟩ := id hY
  have hconj : ∀ u v : Y, orderOf u = 2 → orderOf v = 2 → IsConj u v := fun u v hu hv =>
    isConj_of_equiv_of_involutions e (fun u v hu hv => ly_isConj_of_involutions hu hv) hu hv
  obtain ⟨h, hh⟩ := isConj_iff.1 (hconj τ τ' hτ hτ')
  have hcomm : ∀ x : Y, x * τ = τ * x → (h * x * h⁻¹) * τ' = τ' * (h * x * h⁻¹) := by
    intro x hx
    rw [← hh]
    calc h * x * h⁻¹ * (h * τ * h⁻¹) = h * (x * τ) * h⁻¹ := by group
      _ = h * (τ * x) * h⁻¹ := by rw [hx]
      _ = h * τ * h⁻¹ * (h * x * h⁻¹) := by group
  have hord : ∀ x : Y, orderOf (h * x * h⁻¹) = orderOf x := fun x => by
    have := MulEquiv.orderOf_eq (MulAut.conj h) x
    simpa [MulAut.conj_apply] using this
  have hyy : (h * y * h⁻¹) * (h * s * h⁻¹) = (h * s * h⁻¹) * (h * y * h⁻¹) := by
    calc h * y * h⁻¹ * (h * s * h⁻¹) = h * (y * s) * h⁻¹ := by group
      _ = h * (s * y) * h⁻¹ := by rw [hys]
      _ = h * s * h⁻¹ * (h * y * h⁻¹) := by group
  obtain ⟨-, hZ, ⟨E⟩⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ τ' hτ'
  have hτ'C : τ' ∈ centralizer ({τ'} : Set Y) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have htZ : (⟨τ', hτ'C⟩ : ↥(centralizer ({τ'} : Set Y))) ∈
      center ↥(centralizer ({τ'} : Set Y)) := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have ht2 : orderOf (⟨τ', hτ'C⟩ : ↥(centralizer ({τ'} : Set Y))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hτ'
  have hyC : h * y * h⁻¹ ∈ centralizer ({τ'} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm y hyτ)
  have hsC : h * s * h⁻¹ ∈ centralizer ({τ'} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm s hsτ)
  have hy'C : y' ∈ centralizer ({τ'} : Set Y) := Subgroup.mem_centralizer_singleton_iff.2 hyτ'
  have hs'C : s' ∈ centralizer ({τ'} : Set Y) := Subgroup.mem_centralizer_singleton_iff.2 hsτ'
  obtain ⟨g, hg⟩ := CoverConj.conj_of_order_three_seven htZ ht2 hZ E
    (z := ⟨h * y * h⁻¹, hyC⟩) (w := ⟨h * s * h⁻¹, hsC⟩) (z' := ⟨y', hy'C⟩) (w' := ⟨s', hs'C⟩)
    (by rw [Subgroup.orderOf_mk, hord, hy]) (by rw [Subgroup.orderOf_mk, hord, hs])
    (Subtype.ext hyy) (by rw [Subgroup.orderOf_mk, hy']) (by rw [Subgroup.orderOf_mk, hs'])
    (Subtype.ext hys')
  refine ⟨(g : Y) * h, ?_⟩
  have h1 := congrArg Subtype.val hg
  calc (g : Y) * h * y * ((g : Y) * h)⁻¹ = (g : Y) * (h * y * h⁻¹) * (g : Y)⁻¹ := by group
    _ = y' := h1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.LyLink
