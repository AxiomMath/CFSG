module

public import CFSG.LargeExtraspecial.DW2ModFactor
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev rad (f : LinearMap.BilinForm (ZMod 2) V) (W : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  W ⊓ f.orthogonal W

theorem exists_unique_ne_zero_of_finrank_eq_one {L : Submodule (ZMod 2) V}
    (hL : finrank (ZMod 2) L = 1) : ∃ l ∈ L, l ≠ 0 ∧ ∀ x ∈ L, x ≠ 0 → x = l := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hL
  refine ⟨v, v.2, fun h => hv0 (Subtype.ext h), fun x hx hx0 => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
  have hc' : c • (v : V) = x := congrArg Subtype.val hc
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul] at hc'
    exact absurd hc'.symm hx0
  · rw [one_smul] at hc'
    exact hc'.symm

theorem apply_mem_commSpace_of_commute {c g : V ≃ₗ[ZMod 2] V} (hcg : c * g = g * c) {x : V}
    (hx : x ∈ commSpace g) : c x ∈ commSpace g := by
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  refine mem_commSpace.mpr ⟨c v, ?_⟩
  rw [map_sub, ← LinearEquiv.mul_apply, ← hcg, LinearEquiv.mul_apply]

theorem orth_top_eq_bot {f : LinearMap.BilinForm (ZMod 2) V} (hf : f.Nondegenerate) :
    f.orthogonal ⊤ = ⊥ :=
  eq_bot_iff.mpr fun v hv => (mem_bot (ZMod 2)).mpr
    (hf.2 v fun u => LinearMap.BilinForm.mem_orthogonal_iff.mp hv u mem_top)

section TwoTwo

variable [FiniteDimensional (ZMod 2) V] {Y : Subgroup (V ≃ₗ[ZMod 2] V)}
  {f : LinearMap.BilinForm (ZMod 2) V}

theorem le_orth_stab_of_isUnip (hY : Y ≤ TauCeti.BilinForm.isometryGroup f)
    {W : Submodule (ZMod 2) V} (hW : IsInv Y W) (h : IsUnip Y ⊥ W) :
    W ≤ f.orthogonal (stab Y ⊤) := by
  obtain ⟨k, hk⟩ := h
  intro w hw
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  rw [← iterComm_eq_stab isInv_top (le_max_right k (finrank (ZMod 2) V))] at hu
  refine (iterComm_orth_iff hY _).mpr ?_ u hu w hw
  intro a _ b hb
  have hb0 : b ∈ (⊥ : Submodule (ZMod 2) V) := hk (iterComm_antitone hW (le_max_left _ _) hb)
  rw [mem_bot] at hb0
  rw [hb0, map_zero]

theorem isUnip_orth_stab (hf : f.Nondegenerate) (hr : f.IsRefl)
    (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) : IsUnip Y ⊥ (f.orthogonal (stab Y ⊤)) := by
  rw [← orth_top_eq_bot hf]
  exact (isUnip_orth_iff hf hr hY).mpr (isUnip_stab ⊤)

theorem not_isUnip_stab (hnu : ¬ IsUnip Y ⊥ ⊤) : ¬ IsUnip Y ⊥ (stab Y ⊤) := by
  intro h
  rw [isUnip_bot_stab_iff isInv_top] at h
  exact hnu (h ▸ isUnip_stab ⊤)

variable (hf : f.Nondegenerate) (hr : f.IsRefl) (hY : Y ≤ TauCeti.BilinForm.isometryGroup f)
include hf hr hY

theorem isUnip_rad_stab (h1 : OneFactor Y) : IsUnip Y ⊥ (rad f (stab Y ⊤)) := by
  have hU := isInv_stab (Y := Y) isInv_top
  have hUp := isInv_orth hY hU
  have hnu := not_isUnip_stab h1.not_isUnip
  rcases h1.dichotomy (hU.inf hUp) bot_le le_top with h | h
  · exact h
  · exfalso
    have hle : stab Y ⊤ ≤ f.orthogonal (stab Y ⊤) :=
      (h.stab_le (hU.inf hUp) isInv_top).trans inf_le_right
    rcases h1.dichotomy hUp bot_le le_top with h' | h'
    · exact hnu (h'.mono le_rfl hle)
    · exact hnu ((isUnip_orth_top_iff hf hr hY).mp h')

theorem isNontrivFactor_rad_stab (h1 : OneFactor Y) :
    IsNontrivFactor Y (rad f (stab Y ⊤)) (stab Y ⊤) := by
  have hU := isInv_stab (Y := Y) isInv_top
  have hUp := isInv_orth hY hU
  have hnu := not_isUnip_stab h1.not_isUnip
  refine ⟨hU.inf hUp, hU, inf_le_left, ?_, ?_⟩
  · rw [commSub_stab isInv_top]
    intro hle
    exact hnu ((isUnip_rad_stab hf hr hY h1).mono le_rfl hle)
  · intro W hW hRW hWU
    rcases h1.dichotomy hW bot_le le_top with h | h
    · exact Or.inl (le_antisymm (le_inf hWU (le_orth_stab_of_isUnip hY hW h)) hRW)
    · exact Or.inr (le_antisymm hWU (h.stab_le hW isInv_top))

end TwoTwo

end CFSG.LargeExtraspecial.DW
