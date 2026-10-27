module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5AutFour
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.ComponentClassification.Foote5

theorem isKleinFour_map_of_injective {K K' : Type*} [Group K] [Group K'] {f : K →* K'}
    (hf : Function.Injective f) {V : Subgroup K} (hV : IsKleinFour V) : IsKleinFour (V.map f) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [Subgroup.card_map_of_injective hf, hV.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hV hv, map_one]

theorem not_isKleinFour_of_centralizer {Y : Type} [Group Y] [Finite Y] (hY : FooteSimpleType Y)
    (hconj : Function.Injective (MulAut.conj : Y →* MulAut Y)) {W : Subgroup Y}
    (hcent : ∀ a : Y, a * a = 1 → (∀ w ∈ W, a * w = w * a) → a ∈ W) {γ : MulAut Y}
    (hγ : ∀ w ∈ W, γ w = w → w = 1) {E : Subgroup (MulAut Y)}
    (hE : ∀ α ∈ E, α * γ = γ * α ∧ ∀ w ∈ W, α w = w) : ¬ IsKleinFour E := by
  intro hE4
  have hV2 : ∀ α ∈ E, α * α = 1 := fun α hα => by
    have h := FooteLit.sq_eq_one_of_isKleinFour hE4 hα
    rwa [sq] at h
  have hne := fourgroup_inf_innAut_ne_bot hY hE4.card_four hV2
  obtain ⟨⟨α, hαE, a, ha⟩, hα1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ha1 : a ≠ 1 := fun h => hα1 (Subtype.ext (by
    change α = 1
    rw [← ha, h, map_one]))
  obtain ⟨hcomm, hfix⟩ := hE α hαE
  rw [← ha] at hcomm hfix
  have haa : a * a = 1 := hconj (by rw [map_mul, ha, hV2 α hαE, map_one])
  have haW : ∀ w ∈ W, a * w = w * a := fun w hw => by
    have h := hfix w hw
    rw [MulAut.conj_apply] at h
    calc a * w = a * w * a⁻¹ * a := by group
      _ = w * a := by rw [h]
  have hγa : MulAut.conj a = MulAut.conj (γ a) := by
    ext z
    have h1 := congrArg (fun φ : MulAut Y => φ (γ.symm z)) hcomm
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h1
    rw [MulAut.conj_apply, MulAut.conj_apply]
    exact h1
  exact ha1 (hγ a (hcent a haa haW) (hconj hγa).symm)

end CFSG.ComponentClassification.Sol78
