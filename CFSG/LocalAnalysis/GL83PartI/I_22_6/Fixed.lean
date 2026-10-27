module

public import Mathlib.GroupTheory.PGroup

public section

namespace GL83.CompFam

variable {Y : Type*} [Group Y]

theorem exists_ne_one_commute_of_isPGroup [Finite Y] {p : ℕ} [Fact p.Prime] {P V : Subgroup Y}
    (hP : IsPGroup p P) (hPV : P ≤ Subgroup.normalizer (V : Set Y)) (hV : p ∣ Nat.card V) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ c ∈ P, c * v = v * c := by
  let ψ : P →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hPV)
  letI : MulAction P V := MulAction.compHom V ψ
  have h1 : (1 : V) ∈ MulAction.fixedPoints P V := fun c => map_one (ψ c)
  obtain ⟨v, hv, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hV h1
  refine ⟨v, v.2, fun h => hne (Subtype.ext h.symm), fun c hc => ?_⟩
  have h2 : ψ ⟨c, hc⟩ v = v := hv ⟨c, hc⟩
  have h3 := congrArg (fun x : V => (x : Y)) h2
  simp only [ψ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
  have h4 : c * (v : Y) * c⁻¹ = v := h3
  calc c * (v : Y) = c * v * c⁻¹ * c := by group
    _ = v * c := by rw [h4]

end GL83.CompFam
