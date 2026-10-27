module

public import CFSG.Timmesfeld.Transvection.QuadFormBasic
public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Module QuadraticMap CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem finrank_le_two_of_anisotropic (Q : QuadraticForm (ZMod 2) V)
    {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, Q w = 0 → w = 0) :
    finrank (ZMod 2) W ≤ 2 := by
  have hA : (Q.comp W.subtype).Anisotropic := by
    intro x hx
    exact Subtype.ext (hW x x.2 hx)
  exact CFSG.Timmesfeld.Transvection.QuadForm.finrank_le_two hA

theorem exists_singular_of_three_le (Q : QuadraticForm (ZMod 2) V) {W : Submodule (ZMod 2) V}
    (hW : 3 ≤ finrank (ZMod 2) W) : ∃ w ∈ W, w ≠ 0 ∧ Q w = 0 := by
  by_contra h
  push Not at h
  have := finrank_le_two_of_anisotropic Q (W := W) fun w hw hq => by
    by_contra h0
    exact h w hw h0 hq
  omega

theorem exists_hyperbolic_pair [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {U : Submodule (ZMod 2) V}
    (hcodim : finrank (ZMod 2) V ≤ finrank (ZMod 2) U + 2) (h5 : 5 ≤ finrank (ZMod 2) U) :
    ∃ α ∈ U, ∃ β ∈ U, α ≠ 0 ∧ Q α = 0 ∧ Q β = 0 ∧ polar Q α β = 1 := by
  set B := Q.polarBilin with hB
  set R := U ⊓ LinearMap.BilinForm.orthogonal B U with hR
  have hRle : finrank (ZMod 2) R ≤ 2 := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hQ U
    have h2 : finrank (ZMod 2) R ≤ finrank (ZMod 2) (LinearMap.BilinForm.orthogonal B U) :=
      Submodule.finrank_mono inf_le_right
    omega
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl R
  have hqd := Submodule.finrank_add_eq_of_isCompl hq
  have hW : 3 ≤ finrank (ZMod 2) ↥(q ⊓ U) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq q U
    have h2 := Submodule.finrank_le (q ⊔ U)
    omega
  obtain ⟨α, hαW, hα0, hQα⟩ := exists_singular_of_three_le Q hW
  have hαU : α ∈ U := hαW.2
  have hαR : α ∉ LinearMap.BilinForm.orthogonal B U := by
    intro h
    have : α ∈ R ⊓ q := ⟨⟨hαU, h⟩, hαW.1⟩
    rw [hq.inf_eq_bot, Submodule.mem_bot] at this
    exact hα0 this
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hαR
  push Not at hαR
  obtain ⟨β', hβ'U, hβ'⟩ := hαR
  have hp : polar Q α β' = 1 := by
    have h1 : polar Q β' α ≠ 0 := hβ'
    rw [polar_comm] at h1
    exact zmod2_eq_one_of_ne_zero h1
  rcases zmod2_eq_zero_or_eq_one (Q β') with h0 | h1
  · exact ⟨α, hαU, β', hβ'U, hα0, hQα, h0, hp⟩
  · refine ⟨α, hαU, β' + α, add_mem hβ'U hαU, hα0, hQα, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q β' α, h1, hQα, polar_comm, hp]
      decide
    · rw [polar_add_right, hp, polar_self, hQα, smul_zero, add_zero]

end CFSG.LargeExtraspecial.S7
