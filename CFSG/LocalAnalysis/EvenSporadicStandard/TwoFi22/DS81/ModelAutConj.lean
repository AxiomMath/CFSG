module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

namespace AutConj

theorem exists_conj_eq_of_unique {G : Type*} [Group G] [Finite G] {V N T : Subgroup G}
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVcard : Nat.card V = 2 ^ 10) (T' : Sylow 2 G)
    (hT : (T' : Subgroup G) = T)
    (hcp : ∀ A : Subgroup G, A ≤ T → (∀ a ∈ A, a ^ 2 = 1) → 2 ^ 10 ≤ Nat.card A → A ≤ N)
    (hNcard : Nat.card N = 2 ^ 10) :
    ∃ g : G, V = N.map (MulAut.conj g).toMonoidHom := by
  have hVp : IsPGroup 2 V := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hV2 x x.2
  obtain ⟨Q, hVQ⟩ := hVp.exists_le_sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T' Q
  have hconj : ∀ v ∈ V, g⁻¹ * v * g ∈ T := by
    intro v hv
    have h1 : v ∈ (Q : Subgroup G) := hVQ hv
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, hT] at h1
    simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply] using h1
  set V' : Subgroup G := V.map (MulAut.conj g⁻¹).toMonoidHom with hV'
  have hV'T : V' ≤ T := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using hconj v hv
  have hV'sq : ∀ b ∈ V', b ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, hV2 v hv, map_one]
  have hV'card : Nat.card V' = 2 ^ 10 := by
    rw [hV', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hVcard]
  have hV'N : V' ≤ N := hcp V' hV'T hV'sq (by rw [hV'card])
  have hVN : V' = N := Subgroup.eq_of_le_of_card_ge hV'N (by rw [hV'card, hNcard])
  refine ⟨g, ?_⟩
  rw [← hVN, hV', Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp,
    MonoidHom.coe_ofClass, Function.comp_apply, MulAut.conj_apply, inv_inv]
  constructor
  · intro hx
    exact ⟨x, hx, by group⟩
  · rintro ⟨y, hy, rfl⟩
    have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [this]

end AutConj

end CFSG.EvenSporadicStandard.TwoFi22.DS81
