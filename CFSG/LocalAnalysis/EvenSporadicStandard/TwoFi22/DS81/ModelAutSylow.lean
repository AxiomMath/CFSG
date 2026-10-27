module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

namespace AutSylow

theorem rank_of_sylow {S : Type*} [Group S] [Finite S] {P R T : Subgroup S}
    (hRP : R ≤ normalizer (P : Set S)) (Q : Sylow 2 R) (hQ : (Q : Subgroup R) = T.subgroupOf R)
    {m : ℕ}
    (hTrank : ∀ A : Subgroup S, A ≤ T → (∀ a ∈ A, a ^ 2 = 1) → ¬ A ≤ P → Nat.card A ≤ m) :
    ∀ A : Subgroup S, A ≤ R → (∀ a ∈ A, a ^ 2 = 1) → ¬ A ≤ P → Nat.card A ≤ m := by
  intro A hAR hA2 hAP
  have hA'p : IsPGroup 2 (A.subgroupOf R) := by
    intro x
    refine ⟨1, ?_⟩
    have h := hA2 ((x : R) : S) (mem_subgroupOf.1 x.2)
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  obtain ⟨Q', hQ'⟩ := hA'p.exists_le_sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R Q Q'
  have hconj : ∀ a ∈ A, (g : S)⁻¹ * a * g ∈ T := by
    intro a ha
    have h1 : (⟨a, hAR ha⟩ : R) ∈ (Q' : Subgroup R) := hQ' (mem_subgroupOf.2 ha)
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, hQ,
      mem_subgroupOf] at h1
    simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply] using h1
  set A'' : Subgroup S := A.map (MulAut.conj (g : S)⁻¹).toMonoidHom with hA''
  have hA''T : A'' ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hconj a ha
  have hA''sq : ∀ b ∈ A'', b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA2 a ha, map_one]
  have hA''P : ¬ A'' ≤ P := by
    intro h
    apply hAP
    intro a ha
    have h1 : (g : S)⁻¹ * a * g ∈ P := by
      have := h ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using this
    have h2 := (mem_normalizer_iff.1 (hRP g.2) _).1 h1
    simpa [mul_assoc] using h2
  have hcard : Nat.card A'' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj (g : S)⁻¹).injective
  rw [← hcard]
  exact hTrank A'' hA''T hA''sq hA''P

end AutSylow

end CFSG.EvenSporadicStandard.TwoFi22.DS81
