module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.ABGLocalTools Subgroup
open scoped Pointwise

theorem exists_sylow_map_eq {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (S : Sylow 2 B) :
    ∃ T : Sylow 2 A, (T : Subgroup A).map f = (S : Subgroup B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective f hf
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 A) := inferInstance
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B (T₁.mapSurjective hf) S
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨a • T₁, ?_⟩
  have h1 : ((a • T₁ : Sylow 2 A) : Subgroup A) = MulAut.conj a • (T₁ : Subgroup A) :=
    Sylow.coe_subgroup_smul
  have h3 : ((f a • T₁.mapSurjective hf : Sylow 2 B) : Subgroup B) =
      MulAut.conj (f a) • ((T₁.mapSurjective hf : Sylow 2 B) : Subgroup B) :=
    Sylow.coe_subgroup_smul
  rw [← hb, h3, h1, Sylow.coe_mapSurjective]
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨f t, ⟨t, ht, rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨MulAut.conj a • t, ⟨t, ht, rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩

theorem frattini_lift {C X : Type*} [Group C] [Group X] [Finite C] (π : C →* X)
    (hπ : Function.Surjective π) {T : Subgroup C} (hT : IsSylowOf 2 T ⊤) {nb : X}
    (hn : ∀ s : X, s ∈ T.map π ↔ nb * s * nb⁻¹ ∈ T.map π) :
    ∃ n ∈ normalizer (T : Set C), ∃ s ∈ T.map π, π n = s * nb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n₁, rfl⟩ := hπ nb
  set H : Subgroup C := (T.map π).comap π with hH
  have hTH : T ≤ H := fun t ht => ⟨t, ht, rfl⟩
  set T₂ : Subgroup C := T.map (MulAut.conj n₁).toMonoidHom with hT₂
  have hinj : Function.Injective (MulAut.conj n₁).toMonoidHom := (MulAut.conj n₁).injective
  have hT₂H : T₂ ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    show π (n₁ * t * n₁⁻¹) ∈ T.map π
    rw [map_mul, map_mul, map_inv]
    exact (hn _).1 ⟨t, ht, rfl⟩
  have hT' : IsSylowOf 2 T H := by
    rw [isSylowOf_iff] at hT ⊢
    obtain ⟨-, hp, hdvd⟩ := hT
    refine ⟨hTH, hp, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex T H ⊤ hTH le_top
    rw [Subgroup.relIndex_top_right] at h1
    intro h2
    have h3 : 2 ∣ T.relIndex H * H.index := Dvd.dvd.mul_right h2 _
    rw [h1] at h3
    exact hdvd h3
  have hT₂' : IsSylowOf 2 T₂ H := by
    refine isSylowOf_of_card hT₂H ?_
    rw [hT₂, Subgroup.card_map_of_injective hinj]
    exact hT'.card_eq
  obtain ⟨k, hk, hkconj⟩ := hT'.exists_mem_conj hT₂'
  have hT₂mem : ∀ t : C, n₁ * t * n₁⁻¹ ∈ T₂ ↔ t ∈ T := by
    intro t
    constructor
    · rintro ⟨t', ht', h⟩
      have h' : t' = t := hinj (by simpa [MulAut.conj_apply] using h)
      rw [← h']
      exact ht'
    · intro ht
      exact ⟨t, ht, by simp [MulAut.conj_apply]⟩
  refine ⟨k⁻¹ * n₁, ?_, (π k)⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro t
    have h1 : (k⁻¹ * n₁) * t * (k⁻¹ * n₁)⁻¹ = k⁻¹ * (n₁ * t * n₁⁻¹) * k := by group
    rw [h1, ← hkconj, hT₂mem]
  · exact inv_mem hk
  · rw [map_mul, map_inv]

end CFSG.GH74.Generic.S45
