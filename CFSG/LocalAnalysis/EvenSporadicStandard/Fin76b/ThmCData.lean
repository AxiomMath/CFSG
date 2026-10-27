module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

@[expose] def OuterData (Y : Type*) [Group Y] : Prop :=
  ∀ S : Subgroup (MulAut Y), IsPGroup 2 S → ¬ 2 ∣ S.index →
    ∃ t : Y, t * t = 1 ∧ t ≠ 1 ∧ (∃ g : Y, g * g * (g * g) = t) ∧ MulAut.conj t ∈ S ∧
      ∀ α ∈ S, (∀ β ∈ S, β * α = α * β) ↔ (α = 1 ∨ α = MulAut.conj t)

theorem OuterData.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : OuterData X) : OuterData Y := by
  intro S hS hidx
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  let S' : Subgroup (MulAut X) := S.map φ.symm.toMonoidHom
  have hmem : ∀ β : MulAut X, β ∈ S' ↔ φ β ∈ S := by
    intro β
    constructor
    · rintro ⟨α, hα, rfl⟩
      simpa using hα
    · intro hβ
      exact ⟨φ β, hβ, by simp⟩
  have hS'p : IsPGroup 2 S' :=
    hS.of_equiv (Subgroup.equivMapOfInjective S φ.symm.toMonoidHom φ.symm.injective)
  have hS'idx : ¬ 2 ∣ S'.index := by
    have : S'.index = S.index := Subgroup.index_map_equiv (H := S) φ.symm
    rwa [this]
  obtain ⟨t, ht2, ht1, ⟨g, hg⟩, htS, hcen⟩ := h S' hS'p hS'idx
  have hconj : φ (MulAut.conj t) = MulAut.conj (e t) := by
    ext y
    simp [φ, MulAut.congr_apply]
  refine ⟨e t, by rw [← map_mul, ht2, map_one], fun h1 => ht1 (e.injective (by rw [h1, map_one])),
    ⟨e g, by simp only [← map_mul, hg]⟩, by rw [← hconj]; exact (hmem _).1 htS, ?_⟩
  intro α hα
  have hαmem : φ.symm α ∈ S' := (hmem _).2 (by simpa using hα)
  have key := hcen (φ.symm α) hαmem
  have hsymm : φ.symm α = MulAut.conj t ↔ α = MulAut.conj (e t) := by
    rw [← hconj]
    exact ⟨fun h1 => by rw [← h1]; simp, fun h1 => by rw [h1]; simp⟩
  have hone : φ.symm α = 1 ↔ α = 1 :=
    ⟨fun h1 => by simpa using congrArg φ h1, fun h1 => by rw [h1, map_one]⟩
  have hA : (∀ β ∈ S, β * α = α * β) ↔ ∀ β' ∈ S', β' * φ.symm α = φ.symm α * β' := by
    constructor
    · intro hc β' hβ'
      have h1 := hc (φ β') ((hmem _).1 hβ')
      simpa using congrArg φ.symm h1
    · intro hc β hβ
      have h1 := hc (φ.symm β) ((hmem _).2 (by simpa using hβ))
      simpa using congrArg φ h1
  rw [hA, key, hone, hsymm]

theorem OuterData.of_sylow {Y : Type*} [Group Y] [Finite (MulAut Y)]
    (S₀ : Subgroup (MulAut Y)) (hS₀p : IsPGroup 2 S₀) (hS₀idx : ¬ 2 ∣ S₀.index)
    (h : ∃ t : Y, t * t = 1 ∧ t ≠ 1 ∧ (∃ g : Y, g * g * (g * g) = t) ∧ MulAut.conj t ∈ S₀ ∧
      ∀ α ∈ S₀, (∀ β ∈ S₀, β * α = α * β) ↔ (α = 1 ∨ α = MulAut.conj t)) :
    OuterData Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS hidx
  obtain ⟨t, ht2, ht1, ⟨g, hg⟩, htS, hcen⟩ := h
  let P1 : Sylow 2 (MulAut Y) := hS₀p.toSylow hS₀idx
  let P2 : Sylow 2 (MulAut Y) := hS.toSylow hidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (MulAut Y) P1 P2
  have hmem : ∀ α : MulAut Y, α ∈ S ↔ c⁻¹ * α * c ∈ S₀ := by
    intro α
    have h1 : (P2 : Subgroup (MulAut Y)) = MulAut.conj c • (P1 : Subgroup (MulAut Y)) := by
      rw [← hc, Sylow.coe_subgroup_smul]
    have h2 : α ∈ (P2 : Subgroup (MulAut Y)) ↔
        (MulAut.conj c)⁻¹ • α ∈ (P1 : Subgroup (MulAut Y)) := by
      rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h3 : (P2 : Subgroup (MulAut Y)) = S := rfl
    have h4 : (P1 : Subgroup (MulAut Y)) = S₀ := rfl
    rw [h3, h4] at h2
    rw [h2]
    simp [MulAut.smul_def, mul_assoc]
  refine ⟨c t, by rw [← map_mul, ht2, map_one],
    fun h1 => ht1 (c.injective (by rw [h1, map_one])), ⟨c g, by simp only [← map_mul, hg]⟩, ?_, ?_⟩
  · rw [hmem]
    have : c⁻¹ * MulAut.conj (c t) * c = MulAut.conj t := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rwa [this]
  · intro α hα
    have hαS : c⁻¹ * α * c ∈ S₀ := (hmem α).1 hα
    have key := hcen (c⁻¹ * α * c) hαS
    have hconj : c⁻¹ * MulAut.conj (c t) * c = MulAut.conj t := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    have hA : (∀ β ∈ S, β * α = α * β) ↔ ∀ β' ∈ S₀, β' * (c⁻¹ * α * c) = (c⁻¹ * α * c) * β' := by
      constructor
      · intro hc' β' hβ'
        have hβS : c * β' * c⁻¹ ∈ S := (hmem _).2 (by simpa [mul_assoc] using hβ')
        have h1 := hc' _ hβS
        have h2 := congrArg (fun x => c⁻¹ * x * c) h1
        simpa [mul_assoc] using h2
      · intro hc' β hβ
        have h1 := hc' (c⁻¹ * β * c) ((hmem _).1 hβ)
        have h2 := congrArg (fun x => c * x * c⁻¹) h1
        simpa [mul_assoc] using h2
    have hB : (c⁻¹ * α * c = 1 ∨ c⁻¹ * α * c = MulAut.conj t) ↔
        (α = 1 ∨ α = MulAut.conj (c t)) := by
      constructor
      · rintro (h1 | h1)
        · left
          have : α = c * (c⁻¹ * α * c) * c⁻¹ := by group
          rw [this, h1]; group
        · right
          have : α = c * (c⁻¹ * α * c) * c⁻¹ := by group
          rw [this, h1, ← hconj]; group
      · rintro (h1 | h1)
        · left; rw [h1]; group
        · right; rw [h1, hconj]
    rw [hA, key, hB]

end CFSG.EvenSporadicStandard.Fin76b
