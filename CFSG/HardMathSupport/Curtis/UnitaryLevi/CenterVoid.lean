module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.Elementary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding.UnitaryLevi

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LinearGroups Matrix

theorem exists_mul_of_mem_sup_centralizer {Y : Type*} [Group Y] {L : Subgroup Y} {x : Y}
    (hx : x ∈ L ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ l ∈ L, ∃ z ∈ Subgroup.centralizer (L : Set Y), x = l * z := by
  have hcomm : ∀ l ∈ L, ∀ z ∈ Subgroup.centralizer (L : Set Y), z * l = l * z := fun l hl z hz =>
    (Subgroup.mem_centralizer_iff.mp hz l hl).symm
  let S : Subgroup Y :=
    { carrier := {x | ∃ l ∈ L, ∃ z ∈ Subgroup.centralizer (L : Set Y), x = l * z}
      one_mem' := ⟨1, L.one_mem, 1, Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, z₁, hz₁, rfl⟩ ⟨l₂, hl₂, z₂, hz₂, rfl⟩
        refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, z₁ * z₂, Subgroup.mul_mem _ hz₁ hz₂, ?_⟩
        calc l₁ * z₁ * (l₂ * z₂) = l₁ * (z₁ * l₂) * z₂ := by group
          _ = l₁ * (l₂ * z₁) * z₂ := by rw [hcomm l₂ hl₂ z₁ hz₁]
          _ = l₁ * l₂ * (z₁ * z₂) := by group
      inv_mem' := by
        rintro _ ⟨l, hl, z, hz, rfl⟩
        refine ⟨l⁻¹, L.inv_mem hl, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
        have h : Commute l z := (hcomm l hl z hz).symm
        calc (l * z)⁻¹ = z⁻¹ * l⁻¹ := by group
          _ = l⁻¹ * z⁻¹ := (Commute.inv_inv h).eq.symm }
  have hle : L ⊔ Subgroup.centralizer (L : Set Y) ≤ S := by
    refine sup_le (fun l hl => ⟨l, hl, 1, Subgroup.one_mem _, by simp⟩) fun z hz =>
      ⟨1, L.one_mem, z, hz, by simp⟩
  exact hle hx

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] [CharP K 2]
  in
theorem exists_lift {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (ρ : StatedSU n (2 ^ f) K →* ↥L) (hρs : Function.Surjective ρ)
    (hcompat : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K))
    {u : Y} (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)) {p : ℕ} (hup : u ^ p = 1)
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ∃ t : StatedSU n (2 ^ f) K, ((t : GL (Fin n) K)) ^ p ∈ StatedScalars (Fin n) K ∧
      ∀ g : StatedSU n (2 ^ f) K, Commute g t → ρ g ∈ J.subgroupOf L := by
  obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_of_mem_sup_centralizer hu
  obtain ⟨t, ht⟩ := hρs ⟨l, hl⟩
  have hzc : ∀ y ∈ L, z * y = y * z := fun y hy => (Subgroup.mem_centralizer_iff.mp hz y hy).symm
  have hlz : Commute l z := (hzc l hl).symm
  refine ⟨t, ?_, fun g hg => ?_⟩
  · have hmem : ρ (t ^ p) ∈ Subgroup.center ↥L := by
      rw [map_pow, ht]
      rw [Subgroup.mem_center_iff]
      intro y
      have hpow : (l * z) ^ p = l ^ p * z ^ p := hlz.mul_pow p
      have h1 : l ^ p = (z ^ p)⁻¹ := by
        rw [hpow] at hup
        exact eq_inv_of_mul_eq_one_left hup
      have hz' : z ^ p ∈ Subgroup.centralizer (L : Set Y) := Subgroup.pow_mem _ hz p
      apply Subtype.ext
      have hy : (z ^ p)⁻¹ * (y : Y) = (y : Y) * (z ^ p)⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hz') y y.2).symm
      simp only [Subgroup.coe_mul, SubmonoidClass.coe_pow, h1]
      exact hy.symm
    have h := (hcompat (t ^ p)).1 hmem
    rwa [Subgroup.coe_pow] at h
  · rw [Subgroup.mem_subgroupOf]
    refine hfix _ (ρ g).2 ?_
    have h1 : Commute (ρ g) (ρ t) := hg.map ρ
    have h2 : (ρ g : Y) * l = l * (ρ g : Y) := by
      have := congrArg Subtype.val h1.eq
      rw [ht] at this
      simpa using this
    have h3 : (ρ g : Y) * z = z * (ρ g : Y) := (hzc _ (ρ g).2).symm
    calc l * z * (ρ g : Y) * (l * z)⁻¹ = l * (z * (ρ g : Y)) * z⁻¹ * l⁻¹ := by group
      _ = l * ((ρ g : Y) * z) * z⁻¹ * l⁻¹ := by rw [h3]
      _ = l * (ρ g : Y) * l⁻¹ := by group
      _ = (ρ g : Y) := by rw [← h2]; group

end CFSG.AGLEmbedding.UnitaryLevi
