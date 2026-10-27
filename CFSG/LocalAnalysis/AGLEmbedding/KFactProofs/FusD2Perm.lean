module

public import CFSG.RankThree.PartOne.CTP.FusionSound

public section

namespace CFSG.AGLEmbedding.FusD2

open CFSG.RankThree.PartOne.CTP.Fus

theorem fusionGenerationOf_of_gens {X : Type*} [Group X] {G : Subgroup X} {p : ℕ}
    (hp : p.Prime) {S : Set X} (hS : G = Subgroup.closure S) {x y : X} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hxG : x ∈ G) (hyG : y ∈ G)
    {Γ : Set X} (hΓG : Γ ⊆ G)
    (hfus : ∀ g ∈ Γ, ∃ i j k l : ℕ, x ^ i * y ^ j ≠ 1 ∧ g * (x ^ i * y ^ j) = (x ^ k * y ^ l) * g)
    (hgen : S ⊆ Subgroup.closure Γ) : FusionGenerationOf ↥G p := by
  set E0 : Subgroup X := Subgroup.closure ({x, y} : Set X) with hE0
  have hxE : x ∈ E0 := Subgroup.subset_closure (by simp)
  have hyE : y ∈ E0 := Subgroup.subset_closure (by simp)
  have hE0G : E0 ≤ G := by
    rw [hE0, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hxG, hyG]
  have hpow : ∀ (i j : ℕ), x ^ i * y ^ j ∈ E0 := fun i j =>
    E0.mul_mem (E0.pow_mem hxE i) (E0.pow_mem hyE j)
  refine ⟨E0.subgroupOf G, {g : ↥G | (g : X) ∈ Γ},
    (isPGroup_closure_pair hp hx hy hxy).comap_subtype, fun h => hx1 ?_, ?_, ?_⟩
  · have hm : (⟨x, hxG⟩ : ↥G) ∈ E0.subgroupOf G := Subgroup.mem_subgroupOf.2 hxE
    rw [h] at hm
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hm)
  · rw [eq_top_iff]
    intro h _
    have hmap : (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype = Subgroup.closure Γ := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hz
        exact ⟨⟨z, hΓG hz⟩, hz, rfl⟩
    have hle : G ≤ (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype := by
      rw [hmap, hS, Subgroup.closure_le]
      exact hgen
    obtain ⟨k, hk, hkh⟩ := hle h.2
    have : k = h := Subtype.ext hkh
    rwa [← this]
  · intro g hg
    obtain ⟨i, j, k, l, hne, hg'⟩ := hfus _ hg
    refine ⟨⟨x ^ i * y ^ j, hE0G (hpow i j)⟩, Subgroup.mem_subgroupOf.2 (hpow i j), ?_, ?_⟩
    · intro h1
      exact hne (congrArg Subtype.val h1)
    · refine Subgroup.mem_subgroupOf.2 ?_
      have : (g : X) * (x ^ i * y ^ j) * (g : X)⁻¹ = x ^ k * y ^ l := by
        rw [hg', mul_assoc, mul_inv_cancel, mul_one]
      change (g : X) * (x ^ i * y ^ j) * (g : X)⁻¹ ∈ E0
      rw [this]
      exact hpow k l

end CFSG.AGLEmbedding.FusD2
