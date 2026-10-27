module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E64a
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E64Defs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

structure KleinE (b₁ b₂ : G) : Prop where
  cocycle : ∀ b : G, (b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) → ∀ e ∈ E, e * (b * e * b⁻¹) = 1 →
    ∃ c' ∈ E, e * (b * c' * b⁻¹) = c'
  fix_card : Set.ncard {e : G | e ∈ E ∧ b₁ * e * b₁⁻¹ = e} = 4
  fix_sq : ∀ e ∈ E, b₁ * e * b₁⁻¹ = e → e * e = 1
  fix_sub : ∀ e ∈ E, b₁ * e * b₁⁻¹ = e → b₂ * e * b₂⁻¹ = e
  gen : ∃ (e₀ : ↥E) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B), Subgroup.closure
    ({e₀, c.kappa ⟨b₁, hb₁⟩ e₀, c.kappa ⟨b₂, hb₂⟩ e₀,
      c.kappa ⟨b₁, hb₁⟩ (c.kappa ⟨b₂, hb₂⟩ e₀)} : Set ↥E) = ⊤

theorem kleinE_of_facts (hF : EFacts613 E t) {b₁ b₂ : G} (k : OE64.IsKlein B b₁ b₂) :
    c.KleinE b₁ b₂ := by
  obtain ⟨π, -, hfix, hcoc, hkl⟩ := hF.exists_pi
  obtain ⟨hB1, hB2, hcomm, hne, hnin⟩ := c.klein_kappa (π := π) k.mem₁ k.mem₂ k.sq₁ k.sq₂
    k.comm k.ne₁ k.ne₂ k.ne₁₂
  have hB3 : BInv E π (c.kappa ⟨b₁ * b₂, k.prod_mem⟩) := by
    refine ⟨?_, c.pi_kappa_mem ⟨b₁ * b₂, k.prod_mem⟩, fun hin => ?_⟩
    · rw [← map_mul, ← map_one c.kappa]
      congr 1
      exact Subtype.ext k.prod_sq
    · exact k.prod_ne_one (congrArg Subtype.val (c.eq_one_of_kappa_mem_inn hin))
  obtain ⟨hf1, hf2⟩ := hfix _ hB1
  obtain ⟨hsub, hgen, -⟩ := hkl _ _ hB1 hB2 hcomm hne hnin
  have hconj : ∀ (b : ↥B) (e : ↥E), ((c.kappa b e : ↥E) : G) = (b : G) * e * (b : G)⁻¹ :=
    fun b e => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb e he hee
    have hbB : b ∈ B := by
      rcases hb with rfl | rfl | rfl
      exacts [k.mem₁, k.mem₂, k.prod_mem]
    have hbi : BInv E π (c.kappa ⟨b, hbB⟩) := by
      rcases hb with rfl | rfl | rfl
      exacts [hB1, hB2, hB3]
    obtain ⟨c', hc'⟩ := hcoc _ hbi ⟨e, he⟩ (Subtype.ext (by
      rw [Subgroup.coe_mul, hconj]
      exact hee))
    refine ⟨c', c'.2, ?_⟩
    have := congrArg Subtype.val hc'
    rw [Subgroup.coe_mul, hconj] at this
    exact this
  · have hset : {e : G | e ∈ E ∧ b₁ * e * b₁⁻¹ = e} =
        Subtype.val '' {e : ↥E | c.kappa ⟨b₁, k.mem₁⟩ e = e} := by
      ext e
      constructor
      · rintro ⟨he, hee⟩
        exact ⟨⟨e, he⟩, Subtype.ext (by rw [hconj]; exact hee), rfl⟩
      · rintro ⟨e', he', rfl⟩
        refine ⟨e'.2, ?_⟩
        have := congrArg Subtype.val he'
        rw [hconj] at this
        exact this
    rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    exact hf1
  · intro e he hee
    have := hf2 ⟨e, he⟩ (Subtype.ext (by rw [hconj]; exact hee))
    exact congrArg Subtype.val this
  · intro e he hee
    have := hsub ⟨e, he⟩ (Subtype.ext (by rw [hconj]; exact hee))
    have h2 := congrArg Subtype.val this
    rw [hconj] at h2
    exact h2
  · obtain ⟨e₀, he₀⟩ := hgen
    exact ⟨e₀, k.mem₁, k.mem₂, he₀⟩

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
