module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup

@[expose] def GenUParts {G : Type} [Group G] (p : ℕ) (z₀ : G) (ns ms ks : Set G)
    (U : Subgroup G) : Prop :=
  orderOf z₀ = p ∧ (∀ n ∈ ns, n ∈ normalizer (zpowers z₀ : Set G)) ∧
    (∀ m ∈ ms, ∃ t : G, t * t = 1 ∧ t ≠ 1 ∧ z₀ * t = t * z₀ ∧ m * t = t * m) ∧
    IsPGroup 2 U ∧ z₀ ∈ normalizer (U : Set G) ∧ U ⊓ closure (ns ∪ ms) ≠ ⊥ ∧
    (∀ k ∈ ks, k ∈ normalizer (U : Set G)) ∧ closure (ns ∪ ms ∪ ks) = ⊤

@[expose] def GenUW (G : Type) [Group G] (p : ℕ) : Prop :=
  ∃ (z₀ : G) (ns ms ks : Set G) (U : Subgroup G), GenUParts p z₀ ns ms ks U

theorem GenUParts.map {N G : Type} [Group N] [Group G] (f : N ≃* G) {p : ℕ} {z₀ : N}
    {ns ms ks : Set N} {U : Subgroup N} (h : GenUParts p z₀ ns ms ks U) :
    GenUParts p (f z₀) (f '' ns) (f '' ms) (f '' ks) (U.map f.toMonoidHom) := by
  obtain ⟨hord, hns, hms, hU, hzU, hUM, hks, hgen⟩ := h
  have hcoe : ((U.map f.toMonoidHom : Subgroup G) : Set G) = f '' (U : Set N) := coe_map _ _
  refine ⟨?_, ?_, ?_, hU.map _, ?_, ?_, ?_, ?_⟩
  · exact (orderOf_injective f.toMonoidHom f.injective z₀).trans hord
  · rintro _ ⟨n, hn, rfl⟩
    exact mem_normalizer_zpowers_map f (hns n hn)
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨t, ht2, ht1, hzt, hmt⟩ := hms m hm
    refine ⟨f t, by rw [← map_mul, ht2, map_one],
      fun h => ht1 (f.injective (h.trans (map_one f).symm)), ?_, ?_⟩
    · rw [← map_mul, ← map_mul, hzt]
    · rw [← map_mul, ← map_mul, hmt]
  · rw [hcoe]
    exact mem_normalizer_image_of_mem f hzU
  · rw [← Set.image_union, closure_image_eq_map, ← map_inf_eq _ _ _ f.injective, Ne,
      map_eq_bot_iff_of_injective _ f.injective]
    exact hUM
  · rintro _ ⟨k, hk, rfl⟩
    rw [hcoe]
    exact mem_normalizer_image_of_mem f (hks k hk)
  · rw [← Set.image_union, ← Set.image_union]
    exact closure_image_eq_top f hgen

theorem GenUW.of_mulEquiv {N G : Type} [Group N] [Group G] (f : N ≃* G) {p : ℕ}
    (h : GenUW N p) : GenUW G p := by
  obtain ⟨z₀, ns, ms, ks, U, hparts⟩ := h
  exact ⟨f z₀, f '' ns, f '' ms, f '' ks, U.map f.toMonoidHom, hparts.map f⟩

theorem exists_genU_witness_for {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) (hW : GenUW G p) {z : G} (hz : orderOf z = p) :
    ∃ (ns ms ks : Set G) (U : Subgroup G), (∀ n ∈ ns, n ∈ normalizer (zpowers z : Set G)) ∧
      (∀ m ∈ ms, ∃ t : G, t * t = 1 ∧ t ≠ 1 ∧ z * t = t * z ∧ m * t = t * m) ∧
      IsPGroup 2 U ∧ z ∈ normalizer (U : Set G) ∧ U ⊓ closure (ns ∪ ms) ≠ ⊥ ∧
      (∀ k ∈ ks, k ∈ normalizer (U : Set G)) ∧ closure (ns ∪ ms ∪ ks) = ⊤ := by
  obtain ⟨z₀, ns, ms, ks, U, hparts⟩ := hW
  obtain ⟨c, hzc⟩ := exists_mulEquiv_zpowers hp hsyl hz hparts.1
  obtain ⟨-, hns, hms, hU, hzU, hUM, hks, hgen⟩ := hparts.map c
  have hzmem : z ∈ zpowers (c z₀) := by
    rw [hzc]
    exact mem_zpowers z
  refine ⟨c '' ns, c '' ms, c '' ks, U.map c.toMonoidHom, ?_, ?_, hU, ?_, hUM, hks, hgen⟩
  · intro n hn
    rw [← hzc]
    exact hns n hn
  · intro m hm
    obtain ⟨t, ht2, ht1, hzt, hmt⟩ := hms m hm
    exact ⟨t, ht2, ht1, commute_of_mem_zpowers hzmem hzt, hmt⟩
  · exact (zpowers_le.mpr hzU) hzmem

theorem false_of_genUW {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) (hW : GenUW G p) {K : Subgroup G} {z : G} (hz : orderOf z = p)
    (hN : normalizer (zpowers z : Set G) ≤ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K) (hK : K ≠ ⊤) : False := by
  obtain ⟨ns, ms, ks, U, hns, hms, hU, hzU, hUM, hks, hgen⟩ :=
    exists_genU_witness_for hp hsyl hW hz
  have hM : closure (ns ∪ ms) ≤ K := closure_le_of_gen hN hcl hns hms
  have hUK : U ⊓ K ≠ ⊥ := fun h => hUM (eq_bot_iff.mpr ((inf_le_inf_left U hM).trans h.le))
  have hNU : normalizer (U : Set G) ≤ K := hcl U hU hzU hUK
  apply hK
  rw [eq_top_iff, ← hgen, closure_le]
  rintro g ((hg | hg) | hg)
  · exact hM (subset_closure (Or.inl hg))
  · exact hM (subset_closure (Or.inr hg))
  · exact hNU (hks g hg)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
