module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrFrattini

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def NeedsThree (U Z : Subgroup G) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, Subgroup.closure {a, b} ⊔ Z ≠ U

theorem core [Finite G] {p : ℕ} [Fact p.Prime] {U P N Z : Subgroup G} {y : G}
    (hU : IsPGroup p U) (hZ : Z = ⁅U, U⁆) (hirr : IrrAct y U Z) (hrank : NeedsThree U Z)
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) (hyN : y ∈ Subgroup.normalizer (N : Set G))
    (hNP : ∀ A : Subgroup G, A ≤ N → IsPGroup p A → A ≤ P)
    (hcyc : ∀ A : Subgroup G, A ≤ P → IsPGroup p A → IsCyclic A)
    (hpow : ∀ u ∈ U, ∃ k : ℕ, y * u * y⁻¹ * (u ^ k)⁻¹ ∈ N) : False := by
  have hyZ : y ∈ Subgroup.normalizer (Z : Set G) := hZ ▸ mem_normalizer_commutator hyU hyU
  have hKp : IsPGroup p ↥(U ⊓ N) := hU.to_le inf_le_left
  have hKc : IsCyclic ↥(U ⊓ N) := hcyc _ (hNP _ inf_le_right hKp) hKp
  have hyK : y ∈ Subgroup.normalizer ((U ⊓ N : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hyU, hyN⟩
  have hKZ : U ⊓ N ≤ Z := by
    rcases hirr.le_or_sup_eq inf_le_left hyK hyZ with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg, hgK⟩ := exists_zpowers_eq_of_isCyclic (U ⊓ N)
      exact hrank g hg.1 g hg.1 (by rw [closure_pair_self, ← hgK]; exact h)
  have hpowZ : ∀ u ∈ U, ∃ k : ℕ, y * u * y⁻¹ * (u ^ k)⁻¹ ∈ Z := by
    intro u hu
    obtain ⟨k, hk⟩ := hpow u hu
    exact ⟨k, hKZ ⟨U.mul_mem ((Subgroup.mem_normalizer_iff.1 hyU u).1 hu)
      (U.inv_mem (U.pow_mem hu k)), hk⟩⟩
  obtain ⟨g, hgU, hgZ⟩ : ∃ g ∈ U, g ∉ Z := by
    by_contra h
    push Not at h
    refine hrank 1 U.one_mem 1 U.one_mem ?_
    rw [closure_pair_self, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
    exact le_antisymm hirr.1 (fun x hx => h x hx)
  have h1 : Z ≤ Subgroup.zpowers g ⊔ Z := le_sup_right
  have h2 : Subgroup.zpowers g ⊔ Z ≤ U := sup_le (Subgroup.zpowers_le.2 hgU) hirr.1
  rcases hirr.2 _ h1 h2 (mem_normalizer_of_powerMap h1 hpowZ h2) with h4 | h4
  · exact hgZ (h4 ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers g))
  · exact hrank g hgU g hgU (by rw [closure_pair_self]; exact h4)

theorem le_of_two_generated [Finite G] {p : ℕ} [Fact p.Prime] {U Z I : Subgroup G} {y : G}
    [I.Normal] (hU : IsPGroup p U) (hZ : Z = ⁅U, U⁆) (hirr : IrrAct y U Z)
    (hrank : NeedsThree U Z) (hyU : y ∈ Subgroup.normalizer (U : Set G))
    (hyI : y ∈ Subgroup.normalizer (I : Set G)) {a b : G} (ha : a ∈ U) (hb : b ∈ U)
    (hgen : U ≤ Subgroup.closure {a, b} ⊔ I) : U ≤ I := by
  have hyZ : y ∈ Subgroup.normalizer (Z : Set G) := hZ ▸ mem_normalizer_commutator hyU hyU
  have hyK : y ∈ Subgroup.normalizer ((U ⊓ I : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hyU, hyI⟩
  have hcl : Subgroup.closure {a, b} ≤ U := (Subgroup.closure_le U).2 (by
    rintro x (rfl | rfl)
    · exact ha
    · exact hb)
  rcases hirr.le_or_sup_eq inf_le_left hyK hyZ with h | h
  · exfalso
    refine hrank a ha b hb (le_antisymm (sup_le hcl hirr.1) fun u hu => ?_)
    obtain ⟨g, hg, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hgen hu)
    have hwU : w ∈ U := by
      have := mul_mem (inv_mem (hcl hg)) hu
      simpa using this
    exact mul_mem (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right (h ⟨hwU, hw⟩))
  · have hKU := eq_of_sup_commutator_eq (K := U ⊓ I) hU inf_le_left (by rw [← hZ]; exact h)
    intro x hx
    have hx' : x ∈ U ⊓ I := by
      rw [hKU]
      exact hx
    exact hx'.2

end CFSG.AGLEmbedding.ParabAutIrr
