module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLevi
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem noIrrAction [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {I J S T U Z : Subgroup G} [I.Normal] {y : G}
    (hU : IsPGroup p U) (hZ : Z = ⁅U, U⁆) (hirr : IrrAct y U Z) (hrank : NeedsThree U Z)
    (hyU : y ∈ Subgroup.normalizer (U : Set G))
    (hself : ∀ g ∈ I, g ∈ Subgroup.normalizer (J : Set G) → g ∈ J)
    (hUJ : U ≤ Subgroup.normalizer (J : Set G)) (hyJ : y ∈ Subgroup.normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hSJ : S ≤ J) (hTJ : T ≤ J) (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hTodd : ∀ t ∈ T, ∃ m : ℕ, Odd m ∧ t ^ m = 1) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hgen : J ≤ T ⊔ S ⊔ perfectJoin J)
    (hcyc : ∀ A : Subgroup G, A ≤ perfectJoin J → IsPGroup p A → IsCyclic A)
    (R1 : ∃ a ∈ U, ∃ b ∈ U, U ≤ Subgroup.closure {a, b} ⊔ I)
    (R2 : U ≤ I → U ≤ J → y ∉ I → ∀ u ∈ U, ∃ k : ℕ, y * u * y⁻¹ * (u ^ k)⁻¹ ∈ twoCore J) :
    False := by
  obtain ⟨hEq, hab⟩ := borelLike_facts hS2 hSJ hTJ hTc hTodd hTS hgen
  obtain ⟨a, ha, b, hb, hgen2⟩ := R1
  have hyI : y ∈ Subgroup.normalizer (I : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    exact fun x => ⟨fun hx => Subgroup.Normal.conj_mem inferInstance x hx y,
      fun hx => by simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _ hx y⁻¹⟩
  have hUI : U ≤ I := le_of_two_generated hU hZ hirr hrank hyU hyI ha hb hgen2
  have hUJ' : U ≤ J := fun u hu => hself u (hUI hu) (hUJ hu)
  have hpow : ∀ u ∈ U, ∃ k : ℕ, y * u * y⁻¹ * (u ^ k) ⁻¹ ∈ twoCore J := by
    by_cases hyI' : y ∈ I
    · have hyJ' : y ∈ J := hself y hyI' hyJ
      intro u hu
      refine ⟨1, ?_⟩
      have := hab y hyJ' u (hUJ' hu)
      simpa [commutatorElement_def] using this
    · exact R2 hUI hUJ' hyI'
  exact core hU hZ hirr hrank hyU (mem_normalizer_twoCore hyJ)
    (fun A hA hAp => pSubgroup_le_perfectJoin (Fact.out) hp2 hS2 hSJ (hEq ▸ hA) hAp) hcyc hpow

end CFSG.AGLEmbedding.ParabAutIrr
