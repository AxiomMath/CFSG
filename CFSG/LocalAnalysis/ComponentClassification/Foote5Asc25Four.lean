module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25Psu
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitF5B4Four

public section

namespace CFSG.ComponentClassification.Foote5.Asc25

open CFSG Subgroup CFSG.ABGLocalTools CFSG.EvenSporadicStandard.Finkelstein77
  CFSG.ComponentClassification.Asc76X CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_conj_closed {𝒞 : Set G} (h𝒞 : ∀ g y, y ∈ 𝒞 → g * y * g⁻¹ ∈ 𝒞)
    {D T : Subgroup G} (hD𝒞 : ∀ d ∈ D, d ≠ 1 → d ∈ 𝒞)
    (hsic : ∀ s ∈ normalizer (D : Set G), s ∈ 𝒞 → s ∈ D) (hT : IsPGroup 2 T) (hDT : D ≤ T) :
    T ≤ normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hle
  have hlt : T ⊓ normalizer (D : Set G) < T :=
    lt_of_le_of_ne inf_le_left fun h => hle (h ▸ inf_le_right)
  obtain ⟨n, hnT, hnN, hnnot⟩ := Lemma25Proof.exists_mem_normalizer_not_mem hT hlt
  apply hnnot
  refine mem_inf.mpr ⟨hnT, ?_⟩
  have hconj : ∀ d ∈ D, n * d * n⁻¹ ∈ D := by
    intro d hd
    by_cases hd1 : d = 1
    · rw [hd1, mul_one, mul_inv_cancel]
      exact one_mem _
    have hdN : d ∈ T ⊓ normalizer (D : Set G) := mem_inf.mpr ⟨hDT hd, le_normalizer hd⟩
    have h1 := (mem_normalizer_iff.mp hnN d).mp hdN
    exact hsic _ (mem_inf.mp h1).2 (h𝒞 n d (hD𝒞 d hd hd1))
  rw [mem_normalizer_iff_map_conj_eq]
  refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj n).injective).ge
  rintro _ ⟨d, hd, rfl⟩
  exact hconj d hd

theorem fourgroup_cases
    {x : G} (hx : orderOf x = 4) (hwc : WeaklyClosedInNormalizer (zpowers x)) {D : Subgroup G}
    (hD4 : Nat.card D = 4) (hD𝒞 : ∀ d ∈ D, d ≠ 1 → IsConj (x ^ 2) d)
    (hsic : ∀ s ∈ normalizer (D : Set G), IsConj (x ^ 2) s → s ∈ D) :
    IsSylowOf 2 D (normalClosure (D : Set G)) ∨
      ∀ P : Subgroup G, IsSylowOf 2 P (normalClosure (D : Set G)) →
        Nonempty (P ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : ∀ d ∈ D, d * d = 1 := fun d hd => by
    by_cases hd1 : d = 1
    · rw [hd1, mul_one]
    · exact Lemma25Proof.sq_eq_one_of_isConj hx (hD𝒞 d hd hd1)
  have hDp : IsPGroup 2 D := IsPGroup.of_card (n := 2) (by rw [hD4]; norm_num)
  obtain ⟨T, hT, hDT⟩ := FooteLit.exists_isSylowOf_ge_of_le (le_top : D ≤ ⊤) hDp
  have hTN : T ≤ normalizer (D : Set G) :=
    le_normalizer_of_conj_closed (𝒞 := {u | IsConj (x ^ 2) u})
      (fun g y hy => Lemma25Proof.isConj_conj g hy) hD𝒞 hsic hT.isPGroup hDT
  have hwcD : ∀ g : G, rightConjugate D g ≤ T → rightConjugate D g = D := by
    intro g hg
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      have hmem : (MulAut.conj g⁻¹).toMonoidHom d ∈ T := hg ⟨d, hd, rfl⟩
      by_cases hd1 : d = 1
      · rw [hd1, map_one]
        exact one_mem _
      · apply hsic _ (hTN hmem)
        exact Lemma25Proof.isConj_conj g⁻¹ (hD𝒞 d hd hd1)
    · rw [rightConjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
  rcases hallFusionThm32 G T D hT hDT hD4 (FooteLit.F5.isElemAbelian_of_mul_self hD2) hwcD with
    h1 | h2 | h3
  · exact Or.inl h1
  · exact absurd (false_of_psu3 hx hwc hD4 hD𝒞 (Classical.choice h2)) id
  · exact Or.inr h3

end CFSG.ComponentClassification.Foote5.Asc25
