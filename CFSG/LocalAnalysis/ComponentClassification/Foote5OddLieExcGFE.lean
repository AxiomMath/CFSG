module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcField

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank

variable {τ : Tag}

theorem card_fixSubfield_of_sq_pow' {K : Type} [Field K] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e)) :
    Nat.card (fixSubfield δ) = p ^ e := by
  have hK' : Nat.card K = p ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hord, -, -, hA⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega) hK'
  have hδφ : δ = φ ^ e := RingEquiv.ext fun c => by
    rw [hδ, ringAut_pow_apply_of_frobenius hφ e c]
  have hδord : orderOf δ = 2 := by
    rw [hδφ, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 2 rfl), hord,
      Nat.mul_div_cancel _ (by omega : 0 < e)]
  obtain ⟨-, S, hS, hcard⟩ := hA (Subgroup.zpowers δ)
  rw [Nat.card_zpowers, hδord, Nat.mul_div_cancel_left e two_pos] at hcard
  have hSk : S = fixSubfield δ := by
    refine SetLike.ext' ?_
    rw [hS]
    ext a
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_fixSubfield]
    constructor
    · intro h
      exact h δ (Subgroup.mem_zpowers δ)
    · intro h τ' hτ'
      have hstab : Subgroup.zpowers δ ≤ MulAction.stabilizer (K ≃+* K) a :=
        Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]; exact h)
      have h' := hstab hτ'
      rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h'
  rw [← hSk, hcard]

@[expose] def InnerDiagCoreInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    ∀ α : MulAut (adjointGroup τ K), α ^ 2 = 1 → α ≠ 1 →
      ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ), (∀ h : adjointGroup τ K,
        (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ *
          (g : ModGL τ K)⁻¹) →
      OuterCoreAt α

theorem outerCoreAt_GFE_of_innerDiag
    {K : Type} [Field K] [Finite K] (hτ : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3))
    (hK : Odd (Nat.card K)) (hinn : InnerDiagCoreInput τ) (α : MulAut (adjointGroup τ K))
    (hα : orderOf α = 2) : OuterCoreAt α := by
  have hα2 : α ^ 2 = 1 := sq_eq_one_of_orderOf hα
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    exact absurd hα (by norm_num)
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ hK hα2 with ⟨g, a, hαg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
  · exact hinn K hK α hα2 hα1 g a hαg
  ·
    have hqp : q = p := by
      have h1 : q ∣ p ^ f := by
        rw [← hcard, hKe, ← pow_mul]
        exact dvd_pow_self q (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1)
    subst hqp
    have hk : Nat.card (fixSubfield δ) = q ^ e := card_fixSubfield_of_sq_pow' hq he hKe δ hδ
    have : Finite (fixSubfield δ) := Subtype.finite
    have hτ3 : τ = .G2 ∨ τ = .F4 ∨ τ = .E8 := by
      rcases hτ with h | h | ⟨h, -⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    have hNFs : UniqueFieldNormalForm τ K ∧ UniqueFieldNormalForm τ (fixSubfield δ) := by
      rcases hτ with h | h | ⟨h, h3⟩
      · exact ⟨(odd_F4_and_nonexceptional_G2_automorphism_normal_form hq hp2 hf K hcard τ
          (Or.inl h)).1, (odd_F4_and_nonexceptional_G2_automorphism_normal_form hq hp2 he _ hk τ
          (Or.inl h)).1⟩
      · subst h
        exact ⟨uniqueFieldNormalForm_E8 K, uniqueFieldNormalForm_E8 _⟩
      · have h3' : q ≠ 3 := fun h' => h3 (hchar.trans h')
        exact ⟨(odd_F4_and_nonexceptional_G2_automorphism_normal_form hq hp2 hf K hcard τ
          (Or.inr ⟨h, h3'⟩)).1, (odd_F4_and_nonexceptional_G2_automorphism_normal_form hq hp2 he
          _ hk τ (Or.inr ⟨h, h3'⟩)).1⟩
    exact outerCoreAt_quadratic_field hK2 hq he hKe δ hδ hNFs.1 hNFs.2
      (entrywiseFixedGroup_eq_fixedFieldImage_of_det_one hτ3 δ) hαg hα2

@[expose] def G2ThreeOuterCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 3 →
    ∀ α : MulAut (adjointGroup Tag.G2 K), α ^ 2 = 1 → α ≠ 1 →
      (¬ ∃ (g : adjointGroup Tag.G2 K) (a : Fin Tag.G2.rank → Kˣ), ∀ h : adjointGroup Tag.G2 K,
        (α h : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) * rootDiagUnit Tag.G2 a * h *
          (rootDiagUnit Tag.G2 a)⁻¹ * (g : ModGL Tag.G2 K)⁻¹) →
      OuterCoreAt α

theorem outerCoreAt_of_lieModel_untwisted
    {S : Type} [Group S] (τ : Tag) {t : StatedLieTag} {n p f : ℕ}
    (hm : LieModel S t n p f)
    (ht : ∀ G : Type, ∀ _ : Group G, ChevalleyExceptionalModel G t p f →
      UntwistedChevalleyModel G τ (p ^ f))
    (hnot : t ∉ classicalTags ∧ t ∉ reeTitsTags ∧ t ≠ .twistedB2)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ β : MulAut (adjointGroup τ K), orderOf β = 2 → OuterCoreAt β)
    (i : MulAut S) (hi : orderOf i = 2) : OuterCoreAt i := by
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hY⟩ | ⟨-, hrt, -⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl hnot.1
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ (ht S inferInstance hY)
    exact outerCoreAt_of_congr e
      (h K hK _ ((MulEquiv.orderOf_eq (MulAut.congr e) i).trans hi))
  · exact absurd hrt hnot.2.1
  · exact absurd hsz hnot.2.2

theorem oddLieCoreFamilyInput_F4
    (hinn : InnerDiagCoreInput .F4) : OddLieCoreFamilyInput .F4 := by
  refine oddLieCoreFamilyInput_of_outerCoreAt fun S _ _ _ _ n p f hp hp2 _ hm i hi => ?_
  refine outerCoreAt_of_lieModel_untwisted .F4 hm (fun G _ hG => hG.2) ⟨by decide, by decide,
    by decide⟩ (fun K _ _ hK β hβ => ?_) i hi
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  exact outerCoreAt_GFE_of_innerDiag (Or.inl rfl) hodd hinn β hβ

theorem oddLieCoreFamilyInput_E8
    (hinn : InnerDiagCoreInput .E8) : OddLieCoreFamilyInput .E8 := by
  refine oddLieCoreFamilyInput_of_outerCoreAt fun S _ _ _ _ n p f hp hp2 _ hm i hi => ?_
  refine outerCoreAt_of_lieModel_untwisted .E8 hm (fun G _ hG => hG.2) ⟨by decide, by decide,
    by decide⟩ (fun K _ _ hK β hβ => ?_) i hi
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  exact outerCoreAt_GFE_of_innerDiag (Or.inr (Or.inl rfl)) hodd hinn β hβ

theorem oddLieCoreFamilyInput_G2
    (hinn : InnerDiagCoreInput .G2) (h3 : G2ThreeOuterCoreInput) :
    OddLieCoreFamilyInput .G2 := by
  refine oddLieCoreFamilyInput_of_outerCoreAt fun S _ _ _ _ n p f hp hp2 _ hm i hi => ?_
  refine outerCoreAt_of_lieModel_untwisted .G2 hm (fun G _ hG => hG.2) ⟨by decide, by decide,
    by decide⟩ (fun K _ _ hK β hβ => ?_) i hi
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  by_cases h3K : ringChar K = 3
  · have hβ2 : β ^ 2 = 1 := sq_eq_one_of_orderOf hβ
    have hβ1 : β ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hβ
      exact absurd hβ (by norm_num)
    by_cases hin : ∃ (g : adjointGroup Tag.G2 K) (a : Fin Tag.G2.rank → Kˣ),
        ∀ h : adjointGroup Tag.G2 K, (β h : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) *
          rootDiagUnit Tag.G2 a * h * (rootDiagUnit Tag.G2 a)⁻¹ * (g : ModGL Tag.G2 K)⁻¹
    · obtain ⟨g, a, hαg⟩ := hin
      exact hinn K hodd β hβ2 hβ1 g a hαg
    · exact h3 K h3K β hβ2 hβ1 hin
  · exact outerCoreAt_GFE_of_innerDiag (Or.inr (Or.inr ⟨rfl, h3K⟩)) hodd hinn β hβ

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
