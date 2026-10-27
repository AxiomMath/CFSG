module

public import CFSG.CharacterTheory.Wreathed.FourPointCompleteModelSupport
public import CFSG.CharacterTheory.Wreathed.CentralSL2.BaseCuspidalFamily

public noncomputable section

namespace CFSG.Wreathed.FourPointCompleteModel

open CFSG.TwoRankLowerBound.Helpers
open CFSG.Wreathed.CyclicCentralSL2Extension

open scoped Classical

theorem twoUnit_not_isSquare : ¬ IsSquare twoUnit := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun v : (ZMod 3)ˣ => (v : ZMod 3)) hc
  simp only [Units.val_mul, twoUnit_val] at h
  have key : ∀ y : ZMod 3, (2 : ZMod 3) ≠ y * y := by decide
  exact key _ h

@[expose] def galoisBasis : Module.Basis (Fin 2) (ZMod 3) (GaloisField 3 2) :=
  Module.finBasisOfFinrankEq (ZMod 3) (GaloisField 3 2) (GaloisField.finrank 3 (by norm_num))

theorem exists_unit_mul_frobenius_eq_neg_one :
    ∃ y : (GaloisField 3 2)ˣ,
      (y : GaloisField 3 2) * (y : GaloisField 3 2) ^ Nat.card (ZMod 3) = -1 := by
  obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 3 2)ˣ)
  have hcard : Nat.card (GaloisField 3 2)ˣ = 8 := by
    rw [Nat.card_units, GaloisField.card 3 2 (by norm_num)]
    norm_num
  rw [hcard] at hy
  have hne : y ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hy]; norm_num)
  have hsq : (y ^ 4) * (y ^ 4) = 1 := by
    rw [← pow_add, show 4 + 4 = orderOf y by rw [hy]]
    exact pow_orderOf_eq_one y
  have hval : ((y ^ 4 : (GaloisField 3 2)ˣ) : GaloisField 3 2) *
      ((y ^ 4 : (GaloisField 3 2)ˣ) : GaloisField 3 2) = 1 := by
    rw [← Units.val_mul, hsq, Units.val_one]
  rcases mul_self_eq_one_iff.mp hval with h1 | h1
  · exact absurd (Units.ext h1) hne
  · refine ⟨y, ?_⟩
    rw [Nat.card_zmod, ← pow_succ', ← Units.val_pow_eq_pow_val]
    exact h1

theorem degree_ncard_of_families {X : Type*} (x₀ : X) (I F1 F2 F3 F4 : Set (X → ℂ))
    (hI : I = F1 ∪ F2 ∪ F3 ∪ F4) (h1 : ∀ η ∈ F1, η x₀ = 1) (h2 : ∀ η ∈ F2, η x₀ = 3)
    (h3 : ∀ η ∈ F3, η x₀ = 4) (h4 : ∀ η ∈ F4, η x₀ = 2) (n1 : F1.ncard = 4)
    (n2 : F2.ncard = 4) (n3 : F3.ncard = 2) (n4 : F4.ncard = 6) :
    I.ncard = 16 ∧ {η ∈ I | η x₀ = 1}.ncard = 4 ∧ {η ∈ I | η x₀ = 2}.ncard = 6 ∧
      {η ∈ I | η x₀ = 3}.ncard = 4 ∧ {η ∈ I | η x₀ = 4}.ncard = 2 := by
  have hfin : ∀ F : Set (X → ℂ), F.ncard ≠ 0 → F.Finite := fun F hF =>
    Set.finite_of_ncard_ne_zero hF
  have f1 := hfin F1 (by rw [n1]; norm_num)
  have f2 := hfin F2 (by rw [n2]; norm_num)
  have f3 := hfin F3 (by rw [n3]; norm_num)
  have f4 := hfin F4 (by rw [n4]; norm_num)
  have hdisj : ∀ (F F' : Set (X → ℂ)) (a a' : ℂ), a ≠ a' → (∀ η ∈ F, η x₀ = a) →
      (∀ η ∈ F', η x₀ = a') → Disjoint F F' := by
    intro F F' a a' haa' hF hF'
    rw [Set.disjoint_left]
    intro η hη hη'
    exact haa' ((hF η hη).symm.trans (hF' η hη'))
  have d12 := hdisj F1 F2 1 3 (by norm_num) h1 h2
  have d13 := hdisj F1 F3 1 4 (by norm_num) h1 h3
  have d14 := hdisj F1 F4 1 2 (by norm_num) h1 h4
  have d23 := hdisj F2 F3 3 4 (by norm_num) h2 h3
  have d24 := hdisj F2 F4 3 2 (by norm_num) h2 h4
  have d34 := hdisj F3 F4 4 2 (by norm_num) h3 h4
  have hsep : ∀ (F : Set (X → ℂ)) (a : ℂ), F ⊆ I → (∀ η ∈ F, η x₀ = a) →
      (∀ η ∈ I, η x₀ = a → η ∈ F) → {η ∈ I | η x₀ = a} = F := by
    intro F a hFI hF hIF
    ext η
    exact ⟨fun hη => hIF η hη.1 hη.2, fun hη => ⟨hFI hη, hF η hη⟩⟩
  have hcases : ∀ η ∈ I, (η ∈ F1 ∧ η x₀ = 1) ∨ (η ∈ F2 ∧ η x₀ = 3) ∨ (η ∈ F3 ∧ η x₀ = 4) ∨
      (η ∈ F4 ∧ η x₀ = 2) := by
    intro η hη
    rw [hI] at hη
    rcases hη with ((hη | hη) | hη) | hη
    · exact Or.inl ⟨hη, h1 η hη⟩
    · exact Or.inr (Or.inl ⟨hη, h2 η hη⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hη, h3 η hη⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hη, h4 η hη⟩))
  have s1 : F1 ⊆ I := fun η hη => hI ▸ Or.inl (Or.inl (Or.inl hη))
  have s2 : F2 ⊆ I := fun η hη => hI ▸ Or.inl (Or.inl (Or.inr hη))
  have s3 : F3 ⊆ I := fun η hη => hI ▸ Or.inl (Or.inr hη)
  have s4 : F4 ⊆ I := fun η hη => hI ▸ Or.inr hη
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hI, Set.ncard_union_eq (Disjoint.union_left (Disjoint.union_left d14 d24) d34)
      ((f1.union f2).union f3) f4, Set.ncard_union_eq (Disjoint.union_left d13 d23)
      (f1.union f2) f3, Set.ncard_union_eq d12 f1 f2, n1, n2, n3, n4]
  · rw [hsep F1 1 s1 h1 fun η hη hη1 => ?_, n1]
    rcases hcases η hη with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    all_goals norm_num [hη1] at h
  · rw [hsep F4 2 s4 h4 fun η hη hη1 => ?_, n4]
    rcases hcases η hη with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · norm_num [hη1] at h
    · norm_num [hη1] at h
    · norm_num [hη1] at h
    · exact h
  · rw [hsep F2 3 s2 h2 fun η hη hη1 => ?_, n2]
    rcases hcases η hη with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · norm_num [hη1] at h
    · exact h
    · norm_num [hη1] at h
    · norm_num [hη1] at h
  · rw [hsep F3 4 s3 h3 fun η hη hη1 => ?_, n3]
    rcases hcases η hη with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · norm_num [hη1] at h
    · norm_num [hη1] at h
    · exact h
    · norm_num [hη1] at h

theorem fourPointModel_irr_ncard :
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    (CFSG.BlocksIrr W).ncard = 16 ∧ {η ∈ CFSG.BlocksIrr W | η 1 = 1}.ncard = 4 ∧
      {η ∈ CFSG.BlocksIrr W | η 1 = 2}.ncard = 6 ∧
      {η ∈ CFSG.BlocksIrr W | η 1 = 3}.ncard = 4 ∧
      {η ∈ CFSG.BlocksIrr W | η 1 = 4}.ncard = 2 := by
  intro W
  obtain ⟨y, hy⟩ := exists_unit_mul_frobenius_eq_neg_one
  obtain ⟨ψ, hψ⟩ := CFSG.Wreathed.CentralSL2.exists_addChar_ne_one (F := ZMod 3)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, hΛ, -, hFam4, -, -, -, -, -, hχ1, hχSt, hΨ, -, -, -, hFam1, hFam2,
      hFam3, hIrr, -⟩ :=
    CFSG.Wreathed.CentralSL2.base_cuspidal_characters_and_complete_family (F := ZMod 3)
      Nat.prime_three ⟨1, rfl⟩ le_rfl (by rw [Nat.card_zmod]; norm_num) twoUnit
      twoUnit_not_isSquare 4 (by norm_num) (by decide) (GaloisField 3 2) galoisBasis y hy ψ hψ
      Complex.I Complex.isPrimitiveRoot_I
  have hq : ((Nat.card (ZMod 3) : ℕ) : ℂ) = 3 := by
    rw [Nat.card_zmod]
    norm_num
  refine degree_ncard_of_families 1 (CFSG.BlocksIrr W) _ _ _ _ hIrr ?_ ?_ ?_ ?_ hFam1 hFam2 ?_ ?_
  · rintro _ ⟨r, rfl⟩
    exact (hχ1 r).2
  · rintro _ ⟨r, rfl⟩
    exact (hχSt r).2.trans hq
  · rintro _ ⟨θ, hθ, rfl⟩
    rw [(hΨ θ hθ).2, hq]
    norm_num
  · rintro _ ⟨lam, hlam, rfl⟩
    rw [(hΛ lam hlam).2, hq]
    norm_num
  · rw [hFam3, Nat.card_zmod]
  · rw [hFam4, Nat.card_zmod]

theorem exists_label_comp_surjective {X Y : Type} [Group X] [Fintype X] [Group Y] [Fintype Y]
    (basisX : FiniteIrreducibleCharacterBasis X) (basisY : FiniteIrreducibleCharacterBasis Y)
    (f : Y →* X) (hf : Function.Surjective f) (η : basisX.index) :
    ∃ θ : basisY.index,
      (basisY.representation θ).character = (basisX.representation η).character ∘ f :=
  finiteIrreducibleCharacterBasis_contains_irreducible basisY
    (inflatedFiniteComplexRepresentation f (basisX.representation η))
    (CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective f hf _ (basisX.irreducible η))

theorem card_filter_eq_ncard_sep {ι X Y : Type*} (B : Finset ι) (c : ι → X → ℂ)
    (hc : Function.Injective c) (L : (Y → ℂ) → X → ℂ) (hL : Function.Injective L)
    (I : Set (Y → ℂ)) (hBI : c '' (B : Set ι) = L '' I) (x₀ : X) (y₀ : Y)
    (hval : ∀ η, L η x₀ = η y₀) (d : ℂ) :
    (B.filter fun i => c i x₀ = d).card = {η ∈ I | η y₀ = d}.ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ hc,
    ← Set.ncard_image_of_injective _ hL]
  congr 1
  ext ψ
  simp only [Set.mem_image, Finset.coe_filter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, ⟨hiB, hid⟩, rfl⟩
    obtain ⟨η, hη, hηi⟩ : c i ∈ L '' I := hBI ▸ ⟨i, hiB, rfl⟩
    exact ⟨η, ⟨hη, by rw [← hval η, hηi, hid]⟩, hηi⟩
  · rintro ⟨η, ⟨hη, hηd⟩, rfl⟩
    obtain ⟨i, hiB, hi⟩ : L η ∈ c '' (B : Set ι) := hBI ▸ ⟨η, hη, rfl⟩
    exact ⟨i, ⟨hiB, by rw [hi, hval, hηd]⟩, hi⟩

theorem card_eq_ncard_of_image {ι X Y : Type*} (B : Finset ι) (c : ι → X → ℂ)
    (hc : Function.Injective c) (L : (Y → ℂ) → X → ℂ) (hL : Function.Injective L)
    (I : Set (Y → ℂ)) (hBI : c '' (B : Set ι) = L '' I) : B.card = I.ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ hc, hBI,
    Set.ncard_image_of_injective _ hL]

end CFSG.Wreathed.FourPointCompleteModel
