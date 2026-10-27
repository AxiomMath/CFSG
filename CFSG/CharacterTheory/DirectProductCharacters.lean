module

public import CFSG.CharacterTheory.Blocks.NormOne
public import CFSG.CharacterTheory.Blocks.NormTwo
public import CFSG.CharacterTheory.Blocks.RepresentationDecomposition
public import CFSG.CharacterTheory.OddOrderBasics.ClassAlgebra

public section

open scoped BigOperators Classical

namespace CFSG.DirectProduct

open TwoRankLowerBound.Helpers BlockSectionOrthogonality.Helpers

@[expose] def outerProductCharacter {S N : Type*} (α : S → ℂ) (β : N → ℂ) : S × N → ℂ :=
  fun x => α x.1 * β x.2

section Characters

variable {G : Type} [Group G] [Fintype G]

theorem representation_character_mem_blocksVChar {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : ρ.character ∈ BlocksVChar G := by
  obtain ⟨-, ⟨m, hm, -⟩, -⟩ := complex_representation_character_decomposition ρ
  rw [hm, Finsupp.sum]
  refine AddSubgroup.sum_mem _ fun χ _ => ?_
  rw [Nat.cast_smul_eq_nsmul ℂ]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure χ.2) _

theorem character_mem_blocksIrr_of_norm_one {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : BlocksInnerProduct ρ.character ρ.character = 1) : ρ.character ∈ BlocksIrr G := by
  obtain ⟨χ, hpos | hneg⟩ :=
    blocksVChar_norm_one_signed_irreducible (representation_character_mem_blocksVChar ρ) h
  · rw [hpos]
    exact χ.2
  · exfalso
    have h1 := blocksIrr_identity_re_pos χ
    have h2 := congrArg Complex.re (congrFun hneg 1)
    rw [Representation.char_one, Pi.neg_apply, Complex.neg_re, Complex.natCast_re] at h2
    have h3 : (0 : ℝ) ≤ Module.finrank ℂ V := Nat.cast_nonneg _
    linarith

theorem blocksInnerProduct_self_of_mem {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    BlocksInnerProduct χ χ = 1 := by
  simpa using blocksInnerProduct_irreducible (⟨χ, hχ⟩ : BlocksIrr G) ⟨χ, hχ⟩

theorem blocksInnerProduct_of_mem {χ ψ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (hψ : ψ ∈ BlocksIrr G) :
    BlocksInnerProduct χ ψ = if χ = ψ then 1 else 0 := by
  simpa only [Subtype.mk.injEq] using
    blocksInnerProduct_irreducible (⟨χ, hχ⟩ : BlocksIrr G) ⟨ψ, hψ⟩

omit [Fintype G] in
theorem identity_ne_zero_of_mem {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : χ 1 ≠ 0 := by
  intro h
  have := blocksIrr_identity_re_pos ⟨χ, hχ⟩
  simp only [h, Complex.zero_re, lt_self_iff_false] at this

theorem star_comp_mem_blocksIrr {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    starRingEnd ℂ ∘ χ ∈ BlocksIrr G := by
  have hnorm := blocksInnerProduct_self_of_mem hχ
  have hvchar : χ ∈ BlocksVChar G := AddSubgroup.subset_closure hχ
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hχ
  have hdual : ρ.dual.character = starRingEnd ℂ ∘ ρ.character := by
    funext g
    rw [Representation.char_dual, Function.comp_apply, blocksVChar_conjugate_inverse hvchar]
  rw [← hdual]
  apply character_mem_blocksIrr_of_norm_one
  rw [hdual, ← hnorm]
  simp only [BlocksInnerProduct, Function.comp_apply, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun g _ => mul_comm _ _

theorem comp_mulEquiv_mem_blocksIrr {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (φ : G ≃* G) :
    χ ∘ φ ∈ BlocksIrr G := by
  have hnorm := blocksInnerProduct_self_of_mem hχ
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hχ
  have hcomp : Representation.character (ρ.comp φ.toMonoidHom) = ρ.character ∘ φ := rfl
  rw [← hcomp]
  apply character_mem_blocksIrr_of_norm_one
  rw [hcomp, ← hnorm]
  simp only [BlocksInnerProduct, Function.comp_apply]
  congr 1
  exact Equiv.sum_comp φ.toEquiv (fun g => ρ.character g * starRingEnd ℂ (ρ.character g))

theorem blocksInnerProduct_sum_smul_left {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → G → ℂ) (g : G → ℂ) :
    BlocksInnerProduct (∑ i ∈ s, c i • f i) g = ∑ i ∈ s, c i * BlocksInnerProduct (f i) g := by
  simp only [BlocksInnerProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem regular_values_eq_sum (H : Type) [Group H] [Fintype H] :
    (fun h : H => if h = 1 then (Nat.card H : ℂ) else 0) =
      ∑ θ ∈ (irreducibles_finite H).toFinset, θ 1 • θ := by
  rw [← (CFSG.OddOrderBasics.regular_character_degree_square_sum H).1]
  funext h
  rw [SignalizerFunctor.Helpers.finite_group_regular_character]

theorem blocksInnerProduct_regular {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    BlocksInnerProduct (fun h : G => if h = 1 then (Nat.card G : ℂ) else 0) χ = χ 1 := by
  obtain ⟨d, -, hd, -⟩ := CFSG.OddOrderBasics.irreducible_character_degree_divides_order χ hχ
  have hcard : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [BlocksInnerProduct, Finset.sum_eq_single (1 : G)]
  · rw [ite_eq_left rfl, hd, Complex.conj_natCast]
    field_simp
  · intro g _ hg
    rw [ite_eq_right hg, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Characters

theorem one_mem_blocksIrr (G : Type) [Group G] : (1 : G → ℂ) ∈ BlocksIrr G := by
  rw [blocksIrr_eq_irreducible_characters]
  exact ⟨principalFiniteComplexRepresentation G,
    principalFiniteComplexRepresentation_isIrreducible G,
    principalFiniteComplexRepresentation_character G⟩

section Product

variable {S N : Type} [Group S] [Group N]

theorem outerProductCharacter_one (α : S → ℂ) (β : N → ℂ) :
    outerProductCharacter α β 1 = α 1 * β 1 := rfl

theorem character_tprod_comp_fst_snd {V W : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ S V) (σ : Representation ℂ N W) :
    (Representation.tprod (ρ.comp (MonoidHom.fst S N)) (σ.comp (MonoidHom.snd S N))).character =
      outerProductCharacter ρ.character σ.character := by
  funext x
  rw [Representation.char_tensor]
  rfl

omit [Group S] [Group N] in
theorem star_comp_outerProductCharacter (α : S → ℂ) (β : N → ℂ) :
    starRingEnd ℂ ∘ outerProductCharacter α β =
      outerProductCharacter (starRingEnd ℂ ∘ α) (starRingEnd ℂ ∘ β) := by
  funext x
  simp only [Function.comp_apply, outerProductCharacter, map_mul]

theorem exists_prod_of_preserves_factors [Finite S] [Finite N] (σ : S × N ≃* S × N)
    (hS : ∀ s : S, (σ (s, 1)).2 = 1) (hN : ∀ n : N, (σ (1, n)).1 = 1) :
    ∃ (φ : S ≃* S) (ψ : N ≃* N), ∀ x, σ x = (φ x.1, ψ x.2) := by
  let f : S →* S := (MonoidHom.fst S N).comp (σ.toMonoidHom.comp (MonoidHom.inl S N))
  let g : N →* N := (MonoidHom.snd S N).comp (σ.toMonoidHom.comp (MonoidHom.inr S N))
  have hfS : ∀ s : S, σ (s, 1) = (f s, 1) := fun s => Prod.ext rfl (hS s)
  have hgN : ∀ n : N, σ (1, n) = (1, g n) := fun n => Prod.ext (hN n) rfl
  have hdecomp : ∀ x : S × N, σ x = (f x.1, g x.2) := by
    intro x
    have hx : x = (x.1, 1) * (1, x.2) := by ext <;> simp
    rw [hx, map_mul, hfS, hgN]
    ext <;> simp
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg Prod.fst (σ.injective (by rw [hfS, hfS, hab] : σ (a, 1) = σ (b, 1)))
    exact h
  have hg : Function.Injective g := by
    intro a b hab
    have h := congrArg Prod.snd (σ.injective (by rw [hgN, hgN, hab] : σ (1, a) = σ (1, b)))
    exact h
  refine ⟨MulEquiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩,
    MulEquiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, fun x => ?_⟩
  rw [hdecomp x]
  rfl

theorem outerProductCharacter_kernel_iff {α : S → ℂ} {β : N → ℂ} (hα : α ∈ BlocksIrr S)
    (hβ : β ∈ BlocksIrr N) (A : Subgroup S) (D : Subgroup N) :
    (∀ x ∈ A.prod D, outerProductCharacter α β x = outerProductCharacter α β 1) ↔
      (∀ a ∈ A, α a = α 1) ∧ ∀ d ∈ D, β d = β 1 := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun d hd => ?_⟩
    · have h1 := h (a, 1) (Subgroup.mem_prod.mpr ⟨ha, D.one_mem⟩)
      simp only [outerProductCharacter, Prod.fst_one, Prod.snd_one] at h1
      exact mul_right_cancel₀ (identity_ne_zero_of_mem hβ) h1
    · have h1 := h (1, d) (Subgroup.mem_prod.mpr ⟨A.one_mem, hd⟩)
      simp only [outerProductCharacter, Prod.fst_one, Prod.snd_one] at h1
      exact mul_left_cancel₀ (identity_ne_zero_of_mem hα) h1
  · rintro ⟨hA, hD⟩ x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hx
    simp only [outerProductCharacter, Prod.fst_one, Prod.snd_one, hA _ h1, hD _ h2]

variable [Fintype S] [Fintype N]

theorem blocksInnerProduct_outerProductCharacter (α α' : S → ℂ) (β β' : N → ℂ) :
    BlocksInnerProduct (outerProductCharacter α β) (outerProductCharacter α' β') =
      BlocksInnerProduct α α' * BlocksInnerProduct β β' := by
  have hsum : ∑ x : S × N, outerProductCharacter α β x *
      starRingEnd ℂ (outerProductCharacter α' β' x) =
      (∑ s, α s * starRingEnd ℂ (α' s)) * ∑ n, β n * starRingEnd ℂ (β' n) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun n _ => ?_
    simp only [outerProductCharacter, map_mul]
    ring
  rw [BlocksInnerProduct, hsum, BlocksInnerProduct, BlocksInnerProduct, Nat.card_prod,
    Nat.cast_mul, mul_inv]
  ring

theorem outerProductCharacter_mem_blocksIrr {α : S → ℂ} {β : N → ℂ} (hα : α ∈ BlocksIrr S)
    (hβ : β ∈ BlocksIrr N) : outerProductCharacter α β ∈ BlocksIrr (S × N) := by
  have hnα := blocksInnerProduct_self_of_mem hα
  have hnβ := blocksInnerProduct_self_of_mem hβ
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hα
  obtain ⟨W, _, _, _, σ, -, rfl⟩ := hβ
  rw [← character_tprod_comp_fst_snd]
  apply character_mem_blocksIrr_of_norm_one
  rw [character_tprod_comp_fst_snd, blocksInnerProduct_outerProductCharacter, hnα, hnβ, mul_one]

theorem outerProductCharacter_injOn :
    Set.InjOn (fun p : (S → ℂ) × (N → ℂ) => outerProductCharacter p.1 p.2)
      (BlocksIrr S ×ˢ BlocksIrr N) := by
  rintro ⟨α, β⟩ ⟨hα, hβ⟩ ⟨α', β'⟩ ⟨hα', hβ'⟩ heq
  simp only at heq
  have h1 : BlocksInnerProduct (outerProductCharacter α β) (outerProductCharacter α' β') = 1 := by
    rw [← heq, blocksInnerProduct_outerProductCharacter, blocksInnerProduct_self_of_mem hα,
      blocksInnerProduct_self_of_mem hβ, mul_one]
  rw [blocksInnerProduct_outerProductCharacter, blocksInnerProduct_of_mem hα hα',
    blocksInnerProduct_of_mem hβ hβ'] at h1
  by_cases ha : α = α' <;> by_cases hb : β = β' <;> simp [ha, hb] at h1 ⊢

theorem regular_values_prod_eq_sum :
    (fun x : S × N => if x = 1 then (Nat.card (S × N) : ℂ) else 0) =
      ∑ p ∈ (irreducibles_finite S).toFinset ×ˢ (irreducibles_finite N).toFinset,
        (p.1 1 * p.2 1) • outerProductCharacter p.1 p.2 := by
  have h1 : (fun x : S × N => if x = 1 then (Nat.card (S × N) : ℂ) else 0) =
      outerProductCharacter (fun s : S => if s = 1 then (Nat.card S : ℂ) else 0)
        (fun n : N => if n = 1 then (Nat.card N : ℂ) else 0) := by
    funext x
    simp only [outerProductCharacter, Nat.card_prod, Nat.cast_mul, Prod.ext_iff, Prod.fst_one,
      Prod.snd_one]
    by_cases h1 : x.1 = 1 <;> by_cases h2 : x.2 = 1 <;> simp [h1, h2]
  rw [h1, regular_values_eq_sum S, regular_values_eq_sum N]
  funext x
  simp only [outerProductCharacter, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

theorem outerProductCharacter_surjOn :
    Set.SurjOn (fun p : (S → ℂ) × (N → ℂ) => outerProductCharacter p.1 p.2)
      (BlocksIrr S ×ˢ BlocksIrr N) (BlocksIrr (S × N)) := by
  intro χ hχ
  by_contra hnot
  have horth : ∀ p ∈ (irreducibles_finite S).toFinset ×ˢ (irreducibles_finite N).toFinset,
      (p.1 1 * p.2 1) * BlocksInnerProduct (outerProductCharacter p.1 p.2) χ = 0 := by
    intro p hp
    rw [Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    rw [blocksInnerProduct_of_mem (outerProductCharacter_mem_blocksIrr hp.1 hp.2) hχ,
      ite_eq_right (fun h => hnot ⟨p, hp, h⟩), mul_zero]
  have h : BlocksInnerProduct (∑ p ∈ (irreducibles_finite S).toFinset ×ˢ
      (irreducibles_finite N).toFinset, (p.1 1 * p.2 1) • outerProductCharacter p.1 p.2) χ =
      χ 1 := by
    rw [← regular_values_prod_eq_sum]
    convert blocksInnerProduct_regular hχ
  rw [blocksInnerProduct_sum_smul_left, Finset.sum_eq_zero horth] at h
  exact identity_ne_zero_of_mem hχ h.symm

theorem degree_square_sum_nontrivial_right :
    ∑ α ∈ (irreducibles_finite S).toFinset, ∑ β ∈ (irreducibles_finite N).toFinset.erase 1,
      (α 1 * β 1) ^ 2 = (Nat.card S : ℂ) * ((Nat.card N : ℂ) - 1) := by
  have hS := (CFSG.OddOrderBasics.regular_character_degree_square_sum S).2
  have hN := (CFSG.OddOrderBasics.regular_character_degree_square_sum N).2
  have h1 : (1 : N → ℂ) ∈ (irreducibles_finite N).toFinset :=
    (Set.Finite.mem_toFinset _).mpr (one_mem_blocksIrr N)
  rw [← Finset.add_sum_erase _ _ h1] at hN
  simp_rw [mul_pow]
  rw [← Finset.sum_mul_sum, hS, ← hN]
  simp

end Product

theorem direct_product_irreducible_character_families (S N : Type) [Group S] [Group N]
    [Fintype S] [Fintype N] :
    Set.BijOn (fun p : (S → ℂ) × (N → ℂ) => outerProductCharacter p.1 p.2)
      (BlocksIrr S ×ˢ BlocksIrr N) (BlocksIrr (S × N)) ∧
    (∀ (α : S → ℂ) (β : N → ℂ), outerProductCharacter α β 1 = α 1 * β 1) ∧
    (∀ α ∈ BlocksIrr S, ∀ β ∈ BlocksIrr N,
      starRingEnd ℂ ∘ α ∈ BlocksIrr S ∧ starRingEnd ℂ ∘ β ∈ BlocksIrr N ∧
        starRingEnd ℂ ∘ outerProductCharacter α β =
          outerProductCharacter (starRingEnd ℂ ∘ α) (starRingEnd ℂ ∘ β)) ∧
    (∀ σ : S × N ≃* S × N,
      (∀ x ∈ (⊤ : Subgroup S).prod (⊥ : Subgroup N),
        σ x ∈ (⊤ : Subgroup S).prod (⊥ : Subgroup N)) →
      (∀ x ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup N),
        σ x ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup N)) →
      ∃ (φ : S ≃* S) (ψ : N ≃* N), (∀ x, σ x = (φ x.1, ψ x.2)) ∧
        ∀ α ∈ BlocksIrr S, ∀ β ∈ BlocksIrr N,
          α ∘ φ ∈ BlocksIrr S ∧ β ∘ ψ ∈ BlocksIrr N ∧
            outerProductCharacter α β ∘ σ = outerProductCharacter (α ∘ φ) (β ∘ ψ)) ∧
    (∀ A : Subgroup S, A.Normal → ∀ D : Subgroup N, D.Normal →
      ∀ χ ∈ BlocksIrr (S × N),
        ((∀ x ∈ A.prod D, χ x = χ 1) ↔
          ∃ α ∈ BlocksIrr S, ∃ β ∈ BlocksIrr N, χ = outerProductCharacter α β ∧
            (∀ a ∈ A, α a = α 1) ∧ ∀ d ∈ D, β d = β 1)) ∧
    ∑ α ∈ (irreducibles_finite S).toFinset, ∑ β ∈ (irreducibles_finite N).toFinset.erase 1,
      (α 1 * β 1) ^ 2 = (Nat.card S : ℂ) * ((Nat.card N : ℂ) - 1) := by
  refine ⟨⟨fun p hp => outerProductCharacter_mem_blocksIrr hp.1 hp.2, outerProductCharacter_injOn,
    outerProductCharacter_surjOn⟩, outerProductCharacter_one,
    fun α hα β hβ => ⟨star_comp_mem_blocksIrr hα, star_comp_mem_blocksIrr hβ,
      star_comp_outerProductCharacter α β⟩, ?_, ?_, degree_square_sum_nontrivial_right⟩
  · intro σ hσS hσN
    have hS : ∀ s : S, (σ (s, 1)).2 = 1 := fun s =>
      (Subgroup.mem_prod.mp (hσS (s, 1) (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top s,
        (⊥ : Subgroup N).one_mem⟩))).2
    have hN : ∀ n : N, (σ (1, n)).1 = 1 := fun n =>
      (Subgroup.mem_prod.mp (hσN (1, n) (Subgroup.mem_prod.mpr ⟨(⊥ : Subgroup S).one_mem,
        Subgroup.mem_top n⟩))).1
    obtain ⟨φ, ψ, hσ⟩ := exists_prod_of_preserves_factors σ hS hN
    refine ⟨φ, ψ, hσ, fun α hα β hβ => ⟨comp_mulEquiv_mem_blocksIrr hα φ,
      comp_mulEquiv_mem_blocksIrr hβ ψ, ?_⟩⟩
    funext x
    simp only [Function.comp_apply, hσ x, outerProductCharacter]
  · intro A _ D _ χ hχ
    constructor
    · intro h
      obtain ⟨⟨α, β⟩, ⟨hα, hβ⟩, rfl⟩ := outerProductCharacter_surjOn hχ
      exact ⟨α, hα, β, hβ, rfl, (outerProductCharacter_kernel_iff hα hβ A D).mp h⟩
    · rintro ⟨α, hα, β, hβ, rfl, hker⟩
      exact (outerProductCharacter_kernel_iff hα hβ A D).mpr hker

end CFSG.DirectProduct
