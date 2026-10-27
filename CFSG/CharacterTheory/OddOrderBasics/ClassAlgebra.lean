module

public import CFSG.Adapters.QiuzhenLegacy.Theory.Character.Divisibility
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
public import CFSG.CharacterTheory.Blocks.IrreducibleCharacterBasis
public import CFSG.LocalAnalysis.SignalizerFunctor.RegularCharacterValues

public section

open scoped BigOperators Classical

namespace CFSG.OddOrderBasics

open BlockSectionOrthogonality.Helpers

theorem regular_character_degree_square_sum (H : Type) [Group H] [Fintype H] :
    (Representation.leftRegular ℂ H).character =
        ∑ θ ∈ (irreducibles_finite H).toFinset, θ 1 • θ ∧
      ∑ θ ∈ (irreducibles_finite H).toFinset, θ 1 ^ 2 = (Nat.card H : ℂ) := by
  set Reg := (Representation.leftRegular ℂ H).character with hRegdef
  have hReg : ∀ g, Reg g = if g = 1 then (Nat.card H : ℂ) else 0 := fun g => by
    rw [hRegdef, SignalizerFunctor.Helpers.finite_group_regular_character]
  have hclass : BlocksIsClassFunction Reg := fun g h =>
    Representation.char_conj (Representation.leftRegular ℂ H) g h
  have hcoeff : ∀ θ ∈ BlocksIrr H, BlocksInnerProduct Reg θ = θ 1 := by
    intro θ hθ
    obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
    have hcard : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [BlocksInnerProduct, Finset.sum_eq_single (1 : H)]
    · rw [hReg, ite_eq_left rfl, Representation.char_one, Complex.conj_natCast]
      field_simp
    · intro g _ hg
      rw [hReg, ite_eq_right hg, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hexp := (irreducible_character_basis H).2.2.2 Reg hclass
  have hexp' : Reg = ∑ θ ∈ (irreducibles_finite H).toFinset, θ 1 • θ := by
    rw [hexp]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [hcoeff θ ((Set.Finite.mem_toFinset _).mp hθ)]
  refine ⟨hexp', ?_⟩
  have h1 := congrFun hexp' 1
  rw [hReg, ite_eq_left rfl, Finset.sum_apply] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, sq]

theorem irreducible_character_degree_divides_order {G : Type} [Group G] [Finite G]
    (θ : G → ℂ) (hθ : θ ∈ BlocksIrr G) :
    ∃ d : ℕ, 0 < d ∧ θ 1 = d ∧ d ∣ Nat.card G ∧
      ∀ p : ℕ, p.Prime → IsPGroup p G → ∃ a : ℕ, d = p ^ a := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hθ
  have : Nontrivial V := Theory.Character.irreducible_nontrivial ρ
  refine ⟨Module.finrank ℂ V, Module.finrank_pos, Representation.char_one ρ,
    Theory.Character.irreducible_dimension_dvd_group_order ρ, fun p hp hG => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  have hdvd := Theory.Character.irreducible_dimension_dvd_group_order ρ
  rw [hn] at hdvd
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨a, ha⟩

@[expose] noncomputable def classPairCount {G : Type*} [Group G] [Finite G]
    (i j : ConjClasses G) (z : G) : ℕ :=
  ((Theory.Character.classSet i ×ˢ Theory.Character.classSet j).filter
    fun p => p.1 * p.2 = z).card

theorem classPairCount_conj {G : Type*} [Group G] [Finite G] (i j : ConjClasses G)
    (z x : G) : classPairCount i j (x * z * x⁻¹) = classPairCount i j z := by
  unfold classPairCount
  symm
  refine Finset.card_nbij' (fun p => (x * p.1 * x⁻¹, x * p.2 * x⁻¹))
    (fun p => (x⁻¹ * p.1 * x, x⁻¹ * p.2 * x)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq,
      Theory.Character.mem_classSet_iff] at hp ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← h1, ConjClasses.mk_eq_mk_iff_isConj]
      exact (isConj_iff.mpr ⟨x, rfl⟩).symm
    · rw [← h2, ConjClasses.mk_eq_mk_iff_isConj]
      exact (isConj_iff.mpr ⟨x, rfl⟩).symm
    · rw [← h3]
      group
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq,
      Theory.Character.mem_classSet_iff] at hp ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← h1, ConjClasses.mk_eq_mk_iff_isConj]
      exact (isConj_iff.mpr ⟨x⁻¹, by group⟩).symm
    · rw [← h2, ConjClasses.mk_eq_mk_iff_isConj]
      exact (isConj_iff.mpr ⟨x⁻¹, by group⟩).symm
    · have : x⁻¹ * (p.1 * p.2) * x = z := by rw [h3]; group
      rw [← this]
      group
  · intro p _
    exact Prod.ext (by dsimp only; group) (by dsimp only; group)
  · intro p _
    exact Prod.ext (by dsimp only; group) (by dsimp only; group)

theorem conjugacy_class_product_coefficients {G : Type*} [Group G] [Fintype G] :
    ∃ a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ,
      (∀ i j s (z : G), ConjClasses.mk z = s →
        ((Theory.Character.classSet i ×ˢ Theory.Character.classSet j).filter
          fun p => p.1 * p.2 = z).card = a i j s) ∧
      (∀ i (x : MonoidAlgebra ℂ G),
        x * Theory.Character.classSumComplex i = Theory.Character.classSumComplex i * x) ∧
      (∀ i j, Theory.Character.classSumComplex i * Theory.Character.classSumComplex j =
        ∑ s, (a i j s : ℂ) • Theory.Character.classSumComplex s) ∧
      ∀ i j s, ((Theory.Character.classSet i ×ˢ Theory.Character.classSet j).filter
          fun p => ConjClasses.mk (p.1 * p.2) = s).card =
        a i j s * (Theory.Character.classSet s).card := by
  let rep : ConjClasses G → G := fun s => Classical.choose (ConjClasses.exists_rep s)
  have hrep : ∀ s, ConjClasses.mk (rep s) = s := fun s =>
    Classical.choose_spec (ConjClasses.exists_rep s)
  let a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ := fun i j s =>
    classPairCount i j (rep s)
  have hconst : ∀ i j s (z : G), ConjClasses.mk z = s → classPairCount i j z = a i j s := by
    intro i j s z hz
    have hconj : IsConj (rep s) z := by
      rw [← ConjClasses.mk_eq_mk_iff_isConj, hrep, hz]
    obtain ⟨x, hx⟩ := isConj_iff.mp hconj
    rw [← hx]
    exact classPairCount_conj i j (rep s) x
  refine ⟨a, hconst, fun i x => Theory.Character.classSumComplex_comm i x, ?_, ?_⟩
  ·
    intro i j
    have hprod : Theory.Character.classSumComplex i * Theory.Character.classSumComplex j =
        ∑ p ∈ Theory.Character.classSet i ×ˢ Theory.Character.classSet j,
          MonoidAlgebra.single (p.1 * p.2) (1 : ℂ) := by
      rw [Theory.Character.classSumComplex, Theory.Character.classSumComplex, Finset.sum_mul_sum,
        Finset.sum_product]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hprod]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Theory.Character.classSet i ×ˢ
      Theory.Character.classSet j) (t := Finset.univ) (g := fun p => p.1 * p.2)
      (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ z : G, (∑ p ∈ (Theory.Character.classSet i ×ˢ Theory.Character.classSet j).filter
        (fun p => p.1 * p.2 = z), MonoidAlgebra.single (p.1 * p.2) (1 : ℂ)) =
        (classPairCount i j z : ℂ) • MonoidAlgebra.single z (1 : ℂ) := by
      intro z
      rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2],
        Finset.sum_const, classPairCount, ← Nat.cast_smul_eq_nsmul ℂ]
    simp_rw [hfib]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := fun z : G => ConjClasses.mk z) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Theory.Character.classSumComplex, Finset.smul_sum]
    have hset : Finset.univ.filter (fun z : G => ConjClasses.mk z = s) =
        Theory.Character.classSet s := by
      ext z
      rw [Finset.mem_filter, Theory.Character.mem_classSet_iff]
      simp
    rw [hset]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [hconst i j s z ((Theory.Character.mem_classSet_iff).mp hz)]
  ·
    intro i j s
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : G × G => p.1 * p.2)
      (t := Theory.Character.classSet s)]
    · rw [Finset.sum_congr rfl fun z hz => ?_, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.filter_filter]
      have hz' := (Theory.Character.mem_classSet_iff).mp hz
      rw [← hconst i j s z hz', classPairCount]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp, -, h⟩
        exact ⟨hp, h⟩
      · rintro ⟨hp, h⟩
        refine ⟨hp, ?_, h⟩
        rw [h, hz']
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      rw [Finset.mem_coe, Theory.Character.mem_classSet_iff]
      exact hp.2

end CFSG.OddOrderBasics
