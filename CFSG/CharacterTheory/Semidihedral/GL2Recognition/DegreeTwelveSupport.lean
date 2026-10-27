module

public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ThreeIndexThree
public import CFSG.CharacterTheory.Blocks.IrreducibleCharacterBasis
public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ColumnsSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.GL2Columns

section FixedSpaces

variable {G : Type} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem finrank_invariants_subgroup [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) :
    (Nat.card A : ℂ)⁻¹ * ∑ x : A, ρ.character (x : G) =
      Module.finrank ℂ (Representation.invariants (ρ.comp A.subtype)) := by
  have : Invertible (Nat.card A : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact Representation.card_inv_mul_sum_char_eq_finrank (ρ := ρ.comp A.subtype)

theorem invariants_le_of_le (ρ : Representation ℂ G V) {A B : Subgroup G} (h : A ≤ B) :
    Representation.invariants (ρ.comp B.subtype) ≤
      Representation.invariants (ρ.comp A.subtype) := fun _ hv x =>
  hv ⟨x, h x.2⟩

theorem invariants_inf_le_sup (ρ : Representation ℂ G V) (A B : Subgroup G) :
    Representation.invariants (ρ.comp A.subtype) ⊓
        Representation.invariants (ρ.comp B.subtype) ≤
      Representation.invariants (ρ.comp (A ⊔ B).subtype) := by
  intro v ⟨hA, hB⟩
  let S : Subgroup G :=
    { carrier := {g | ρ g v = v}
      mul_mem' := fun {g h} hg hh => by
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at hg hh ⊢
        rw [hh, hg]
      one_mem' := by simp
      inv_mem' := fun {g} hg => by
        simp only [Set.mem_ofPred_eq] at hg ⊢
        conv_lhs => rw [← hg]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hAS : A ≤ S := fun x hx => hA ⟨x, hx⟩
  have hBS : B ≤ S := fun x hx => hB ⟨x, hx⟩
  intro x
  exact sup_le hAS hBS x.2

theorem finrank_invariants_top_eq_zero [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hχ : ρ.character ∈ CFSG.BlocksIrr G) (hne : ρ.character ≠ 1) :
    Module.finrank ℂ (Representation.invariants (ρ.comp (⊤ : Subgroup G).subtype)) = 0 := by
  have h := finrank_invariants_subgroup ρ ⊤
  have horth := (CFSG.irreducible_character_basis G).1 _ hχ _
    (principal_mem_blocksIrr (G := G))
  rw [ite_eq_right hne] at horth
  have hsum : ∑ x : (⊤ : Subgroup G), ρ.character (x : G) = ∑ g : G, ρ.character g :=
    Fintype.sum_equiv (Subgroup.topEquiv.toEquiv) _ _ fun _ => rfl
  rw [hsum, Subgroup.card_top] at h
  rw [CFSG.BlocksInnerProduct] at horth
  simp only [Pi.one_apply, map_one, mul_one] at horth
  rw [horth] at h
  exact_mod_cast h.symm

end FixedSpaces

theorem sum_eq_sum_orders {A : Type*} [Group A] [Fintype A] (f : A → ℂ) (D : Finset ℕ)
    (hD : ∀ x : A, orderOf x ∈ D) (c : ℕ → ℂ) (hc : ∀ x, f x = c (orderOf x)) :
    ∑ x, f x = ∑ d ∈ D, c d * (Nat.card {x : A // orderOf x = d} : ℂ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := orderOf) (t := D) (fun x _ => hD x)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [hc x, (Finset.mem_filter.mp hx).2],
    Finset.sum_const, nsmul_eq_mul, mul_comm, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem orderOf_mem_of_card_sum {A : Type*} [Group A] [Fintype A] (D : Finset ℕ)
    (hsum : ∑ d ∈ D, Nat.card {x : A // orderOf x = d} = Nat.card A) :
    ∀ x : A, orderOf x ∈ D := by
  have hcard : (Finset.univ.filter fun y : A => orderOf y ∈ D).card = Nat.card A := by
    rw [Finset.card_eq_sum_card_fiberwise (f := orderOf)
      (s := Finset.univ.filter fun y : A => orderOf y ∈ D) (t := D)
      (fun y hy => (Finset.mem_filter.mp hy).2), ← hsum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hd, h⟩
  have huniv : (Finset.univ.filter fun y : A => orderOf y ∈ D) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, Nat.card_eq_fintype_card])
  intro x
  have hx : x ∈ Finset.univ.filter fun y : A => orderOf y ∈ D := by
    rw [huniv]
    exact Finset.mem_univ x
  exact (Finset.mem_filter.mp hx).2

theorem permutation_constituents_of_degree_gap {G : Type} [Group G] [Fintype G]
    (data : FiniteComplexRepresentation.{0, 0} G) (χ : G → ℂ)
    (hgap : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ χ → ∃ d : ℕ, 12 < d ∧ ψ 1 = d)
    (hχ1 : χ 1 = 12)
    (hone : characterPairing data.character 1 = 1) :
    (data.character 1 ≠ 1 → 13 ≤ (Module.finrank ℂ data.vector : ℕ)) ∧
    ((Module.finrank ℂ data.vector : ℕ) = 13 → data.character = 1 + χ) := by
  obtain ⟨size, summand, hirr, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  let ψ : Fin size → G → ℂ := fun k => (summand k).character
  have hdecomp : data.character = fun g => ∑ k, (1 : ℂ) * ψ k g := by
    funext g
    simp only [one_mul, ψ]
    exact hsum g
  have hprin := principalFiniteComplexRepresentation_character G
  have hcount : (Finset.univ.filter fun k : Fin size => ψ k = 1).card = 1 := by
    have h := hone
    rw [hdecomp, characterPairing_expansion_left] at h
    have h' : ∑ k : Fin size, (1 : ℂ) * characterPairing (ψ k) 1 =
        ((Finset.univ.filter fun k : Fin size => ψ k = 1).card : ℂ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_mul, ← hprin, characterPairing_irreducible _ _ (hirr k)
        (principalFiniteComplexRepresentation_isIrreducible G)]
      split_ifs <;> simp
    rw [h'] at h
    exact_mod_cast h
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hcount
  have hk₀1 : ψ k₀ = 1 := by
    have : k₀ ∈ Finset.univ.filter fun k : Fin size => ψ k = 1 := by
      rw [hk₀]
      exact Finset.mem_singleton_self k₀
    exact (Finset.mem_filter.mp this).2
  have hother : ∀ k, k ≠ k₀ → ψ k ≠ 1 := by
    intro k hk h
    have : k ∈ Finset.univ.filter fun k : Fin size => ψ k = 1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [hk₀, Finset.mem_singleton] at this
    exact hk this
  let deg : Fin size → ℕ := fun k => Module.finrank ℂ (summand k).vector
  have hdegψ : ∀ k, ψ k 1 = deg k := fun k => by
    simp [ψ, deg, FiniteComplexRepresentation.character, Representation.char_one]
  have hmemIrr : ∀ k, ψ k ∈ CFSG.BlocksIrr G := fun k => by
    rw [CFSG.blocksIrr_eq_irreducible_characters]
    exact ⟨summand k, hirr k, rfl⟩
  have hdeg12 : ∀ k, k ≠ k₀ → 12 ≤ deg k ∧ (deg k = 12 → ψ k = χ) := by
    intro k hk
    by_cases hkχ : ψ k = χ
    · refine ⟨?_, fun _ => hkχ⟩
      have h := hdegψ k
      rw [hkχ, hχ1] at h
      have : deg k = 12 := by exact_mod_cast h.symm
      omega
    · obtain ⟨d, hd, hd1⟩ := hgap (ψ k) (hmemIrr k) (hother k hk) hkχ
      have h := hdegψ k
      rw [hd1] at h
      have : deg k = d := by exact_mod_cast h.symm
      refine ⟨by omega, fun h12 => by omega⟩
  have hdim : Module.finrank ℂ data.vector = ∑ k, deg k := by
    have h := congrFun hdecomp 1
    simp only [one_mul] at h
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have : (Module.finrank ℂ data.vector : ℂ) = ((∑ k, deg k : ℕ) : ℂ) := by
      rw [h, Nat.cast_sum]
      exact Finset.sum_congr rfl fun k _ => hdegψ k
    exact_mod_cast this
  have hdegk₀ : deg k₀ = 1 := by
    have h := hdegψ k₀
    rw [hk₀1, Pi.one_apply] at h
    exact_mod_cast h.symm
  have hsplit : ∑ k, deg k = 1 + ∑ k ∈ Finset.univ.erase k₀, deg k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀), hdegk₀]
  constructor
  · intro hne
    rw [hdim, hsplit]
    have hne' : (Finset.univ.erase k₀).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hne
      rw [FiniteComplexRepresentation.character, Representation.char_one, hdim, hsplit,
        hempty, Finset.sum_empty]
      norm_num
    obtain ⟨k₁, hk₁⟩ := hne'
    have h12 := (hdeg12 k₁ (Finset.ne_of_mem_erase hk₁)).1
    have := Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hk₁
    omega
  · intro h13
    rw [hdim, hsplit] at h13
    have hne' : (Finset.univ.erase k₀).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at h13
      omega
    obtain ⟨k₁, hk₁⟩ := hne'
    have hk₁ne := Finset.ne_of_mem_erase hk₁
    have hrest : ∑ k ∈ (Finset.univ.erase k₀).erase k₁, deg k = 0 := by
      have h := Finset.add_sum_erase _ deg hk₁
      have h12 := (hdeg12 k₁ hk₁ne).1
      omega
    have hrest0 : ∀ k ∈ (Finset.univ.erase k₀).erase k₁, False := by
      intro k hk
      have hk₀' : k ≠ k₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
      have h12 := (hdeg12 k hk₀').1
      have := Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hk
      omega
    have hk₁deg : deg k₁ = 12 := by
      have h := Finset.add_sum_erase _ deg hk₁
      omega
    have hψk₁ := (hdeg12 k₁ hk₁ne).2 hk₁deg
    have hempty : (Finset.univ.erase k₀).erase k₁ = ∅ :=
      Finset.eq_empty_of_forall_notMem fun k hk => hrest0 k hk
    have huniv : (Finset.univ : Finset (Fin size)) = {k₀, k₁} := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      by_contra hk
      push Not at hk
      have : k ∈ (Finset.univ.erase k₀).erase k₁ :=
        Finset.mem_erase.mpr ⟨hk.2, Finset.mem_erase.mpr ⟨hk.1, Finset.mem_univ _⟩⟩
      rw [hempty] at this
      exact Finset.notMem_empty _ this
    rw [hdecomp]
    funext g
    rw [huniv, Finset.sum_pair hk₁ne.symm, one_mul, one_mul, hk₀1, hψk₁]
    rfl

theorem relIndex_ne_three_of_GL2_centralizer {G : Type*} [Group G] [Finite G] (t : G)
    (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3)))
    (J : Subgroup G) (hCJ : Subgroup.centralizer ({t} : Set G) ≤ J) :
    (Subgroup.centralizer ({t} : Set G)).relIndex J ≠ 3 := by
  obtain ⟨φ⟩ := hC
  have htJ : t ∈ J := hCJ (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  let t' : J := ⟨t, htJ⟩
  have ht' : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hcent : Subgroup.centralizer ({t'} : Set J) =
      (Subgroup.centralizer ({t} : Set G)).subgroupOf J := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hiso : Nonempty (Subgroup.centralizer ({t'} : Set J) ≃* GL (Fin 2) (ZMod 3)) :=
    ⟨(MulEquiv.subgroupCongr hcent).trans
      ((Subgroup.subgroupOfEquivOfLe hCJ).trans φ)⟩
  have h := GL2_three_central_involution_index_three_obstruction t' ht' hiso
  rw [hcent] at h
  exact h

end CFSG.Semidihedral.GL2Recognition
