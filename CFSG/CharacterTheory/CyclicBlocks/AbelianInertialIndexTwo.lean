module

public import CFSG.CharacterTheory.CyclicBlocks.AbelianFamily
public import CFSG.CharacterTheory.CyclicBlocks.LabelReality

public section

open scoped BigOperators Classical

namespace CFSG.CyclicBlocks

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Semidihedral.Principal

theorem principal_block_abelian_sylow_inverting_index_two {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow p G) (hcomm : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (hN : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2)
    (τ : G) (hτN : τ ∈ Subgroup.normalizer (P : Set G))
    (hτ : ∀ x ∈ (P : Subgroup G), τ * x * τ⁻¹ = x⁻¹) :
    ∃ (ψ₁ : basis.index) (ψ : ℕ → basis.index) (δ : ℤ),
      (δ = 1 ∨ δ = -1) ∧ ψ₁ ≠ principal ∧
      Set.InjOn ψ (Finset.Icc 1 ((Nat.card P - 1) / 2)) ∧
      (∀ μ ∈ Finset.Icc 1 ((Nat.card P - 1) / 2), ψ μ ≠ principal ∧ ψ μ ≠ ψ₁) ∧
      (∀ g : G, p ∣ orderOf g → (basis.representation ψ₁).character g = δ) ∧
      (∀ μ ∈ Finset.Icc 1 ((Nat.card P - 1) / 2),
        (Module.finrank ℂ (basis.representation (ψ μ)).vector : ℤ) =
          Module.finrank ℂ (basis.representation ψ₁).vector + δ) ∧
      (∀ g : G, starRingEnd ℂ ((basis.representation ψ₁).character g) =
        (basis.representation ψ₁).character g) ∧
      (∀ μ ∈ Finset.Icc 1 ((Nat.card P - 1) / 2), ∀ g : G,
        starRingEnd ℂ ((basis.representation (ψ μ)).character g) =
          (basis.representation (ψ μ)).character g) ∧
      (Nat.card P = 3 → ∀ g : G, p ∣ orderOf g →
        (basis.representation (ψ 1)).character g = -δ) := by
  classical
  have hP : InvertedAbelianSylow P τ := ⟨hcomm, hN, hτN, hτ⟩
  have := hP.isMulCommutative
  obtain ⟨hodd, h3⟩ := card_sylow_odd_three_le_of_relIndex hp P hN
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  obtain ⟨basisP⟩ := finiteIrreducibleCharacterBasis_exists (G := (P : Subgroup G))
  obtain ⟨principalP, hprincipalP⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    basisP (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalP
  obtain ⟨T, hT0, hT1, hT2, hTcard⟩ := exists_conj_transversal basisP hodd principalP hprincipalP
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨a, b, δ, haB, hao, hbinj, hb, hδ, hbdeg, hTdec⟩ :=
    hP.abelian_inversion_family_decomposition basis ideal hp principal hprincipal basisP
      principalP hprincipalP hTne hT0 hT1
  have hval := fun (z : (P : Subgroup G)) (hz : z ≠ 1) =>
    hP.abelian_inversion_values basis ideal hp principal hprincipal basisP principalP hprincipalP
      hT0 hT1 hT2 hTcard a b δ haB hao hbinj hb hδ hTdec z hz
  have hsing : ∀ g : G, p ∣ orderOf g → ∃ z : (P : Subgroup G), z ≠ 1 ∧
      ∀ θ ∈ B, (basis.representation θ).character g =
        (basis.representation θ).character z := by
    intro g hg
    obtain ⟨x, hx, hx1, y, hxy, hy, hconj⟩ := exists_isConj_mul_of_dvd_orderOf_of_sylow P hg
    refine ⟨⟨x, hx⟩, fun h => hx1 (congrArg Subtype.val h), fun θ hθ => ?_⟩
    rw [label_character_isConj basis θ hconj,
      hP.principal_section_constant basis ideal hp principal hprincipal hx hx1 hxy hy hθ]
  have hTreal : ∀ (k : T) (g : G),
      starRingEnd ℂ (subgroupProjection basis B P
        (fun w => 1 - (basisP.representation k).character w) g) =
        subgroupProjection basis B P (fun w => 1 - (basisP.representation k).character w) g := by
    intro k g
    by_cases hg : p ∣ orderOf g
    · obtain ⟨x, hx, hx1, y, hxy, hy, hconj⟩ := exists_isConj_mul_of_dvd_orderOf_of_sylow P hg
      have hz1 : (⟨x, hx⟩ : (P : Subgroup G)) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
      have h := hP.subgroupProjection_section basis ideal hp principal hprincipal
        (fun w => 1 - (basisP.representation k).character w) ⟨x, hx⟩ hz1 hxy hy
      rw [subgroupProjection_isConj basis B P _ hconj, h]
      simp only [map_add, map_sub, map_one, finite_character_conjugate_inverse, inv_inv]
      ring
    · rw [subgroupProjection_eq_zero_of_coprime basis ideal p principal
        (fun x hx => orderOf_dvd_of_mem_sylow P hx) _
        (by simp only [label_character_one_of_comm, sub_self]) hg, map_zero]
  have hreal : ∀ k : T,
      (∀ g, starRingEnd ℂ ((basis.representation a).character g) =
        (basis.representation a).character g) ∧
      ∀ g, starRingEnd ℂ ((basis.representation (b k)).character g) =
        (basis.representation (b k)).character g := fun k =>
    real_of_one_add_sub_real basis (hb k).2.2 hδ fun g => by rw [← hTdec k g, hTreal k g]
  obtain ⟨k₀, hk₀⟩ := hTne
  have hrT : Fintype.card (Finset.Icc 1 ((Nat.card P - 1) / 2)) = Fintype.card T := by
    rw [Fintype.card_coe, Fintype.card_coe, Nat.card_Icc]
    omega
  let e : Finset.Icc 1 ((Nat.card P - 1) / 2) ≃ T := Fintype.equivOfCardEq hrT
  let ψ : ℕ → basis.index := fun i =>
    if h : i ∈ Finset.Icc 1 ((Nat.card P - 1) / 2) then b (e ⟨i, h⟩) else principal
  have hψ : ∀ i (h : i ∈ Finset.Icc 1 ((Nat.card P - 1) / 2)), ψ i = b (e ⟨i, h⟩) :=
    fun i h => by simp only [ψ, h, ↓reduceDIte]
  refine ⟨a, ψ, δ, hδ, hao, fun i hi i' hi' hii => ?_, fun i hi => ?_, fun g hg => ?_,
    fun i hi => ?_, (hreal ⟨k₀, hk₀⟩).1, fun i hi => ?_, fun h3' g hg => ?_⟩
  · have h := e.injective (hbinj ((hψ i hi).symm.trans (hii.trans (hψ i' hi'))))
    exact congrArg Subtype.val h
  · rw [hψ i hi]
    exact ⟨(hb _).2.1, (hb _).2.2⟩
  · obtain ⟨z, hz, hθ⟩ := hsing g hg
    rw [hθ a haB]
    exact (hval z hz).1
  · rw [hψ i hi]
    exact hbdeg _
  · rw [hψ i hi]
    exact (hreal _).2
  ·
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 ((Nat.card P - 1) / 2) := by
      rw [h3']
      decide
    obtain ⟨z, hz, hθ⟩ := hsing g hg
    rw [hψ 1 h1, hθ _ (hb _).1, (hval z hz).2]
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp (by omega : T.card = 1)
    have htT : t ∈ T := by
      rw [ht]
      exact Finset.mem_singleton_self t
    have hk : ((e ⟨1, h1⟩ : T) : basisP.index) = t :=
      Finset.card_le_one.mp (by omega) _ (e ⟨1, h1⟩).2 _ htT
    have hsum := sum_conj_transversal basisP principalP hprincipalP hT0 hT1 hT2
      (fun φ => (basisP.representation φ).character z)
    rw [ht, Finset.sum_singleton, sum_label_character_eq_zero_of_ne_one basisP hz, hprincipalP,
      Pi.one_apply, conjugateLabel_character_eq_inv] at hsum
    rw [hk, hsum]
    ring

end CFSG.CyclicBlocks
