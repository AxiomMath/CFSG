module

public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelFaithful
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteCharacters

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

open CFSG.TwoRankLowerBound.Helpers
open scoped ComplexOrder

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

@[expose] def fixedSpaceLayerRepresentation (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) :
    Representation ℂ L (Representation.invariants ((ρ.comp K.subtype).comp O.subtype)) :=
  (fixedSpaceQuotientRepresentation ρ K O).comp L.subtype

theorem fixedSpaceLayerRepresentation_apply (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O))
    (g : L) (v : Representation.invariants ((ρ.comp K.subtype).comp O.subtype)) :
    fixedSpaceLayerRepresentation ρ K O L g v =
      fixedSpaceQuotientRepresentation ρ K O (g : K ⧸ O) v := rfl

variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem fixedSpaceLayerRepresentation_character (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) (g : L) :
    (fixedSpaceLayerRepresentation ρ K O L).character g =
      (fixedSpaceQuotientRepresentation ρ K O).character (g : K ⧸ O) := rfl

omit [FiniteDimensional ℂ V] in
theorem fixedSpaceLayerRepresentation_character_one (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) :
    (fixedSpaceLayerRepresentation ρ K O L).character 1 =
      (fixedSpaceQuotientRepresentation ρ K O).character 1 := rfl

@[expose] def fixedSpaceLayerComplexRepresentation (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) :
    FiniteComplexRepresentation.{0, 0} L where
  vector := Representation.invariants ((ρ.comp K.subtype).comp O.subtype)
  representation := fixedSpaceLayerRepresentation ρ K O L

theorem fixedSpaceLayerComplexRepresentation_degree_le (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) :
    Module.finrank ℂ (fixedSpaceLayerComplexRepresentation ρ K O L).vector ≤
      Module.finrank ℂ V := Submodule.finrank_le _

theorem fixedSpaceLayerRepresentation_cyclic_sections [Fintype G]
    (ρ : Representation ℂ G V) (K : Subgroup G) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O))
    (y : K) (a : ℕ) (ha : 1 ≤ a) (hy : orderOf y = 2 ^ a)
    (yL : L) (hyL : (yL : K ⧸ O) = QuotientGroup.mk' O y) (c : ℂ)
    (hc : ∀ h : ℤ, Odd h → ∀ z : G, Odd (orderOf z) →
      z ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      ρ.character ((y : G) ^ h * z) = c) :
    ∀ h : ℤ, Odd h → ∀ z : L, Odd (orderOf z) →
      z ∈ Subgroup.centralizer ({yL} : Set L) →
      (fixedSpaceLayerRepresentation ρ K O L).character (yL ^ h * z) = c := by
  intro h hh z hz hzy
  have hzX : Odd (orderOf (z : K ⧸ O)) := by rwa [Subgroup.orderOf_coe]
  have hzyX : (z : K ⧸ O) ∈
      Subgroup.centralizer ({QuotientGroup.mk' O y} : Set (K ⧸ O)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hzy ⊢
    have h := congrArg Subtype.val hzy
    simpa only [Subgroup.coe_mul, hyL] using h
  have hvalue := (odd_kernel_fixed_space_character_preserves_cyclic_two_sections
    K O hO y a ha hy ρ c hc).2.2.1 h hh (z : K ⧸ O) hzX hzyX
  rw [fixedSpaceLayerRepresentation_character]
  simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, hyL, QuotientGroup.mk'_apply] using hvalue.1

theorem oddKernel_eq_bot_of_cyclic_section_rigidity [Fintype G] [IsSimpleGroup G]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (Q : ℕ)
    (hQ : 1 < Q) (hdegree : ρ.character 1 = (Q : ℂ))
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (K ⧸ O)) (y : K) (a : ℕ) (ha : 1 ≤ a)
    (hy : orderOf y = 2 ^ a) (yL : L)
    (hyL : (yL : K ⧸ O) = QuotientGroup.mk' O y)
    (hsection : ∀ h : ℤ, Odd h → ∀ z : G, Odd (orderOf z) →
      z ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      ρ.character ((y : G) ^ h * z) = -1)
    (hrigidity : ∀ θ : FiniteComplexRepresentation.{0, 0} L,
      Module.finrank ℂ θ.vector ≤ Q →
      (∀ h : ℤ, Odd h → ∀ z : L, Odd (orderOf z) →
        z ∈ Subgroup.centralizer ({yL} : Set L) → θ.character (yL ^ h * z) = -1) →
      Module.finrank ℂ θ.vector = Q) : O = ⊥ := by
  have hfinrank : Module.finrank ℂ V = Q := by
    rw [Representation.char_one] at hdegree
    exact_mod_cast hdegree
  have hbound : Module.finrank ℂ (fixedSpaceLayerComplexRepresentation ρ K O L).vector ≤ Q :=
    hfinrank ▸ fixedSpaceLayerComplexRepresentation_degree_le ρ K O L
  have hsectionL := fixedSpaceLayerRepresentation_cyclic_sections
    ρ K O hO L y a ha hy yL hyL (-1) hsection
  have hfixed := hrigidity (fixedSpaceLayerComplexRepresentation ρ K O L) hbound hsectionL
  have hfixedOriginal : Module.finrank ℂ
      (Representation.invariants ((ρ.comp K.subtype).comp O.subtype)) =
        Module.finrank ℂ V := hfixed.trans hfinrank.symm
  apply oddKernel_eq_bot_of_fixedSpace_finrank ρ
    (irreducible_ker_eq_bot_of_degree_ne_one ρ ?_) K O hfixedOriginal
  rw [hdegree]
  intro h
  have heq : Q = 1 := by exact_mod_cast h
  omega

theorem oddKernel_eq_bot_of_irreducible_character_section_rigidity
    [Fintype G] [IsSimpleGroup G]
    (β : CFSG.BlocksIrr G) (Q : ℕ) (hQ : 1 < Q) (hdegree : (β : G → ℂ) 1 = (Q : ℂ))
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (K ⧸ O)) (y : K) (a : ℕ) (ha : 1 ≤ a)
    (hy : orderOf y = 2 ^ a) (yL : L)
    (hyL : (yL : K ⧸ O) = QuotientGroup.mk' O y)
    (hsection : ∀ h : ℤ, Odd h → ∀ z : G, Odd (orderOf z) →
      z ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      (β : G → ℂ) ((y : G) ^ h * z) = -1)
    (hrigidity : ∀ θ : FiniteComplexRepresentation.{0, 0} L,
      Module.finrank ℂ θ.vector ≤ Q →
      (∀ h : ℤ, Odd h → ∀ z : L, Odd (orderOf z) →
        z ∈ Subgroup.centralizer ({yL} : Set L) → θ.character (yL ^ h * z) = -1) →
      Module.finrank ℂ θ.vector = Q) : O = ⊥ := by
  obtain ⟨W, hAdd, hModule, hFinite, ρ, hρ, hcharacter⟩ := β.property
  let : AddCommGroup W := hAdd
  let : Module ℂ W := hModule
  let : FiniteDimensional ℂ W := hFinite
  let : ρ.IsIrreducible := hρ
  have hdegreeρ : ρ.character 1 = (Q : ℂ) := by
    simpa only [← hcharacter] using hdegree
  have hsectionρ : ∀ h : ℤ, Odd h → ∀ z : G, Odd (orderOf z) →
      z ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      ρ.character ((y : G) ^ h * z) = -1 := by
    simpa only [← hcharacter] using hsection
  exact oddKernel_eq_bot_of_cyclic_section_rigidity ρ Q hQ hdegreeρ
    K O hO L y a ha hy yL hyL hsectionρ hrigidity

end CFSG.Wreathed.SameFieldOddKernel
