module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerCharacteristicValuation
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOrdersSupport
public import CFSG.CharacterTheory.BlockBasics.LocalRing

public section

open scoped Classical

namespace CFSG.Semidihedral.SimpleLayerFrontier

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.Principal CFSG.TwoRankLowerBound.Helpers

theorem actual_layer_centralizer_orders_with_field_factor {G : Type} [Group G] [Finite G]
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    ∃ h : ℕ, Odd h ∧ h ∣ f ∧
      Nat.card (C t) = 2 * Nat.card CN * CN.index * h * p ^ f * ((p ^ f) ^ 2 - 1) ∧
      (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) =
        2 * Nat.card CN * h * ((p ^ f : ℕ) + if p ^ f % 4 = 1 then 1 else -1) := by
  intro CN
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨-, F, hfield, hfinite, A, a, -, hAodd, hAdvd, -, -, -, -, -, -, -, -, hall⟩ :=
    ActualFourGroupCentralizer.actual_simple_layer_four_group_centralizer_odd_core n hn S fS hG
      t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  let s₀ : C t := ⟨(fS (s n) : G), hsC⟩
  have hs₀ : orderOf s₀ = 2 := by
    rw [← hs2, ← Subgroup.orderOf_coe]
  have hs₀t : s₀ ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  obtain ⟨Psi, -, -, hOC, hSO, hDmap, -, -⟩ := hall s₀ hs₀ hs₀t
  have hD : ActualFourGroupCentralizer.D s₀ =
      (Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype := by
    ext x
    simp only [ActualFourGroupCentralizer.D, KleinFourOddKernel.centralizer,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hN0 : ActualFourGroupCentralizer.N0 s₀ = CN := by
    rw [ActualFourGroupCentralizer.N0, hD]
  have hDcard : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) =
      Nat.card (ActualFourGroupCentralizer.D s₀) := by
    rw [← hDmap, Subgroup.card_map_of_injective Subtype.val_injective]
  refine ⟨Nat.card A, hAodd, hAdvd, ?_, ?_⟩
  · rw [hOC.C_card, hN0]
  · rw [hDcard, hSO.D_card, hN0, ActualFourGroupCentralizer.torusSign]

theorem regular_order_arithmetic {g c d a₀ b₀ h q : ℕ} {e : ℤ} (he : e = 1 ∨ e = -1)
    (hq : 1 < q) (ha : 0 < a₀) (hh : 0 < h)
    (hc : (c : ℤ) = 2 * a₀ * b₀ * h * q * ((q : ℤ) ^ 2 - 1))
    (hd : (d : ℤ) = 2 * a₀ * h * ((q : ℤ) + e))
    (hg : (g : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 * (((q : ℚ) ^ 2 - e * q + 1) / ((q : ℚ) - e) ^ 2)) :
    (g : ℤ) =
      2 * a₀ * b₀ ^ 3 * h * (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 - e * q + 1) := by
  have hcQ : (c : ℚ) = 2 * a₀ * b₀ * h * q * ((q : ℚ) ^ 2 - 1) := by exact_mod_cast hc
  have hdQ : (d : ℚ) = 2 * a₀ * h * ((q : ℚ) + e) := by exact_mod_cast hd
  have hq1 : (1 : ℚ) < q := by exact_mod_cast hq
  have hqe : (q : ℚ) + e ≠ 0 := by
    rcases he with rfl | rfl <;> push_cast <;> intro h0 <;> linarith
  have hqe' : (q : ℚ) - e ≠ 0 := by
    rcases he with rfl | rfl <;> push_cast <;> intro h0 <;> linarith
  have ha' : (a₀ : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hh' : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hsq : (q : ℚ) ^ 2 - 1 = ((q : ℚ) + e) * ((q : ℚ) - e) := by
    rcases he with rfl | rfl <;> push_cast <;> ring
  have hgQ : (g : ℚ) =
      2 * a₀ * b₀ ^ 3 * h * (q : ℚ) ^ 3 * ((q : ℚ) ^ 2 - 1) * ((q : ℚ) ^ 2 - e * q + 1) := by
    rw [hg, hcQ, hdQ, hsq]
    field_simp
  exact_mod_cast hgQ

theorem frontier_regular_order
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hval : 3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) : ℤ) ≤
      padicValNat p (Nat.card G)) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    let a₀ := Nat.card CN
    let b₀ := CN.index
    let e : ℤ := if p ^ f % 4 = 1 then 1 else -1
    ∃ h : ℕ, Odd h ∧ h ∣ f ∧
      Nat.card (C t) = 2 * a₀ * b₀ * h * p ^ f * ((p ^ f) ^ 2 - 1) ∧
      (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) =
        2 * a₀ * h * ((p ^ f : ℕ) + e) ∧
      (Nat.card G : ℤ) = 2 * a₀ * b₀ ^ 3 * h * ((p ^ f : ℕ) : ℤ) ^ 3 *
        (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 2 - e * (p ^ f : ℕ) + 1) ∧
      ((C t).index : ℤ) =
        (b₀ : ℤ) ^ 2 * ((p ^ f : ℕ) : ℤ) ^ 2 * (((p ^ f : ℕ) : ℤ) ^ 2 - e * (p ^ f : ℕ) + 1) := by
  intro CN a₀ b₀ e
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨h, hhodd, hhdvd, hCcard, hDcard⟩ :=
    actual_layer_centralizer_orders_with_field_factor hG n hn S fS t ht hnonab hcentral hnc
      p f hp hpodd hf hmodel
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal, hmax, h2⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, -, -,
      hvalues⟩ :=
    actual_simple_layer_characteristic_valuation_degree_formulas hGnonab n hn S fS t ht2 hnonab
      hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal fS hcent hval
  obtain ⟨-, -, -, -, -, -, -, -, -, -, horder, -⟩ := hvalues
  rw [hcard] at horder
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have he : e = 1 ∨ e = -1 := by
    by_cases h4 : p ^ f % 4 = 1 <;> simp [e, h4]
  have ha : 0 < a₀ := Nat.card_pos
  have hh : 0 < h := hhodd.pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hc : (Nat.card (C t) : ℤ) = 2 * a₀ * b₀ * h * (p ^ f : ℕ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) := by
    rw [hCcard]
    have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    push_cast [Nat.cast_sub this]
    ring
  have hd : (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) =
      2 * a₀ * h * ((p ^ f : ℕ) + e) := hDcard
  have hgZ := regular_order_arithmetic (g := Nat.card G) he hq1 ha hh hc hd (by
    rw [horder])
  refine ⟨h, hhodd, hhdvd, hCcard, hd, hgZ, ?_⟩
  have hmul : (Nat.card (C t) : ℤ) * ((C t).index : ℤ) = Nat.card G := by
    exact_mod_cast Subgroup.card_mul_index (C t)
  rw [hgZ, hc] at hmul
  have hne : (2 * a₀ * b₀ * h * (p ^ f : ℕ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) : ℤ) ≠ 0 := by
    have hq2 : (1 : ℤ) < ((p ^ f : ℕ) : ℤ) ^ 2 := by
      have : (1 : ℤ) < ((p ^ f : ℕ) : ℤ) := by exact_mod_cast hq1
      nlinarith
    have : (0 : ℤ) < 2 * a₀ * b₀ * h * (p ^ f : ℕ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) := by
      have h1 : (0 : ℤ) < a₀ := by exact_mod_cast ha
      have h2 : (0 : ℤ) < b₀ := by exact_mod_cast hb
      have h3 : (0 : ℤ) < h := by exact_mod_cast hh
      have h4 : (0 : ℤ) < ((p ^ f : ℕ) : ℤ) := by exact_mod_cast (by omega : 0 < p ^ f)
      have h5 : (0 : ℤ) < ((p ^ f : ℕ) : ℤ) ^ 2 - 1 := by linarith
      positivity
    exact this.ne'
  apply mul_left_cancel₀ hne
  linear_combination hmul

end CFSG.Semidihedral.SimpleLayerFrontier
