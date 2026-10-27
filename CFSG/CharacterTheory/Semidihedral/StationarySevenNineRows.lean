module

public import CFSG.CharacterTheory.Semidihedral.StationarySevenNineSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralOddEigenspaceBound
public import CFSG.CharacterTheory.Semidihedral.Principal.OddKernelGL2ScaledOrders
public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterSevenNineOrdersSupport

public section

open scoped Classical

namespace CFSG.Semidihedral.StationarySevenNine

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.Principal
open CFSG.TwoRankLowerBound.Helpers

theorem local_parameter_nine_rows_of_family {G : Type} [Group G] [Fintype G]
    [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq9 : p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hOF : ActualPrincipalOrderFormulas G t (fS (s n) : G) q e δ₁ δ₂
      (Module.finrank ℂ (basis.representation χ₁).vector)
      (Module.finrank ℂ (basis.representation χ₂).vector)) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    let a₀ := Nat.card CN
    let b₀ := CN.index
    let f₁ := Module.finrank ℂ (basis.representation χ₁).vector
    let f₂ := Module.finrank ℂ (basis.representation χ₂).vector
    let f₃ := Module.finrank ℂ (basis.representation χ₃).vector
    let X : ℕ × ℕ := (Nat.card G, (C t).index)
    n = 5 ∧ q = 9 ∧ e = 1 ∧ Nat.card (C t) = 1440 * a₀ * b₀ ∧
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 20 * a₀ ∧
      ((δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1 ∧ f₁ = 729 ∧ f₂ = 73 ∧ f₃ = 657 ∧
          X = (8514720 * a₀ * b₀ ^ 3, 5913 * b₀ ^ 2)) ∨
        (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1 ∧ f₁ = 71 ∧ f₂ = 567 ∧ f₃ = 497 ∧
          X = (6441120 * a₀ * b₀ ^ 3, 4473 * b₀ ^ 2)) ∨
        (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1 ∧ f₁ = 135 ∧ f₂ = 201 ∧ f₃ = 335 ∧
          X = (7236000 * a₀ * b₀ ^ 3, 5025 * b₀ ^ 2))) := by
  intro CN a₀ b₀ f₁ f₂ f₃ X
  subst hq
  have horder := cleared_first_order_formula (pow_pos hp.pos f) hOF
  have he₁ : e = 1 := by
    rw [he, hq9]
    rfl
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  have hpf := prime_pow_seven_or_nine hp hf (Or.inr hq9)
  have hfodd : ∀ a : ℕ, Odd a → a ∣ f → a = 1 := by
    intro a ha hdvd
    rcases hpf with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Nat.dvd_one.mp hdvd
    · have := Nat.le_of_dvd (by norm_num) hdvd
      obtain ⟨k, hk⟩ := ha
      interval_cases a <;> omega
  obtain ⟨h2part, hCcard, hDcard⟩ := actual_layer_centralizer_orders hG n hn S fS t ht hnonab
    hcentral hnc p f hp hpodd hf hmodel hfodd
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hn5 : n = 5 := by
    apply eq_five_of_modulus hn
    rw [← h2part, hq9, show (9 : ℕ) ^ 2 - 1 = 80 by norm_num, padicValNat_two_eighty]
  have hq3 : 3 ≤ p ^ f := by omega
  have hqodd : Odd (p ^ f) := hpodd.pow
  have he1 : p ^ f % 4 = 1 → e = 1 := fun _ => he₁
  have he3 : p ^ f % 4 = 3 → e = -1 := by
    intro h
    rw [hq9] at h
    norm_num at h
  obtain ⟨hf₁, hf₂, hf₃, ho₁, ho₂, ho₃, hsigns, hsum, hprod, hc₁, hc₂⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal principal hprincipal
      localBasis localPrincipal (p ^ f) hq3 hqodd h2part e he1 he3 φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ
      ν hfam hdeg
  have hM : (2 : ℤ) * (modulus n : ℕ) = 32 := by
    subst hn5
    rfl
  rw [hM] at hc₁ hc₂
  have hrows := (seven_nine_signed_degree_product_finite_alternatives).1 ((p ^ f : ℕ) : ℤ) e
    _ _ _ δ₁ δ₂ δ₃ (Or.inr ⟨by rw [hq9]; norm_num, he₁⟩)
    hf₁ hf₂ hf₃ ho₁ ho₂ ho₃ hsigns hsum hprod hc₁ hc₂
  have hc : Nat.card (C t) = 1440 * a₀ * b₀ := by
    rw [hCcard, hq9]
    ring
  have hd : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 20 * a₀ := by
    have hif : (((p ^ f : ℕ) : ℤ) + if p ^ f % 4 = 1 then 1 else -1) = 10 := by
      rw [hq9]
      norm_num
    have h : (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) = 20 * a₀ := by
      rw [hDcard, hif]
      ring
    exact_mod_cast h
  subst he₁
  rw [hq9] at horder
  refine ⟨hn5, hq9, rfl, hc, hd, ?_⟩
  rcases hrows with ⟨h7, -⟩ | ⟨-, hfs⟩
  · exfalso
    rw [hq9] at h7
    norm_num at h7
  · rcases hfs with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨⟨rfl, rfl, rfl⟩, h1, h2, h3⟩ := h
    · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 729 := by
        exact_mod_cast h1
      rw [hf1] at horder
      exact Or.inl ⟨rfl, rfl, rfl, by exact_mod_cast h1, by exact_mod_cast h2,
        by exact_mod_cast h3, order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
          (by norm_num) hc hd horder (by norm_num) (by norm_num)⟩
    · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 71 := by
        exact_mod_cast h1
      rw [hf1] at horder
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl, by exact_mod_cast h1, by exact_mod_cast h2,
        by exact_mod_cast h3, order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
          (by norm_num) hc hd horder (by norm_num) (by norm_num)⟩)
    · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 135 := by
        exact_mod_cast h1
      rw [hf1] at horder
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl, by exact_mod_cast h1, by exact_mod_cast h2,
        by exact_mod_cast h3, order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
          (by norm_num) hc hd horder (by norm_num) (by norm_num)⟩)

theorem family_first_character_rat {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (t : G)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (e : ℤ) (k : ℕ) (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index)
    (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e k φ
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (h1 : Module.finrank ℂ (basis.representation χ₁).vector ≠ 1)
    (h2 : Module.finrank ℂ (basis.representation χ₂).vector ≠
      Module.finrank ℂ (basis.representation χ₁).vector)
    (h3 : Module.finrank ℂ (basis.representation χ₃).vector ≠
      Module.finrank ℂ (basis.representation χ₁).vector)
    (h4 : Module.finrank ℂ (basis.representation χ₄).vector ≠
      Module.finrank ℂ (basis.representation χ₁).vector) (g : G) :
    ∃ r : ℚ, (basis.representation χ₁).character g = r := by
  obtain ⟨-, hδ₁, -, -, -, -, -, -, -, -, -, hB, -, -, -, hodd⟩ := hfam
  have hχ₁B : χ₁ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
  have hχ₁1 : (basis.representation χ₁).character 1 =
      (Module.finrank ℂ (basis.representation χ₁).vector : ℂ) :=
    (basis_character_one basis χ₁).1
  refine CFSG.LyonsUnitaryFour.character_rat_of_isolated_principal_block basis ideal hprincipal
    hχ₁B {1} (fun x hx => ⟨(Module.finrank ℂ (basis.representation χ₁).vector : ℚ), by
      rw [Set.mem_singleton_iff.mp hx, hχ₁1]
      norm_num⟩) ?_ g
  intro b hb hbval
  have hb1 : (basis.representation b).character 1 =
      (Module.finrank ℂ (basis.representation χ₁).vector : ℂ) := by
    rw [hbval 1 rfl, hχ₁1]
  have hodd1 := hodd 1 (by rw [orderOf_one]; exact odd_one)
  rw [hB] at hb
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hb
  rcases hb with ((hb | hb | hb | hb | hb) | ⟨j, hj, hb⟩) | ⟨i, hi, hb⟩
  · exfalso
    rw [hb, hprincipal, Pi.one_apply] at hb1
    apply h1
    exact_mod_cast hb1.symm
  · exact hb
  · exfalso
    rw [hb, (basis_character_one basis _).1] at hb1
    apply h2
    exact_mod_cast hb1
  · exfalso
    rw [hb, (basis_character_one basis _).1] at hb1
    apply h3
    exact_mod_cast hb1
  · exfalso
    rw [hb, (basis_character_one basis _).1] at hb1
    apply h4
    exact_mod_cast hb1
  · exfalso
    rw [← hb, hodd1.1 j hj, hχ₁1] at hb1
    rcases hδ₁ with rfl | rfl <;> norm_num at hb1
  · exfalso
    rw [← hb, hodd1.2.1 i hi, hχ₁1] at hb1
    rcases hδ₁ with rfl | rfl <;> norm_num at hb1

theorem character_ne_degree_of_simple {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index)
    (hχ : Module.finrank ℂ (basis.representation χ).vector ≠ 1) {a : G} (ha : a ≠ 1) :
    (basis.representation χ).character a ≠ (basis.representation χ).character 1 := by
  intro h
  have hker := CFSG.Wreathed.FourPointGaussianColumns.ker_eq_bot_of_character_ne_one
    (basis.representation χ) (basis.irreducible χ) (by
      intro h1
      apply hχ
      have h1' := congrFun h1 1
      rw [(basis_character_one basis χ).1, Pi.one_apply] at h1'
      exact_mod_cast h1')
  have hρ := GL2ScaledOrders.rep_eq_one_of_character_eq
    (basis.representation χ).representation a h
  have hmem : a ∈ MonoidHom.ker (basis.representation χ).representation := hρ
  rw [hker] at hmem
  exact ha (Subgroup.mem_bot.mp hmem)

theorem supplied_quaternion_sixteen {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (fS : SemidihedralGroup 5 ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r 5) : G) ^ 2 ^ (5 - 2)) :
    ∃ Q : Subgroup G, Q ≤ C t ∧ IsPGroup 2 Q ∧ Nat.card Q = 16 ∧ t ∈ Q ∧
      ∀ u ∈ Q, u ≠ 1 → t ∈ Subgroup.zpowers u := by
  obtain ⟨-, -, hcent, -, -, -⟩ := supplied_t_s_facts (by norm_num) fS ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hQcard, hzQ, -, hQinv, -, -, -, -, -⟩ :=
    supplied_index_two_and_element_structure 5 (by norm_num) fS
  set Q₀ : Subgroup (S : Subgroup G) := Subgroup.closure {fS (r 5) ^ 2, fS (r 5) * fS (s 5)}
    with hQ₀
  set Q : Subgroup G := Q₀.map (S : Subgroup G).subtype with hQ
  have hz : (((fS (r 5)) ^ (2 ^ (5 - 1) / 2) : (S : Subgroup G)) : G) = t := by
    rw [ht, Subgroup.coe_pow]
    norm_num
  have hQS : Q ≤ (S : Subgroup G) := Subgroup.map_subtype_le _
  have hQ2 : IsPGroup 2 Q := S.isPGroup'.to_le hQS
  have htQ : t ∈ Q := by
    rw [← hz]
    exact Subgroup.mem_map_of_mem _ hzQ
  have hQt : ∀ g ∈ Q, orderOf g = 2 → g = t := by
    rintro _ ⟨g, hg, rfl⟩ hg2
    have hg2' : orderOf g = 2 := (Subgroup.orderOf_coe g).symm.trans hg2
    rw [← hz]
    exact congrArg Subtype.val (hQinv g hg hg2')
  refine ⟨Q, hQS.trans (centered_sylow_le_centralizer (by norm_num) fS hcent), hQ2, ?_, htQ,
    fun u hu hu1 => mem_zpowers_of_unique_involution Q hQ2 hQt hu hu1⟩
  rw [Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective]
  exact hQcard

theorem central_five_eigenspace_data {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hrat : ∀ g : G, ∃ r : ℚ, (basis.representation χ).character g = r)
    {t : G} (ht : orderOf t = 2) (hχt : ‖(basis.representation χ).character t‖ = 9)
    (A : Subgroup G)
    (hAZ : ∀ a ∈ A, a ∈ Subgroup.centralizer {t} ∧ ∀ c ∈ Subgroup.centralizer {t}, a * c = c * a)
    (hA5 : Nat.card A = 5) (Q : Subgroup G) (hQC : Q ≤ Subgroup.centralizer {t})
    (hQ2 : IsPGroup 2 Q) (hQ16 : Nat.card Q = 16) (htQ : t ∈ Q)
    (hQt : ∀ u ∈ Q, u ≠ 1 → t ∈ Subgroup.zpowers u)
    (hker : ∃ a ∈ A, (basis.representation χ).character a ≠
      (basis.representation χ).character 1) :
    ∀ z ∈ A, z ≠ 1 → ∃ d₀ m : ℕ, 0 < m ∧ 9 ≤ d₀ ∧
      Module.finrank ℂ (basis.representation χ).vector = d₀ + 4 * (16 * m) ∧
      (basis.representation χ).character z = (d₀ : ℂ) - (16 * m : ℕ) := by
  intro z hz hz1
  set ρ := (basis.representation χ).representation with hρdef
  have hρ : ρ.character = (basis.representation χ).character := rfl
  obtain ⟨hmult, hprin, -⟩ := central_odd_prime_principal_eigenspace_degree_bound basis ideal
    principal hprincipal hχ ρ hρ ht A hAZ Nat.prime_five ⟨2, rfl⟩ hA5 Q hQC hQ2 htQ hQt
    (fun a _ => hrat a) hker
  have hz5 : z ^ 5 = 1 := by
    have h := A.orderOf_dvd_natCard hz
    rw [hA5] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  obtain ⟨q, hq⟩ := hrat z
  obtain ⟨d, hd, hdim, hval⟩ := rational_prime_order_eigenspaces ρ Nat.prime_five hz5 (q := q)
    (by rw [hρ]; exact hq)
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (5 : ℕ))) 5 :=
    Complex.isPrimitiveRoot_exp 5 (by norm_num)
  obtain ⟨m, hm, hmeq⟩ := hmult z hz hz1 _ hζ.pow_eq_one (hζ.ne_one (by norm_num))
  rw [hd _ hζ.pow_eq_one (hζ.ne_one (by norm_num)), hQ16] at hmeq
  have hprin' := hprin z hz hz1
  rw [hρ, hχt] at hprin'
  have hd₀ : 9 ≤ Module.finrank ℂ (Module.End.eigenspace (ρ z) 1) := by exact_mod_cast hprin'
  refine ⟨Module.finrank ℂ (Module.End.eigenspace (ρ z) 1), m, hm, hd₀, ?_, ?_⟩
  · rw [hdim, hmeq]
  · rw [← hρ, hval, hmeq]

end CFSG.Semidihedral.StationarySevenNine
