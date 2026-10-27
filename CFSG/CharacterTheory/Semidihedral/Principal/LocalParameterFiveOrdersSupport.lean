module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerRotationCongruencesSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.PerfectSemidihedralRotationCongruences
public import CFSG.CharacterTheory.Semidihedral.Principal.SignedDegreeFive
public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupCentralizer
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerOrderFormulas

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem supplied_t_s_facts {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (fS : SemidihedralGroup n ≃* S) {t : G} (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    (fS (z n) : G) = t ∧ orderOf t = 2 ∧ (fS (r n) : G) ^ (modulus n / 2) = t ∧
      (fS (s n) : G) ∈ C t ∧ orderOf (fS (s n) : G) = 2 ∧ (fS (s n) : G) ≠ t := by
  have hz : (fS (z n) : G) = t := by
    rw [ht, z, map_pow, SubmonoidClass.coe_pow]
    rfl
  have hM : modulus n / 2 = 2 ^ (n - 2) := by
    rw [modulus, show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos]
  refine ⟨hz, ?_, by rw [hM, ht], ?_, ?_, ?_⟩
  · rw [← hz, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_z n (by omega)
  · rw [← hz, Subgroup.mem_centralizer_singleton_iff]
    have h := (Subgroup.mem_center_iff.mp (z_mem_center n hn)) (s n)
    have h' := congrArg (fun w => ((fS w : S) : G)) h
    simp only [map_mul, Subgroup.coe_mul] at h'
    exact h'
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_s n (by omega)
  · intro h
    rw [← hz] at h
    have hsz : s n = z n := fS.injective (Subtype.ext h)
    rw [s_eq_element n (by omega), z_eq_element n (by omega), element_eq_iff] at hsz
    exact one_ne_zero hsz.2

theorem perfect_family_degree_data {G : Type} [Group G] [Fintype G] [Group.IsPerfect G]
    {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G} (e' : SemidihedralGroup n ≃* (S : Subgroup G))
    {t : G} (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (hqM : 2 ^ padicValNat 2 (q ^ 2 - 1) = modulus n)
    (e : ℤ) (he1 : q % 4 = 1 → e = 1) (he3 : q % 4 = 3 → e = -1) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄) :
    1 < (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) ∧
      1 < (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) ∧
      1 < (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) ∧
      Odd (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) ∧
      Odd (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) ∧
      Odd (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) ∧
      ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
        (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧
      1 + δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
          δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) +
          δ₃ * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) = 0 ∧
      (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) *
          (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) =
        (q : ℤ) ^ 2 * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) ∧
      (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) ≡ δ₁ * (2 - e * q)
        [ZMOD 2 * modulus n] ∧
      (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) ≡ -δ₂ * e * q
        [ZMOD 2 * modulus n] := by
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨hrot, -⟩ := actual_principal_rotation_values_and_congruences hG hn ht hnonab basis
    ideal principal hprincipal localBasis localPrincipal q hq3 hqodd e he1 he3 φ δ₁ δ₂ δ₃ δ₄
    χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg e' hcent
  obtain ⟨hlφ, hδ₁, hδ₂, hδ₃, -, -, -, -, -, -, -, hB, -, hodd, hsec, hrel⟩ := hfam
  obtain ⟨hf₁, hf₂, hf₃, -, hsigns, -, -, hprod, -⟩ := hdeg
  obtain ⟨hφ1, -⟩ := family_character_nonconstant hnonab localBasis ideal localPrincipal q φ hlφ
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index),
      c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hodd₁ := (hodd χ₁ (hmem χ₁ (by simp))).mpr (Or.inr (Or.inl rfl))
  have hodd₂ := (hodd χ₂ (hmem χ₂ (by simp))).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hodd₃ := (hodd χ₃ (hmem χ₃ (by simp))).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hsec1 := hsec 1 (by simp)
  simp only [OneMemClass.coe_one, mul_one, hφ1] at hsec1
  obtain ⟨h₁t, h₂t, h₃t, -⟩ := hsec1
  obtain ⟨-, -, hrel1, -⟩ := hrel 1 (by simp)
  rw [(basis_character_one basis χ₁).1, (basis_character_one basis χ₂).1,
    (basis_character_one basis χ₃).1] at hrel1
  have hsum : 1 + δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
      δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) +
      δ₃ * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) = 0 := by
    exact_mod_cast hrel1
  obtain ⟨hc₁, hc₂, -⟩ := perfect_semidihedral_rotation_values_full_sylow_degree_congruences hn
    S e' (e' (r n) : G) t rfl hcent.symm q hq3 hqodd hqM e he1 he3 (basis.representation χ₁)
    (basis.representation χ₂) (basis.representation χ₃) δ₁ δ₂ δ₃ hδ₁ hδ₂ hδ₃
    (by rw [h₁t]; push_cast; ring) (by rw [h₂t]; push_cast; ring) (by rw [h₃t]; push_cast; ring)
    (fun v hv0 hv1 => (hrot v hv0 hv1).1) (fun v hv0 hv1 => (hrot v hv0 hv1).2.1)
    (fun v hv0 hv1 => (hrot v hv0 hv1).2.2)
  refine ⟨by exact_mod_cast hf₁, by exact_mod_cast hf₂, by exact_mod_cast hf₃,
    by exact_mod_cast hodd₁.natCast, by exact_mod_cast hodd₂.natCast,
    by exact_mod_cast hodd₃.natCast, hsigns, hsum, by exact_mod_cast hprod, hc₁, hc₂⟩

theorem actual_layer_centralizer_orders {G : Type} [Group G] [Finite G]
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hfodd : ∀ a : ℕ, Odd a → a ∣ f → a = 1) :
    2 ^ padicValNat 2 ((p ^ f) ^ 2 - 1) = modulus n ∧
      Nat.card (C t) =
        2 * Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
            (N t)) *
          (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
            (N t)).index * p ^ f * ((p ^ f) ^ 2 - 1) ∧
      (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) =
        2 * Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
            (N t)) * ((p ^ f : ℕ) + if p ^ f % 4 = 1 then 1 else -1) := by
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have h2part : 2 ^ padicValNat 2 ((p ^ f) ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, Nat.factorization_def _ Nat.prime_two] at h
    rw [h]
    rfl
  obtain ⟨-, F, hfield, hfinite, A, a, -, hAodd, hAdvd, -, -, -, -, -, -, -, -, hall⟩ :=
    ActualFourGroupCentralizer.actual_simple_layer_four_group_centralizer_odd_core n hn S fS hG
      t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  let s₀ : C t := ⟨(fS (s n) : G), hsC⟩
  have hs₀ : orderOf s₀ = 2 := by
    rw [← hs2, ← Subgroup.orderOf_coe]
  have hs₀t : s₀ ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  obtain ⟨Psi, -, -, hOC, hSO, hDmap, -, -⟩ := hall s₀ hs₀ hs₀t
  have hA : Nat.card A = 1 := hfodd _ hAodd hAdvd
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
  have hN0 : ActualFourGroupCentralizer.N0 s₀ =
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t) := by
    rw [ActualFourGroupCentralizer.N0, hD]
  have hDcard : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) =
      Nat.card (ActualFourGroupCentralizer.D s₀) := by
    rw [← hDmap, Subgroup.card_map_of_injective Subtype.val_injective]
  refine ⟨h2part, ?_, ?_⟩
  · rw [hOC.C_card, hA, hN0, mul_one]
  · rw [hDcard, hSO.D_card, hA, hN0, ActualFourGroupCentralizer.torusSign]
    push_cast
    ring

theorem cleared_first_order_formula {G : Type} [Group G] [Finite G] {t s : G} {q : ℕ}
    {e δ₁ δ₂ : ℤ} {f₁ f₂ : ℕ} (hq : 0 < q)
    (h : ActualPrincipalOrderFormulas G t s q e δ₁ δ₂ f₁ f₂) :
    (Nat.card G : ℚ) * (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) ^ 2 *
        (((f₁ : ℚ) - e * δ₁ * q) ^ 2 * q) =
      (Nat.card (C t) : ℚ) ^ 3 * ((f₁ : ℚ) * ((f₁ : ℚ) + δ₁) * ((q : ℚ) + e)) := by
  obtain ⟨hne, -, hG, -⟩ := h
  change (Nat.card G : ℚ) = (Nat.card (C t) : ℚ) ^ 3 /
      (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) ^ 2 *
      ((f₁ : ℚ) * (f₁ + δ₁) / (f₁ - e * δ₁ * q) ^ 2) * ((q + e) / q) at hG
  have hd : (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  generalize (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) = D at hd hG ⊢
  generalize (f₁ : ℚ) - e * δ₁ * q = Y at hne hG ⊢
  rw [hG]
  field_simp

theorem order_pair_of_identity {G : Type*} [Group G] [Finite G] (C' : Subgroup G)
    {d a₀ b₀ c₀ d₀ K I : ℕ} {X Y : ℚ} (ha : 0 < a₀) (hb : 0 < b₀) (hc₀ : 0 < c₀)
    (hd₀ : 0 < d₀) (hY : Y ≠ 0) (hc : Nat.card C' = c₀ * a₀ * b₀) (hd : d = d₀ * a₀)
    (h : (Nat.card G : ℚ) * (d : ℚ) ^ 2 * Y = (Nat.card C' : ℚ) ^ 3 * X)
    (hK : (c₀ : ℚ) ^ 3 * X = K * (d₀ : ℚ) ^ 2 * Y) (hKI : K = c₀ * I) :
    (Nat.card G, C'.index) = (K * a₀ * b₀ ^ 3, I * b₀ ^ 2) := by
  have ha' : (a₀ : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd' : (d₀ : ℚ) ≠ 0 := by exact_mod_cast hd₀.ne'
  have hg' : (Nat.card G : ℚ) = K * a₀ * b₀ ^ 3 := by
    apply mul_right_cancel₀ (show (d₀ : ℚ) ^ 2 * (a₀ : ℚ) ^ 2 * Y ≠ 0 by positivity)
    rw [hc, hd] at h
    push_cast at h
    linear_combination h + (a₀ : ℚ) ^ 3 * (b₀ : ℚ) ^ 3 * hK
  have hg : Nat.card G = K * a₀ * b₀ ^ 3 := by exact_mod_cast hg'
  refine Prod.ext hg ?_
  have hmul : Nat.card C' * C'.index = Nat.card G := Subgroup.card_mul_index C'
  rw [hc, hg, hKI] at hmul
  apply Nat.eq_of_mul_eq_mul_left (show 0 < c₀ * a₀ * b₀ by positivity)
  change c₀ * a₀ * b₀ * C'.index = _
  rw [hmul]
  ring

theorem padicValNat_two_twentyFour : padicValNat 2 24 = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem eq_four_of_modulus {n : ℕ} (hn : 4 ≤ n) (h : 2 ^ 3 = modulus n) : n = 4 := by
  rw [modulus] at h
  have := Nat.pow_right_injective le_rfl h
  omega

theorem local_parameter_five_orders_of_family {G : Type} [Group G] [Fintype G]
    [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = 5) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
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
    let X : ℕ × ℕ := (Nat.card G, (C t).index)
    let P₁ : ℕ × ℕ := (68400 * a₀ * b₀ ^ 3, 285 * b₀ ^ 2)
    let P₂ : ℕ × ℕ := (126000 * a₀ * b₀ ^ 3, 525 * b₀ ^ 2)
    let P₃ : ℕ × ℕ := (85680 * a₀ * b₀ ^ 3, 357 * b₀ ^ 2)
    n = 4 ∧ Nat.card (C t) = 240 * a₀ * b₀ ∧
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * a₀ ∧
      (X = P₁ ∨ X = P₂ ∨ X = P₃) ∧ ¬ (X = P₁ ∧ X = P₂) ∧ ¬ (X = P₁ ∧ X = P₃) ∧
      ¬ (X = P₂ ∧ X = P₃) ∧ b₀ ^ 2 ∣ (C t).index := by
  intro CN a₀ b₀ X P₁ P₂ P₃
  subst hq
  have he1 : e = 1 := by rw [he]; rfl
  subst he1
  have horder := cleared_first_order_formula (by norm_num) hOF
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨h2part, hCcard, hDcard⟩ := actual_layer_centralizer_orders hG n hn S fS t ht hnonab
    hcentral hnc 5 1 (by norm_num) (by decide) le_rfl hmodel
    (fun a _ ha => Nat.dvd_one.mp ha)
  simp only [pow_one] at h2part hCcard hDcard
  rw [ite_true] at hDcard
  have hn4 : n = 4 := eq_four_of_modulus hn (by
    rw [← h2part, show (5 : ℕ) ^ 2 - 1 = 24 by norm_num, padicValNat_two_twentyFour])
  have hqM : 2 ^ padicValNat 2 (5 ^ 2 - 1) = modulus n := h2part
  obtain ⟨hf₁, hf₂, hf₃, ho₁, ho₂, ho₃, hsigns, hsum, hprod, hc₁, hc₂⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal principal hprincipal
      localBasis localPrincipal 5 (by norm_num) (by decide) hqM 1 (fun _ => rfl)
      (fun h => absurd h (by norm_num)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg
  have hM : (2 : ℤ) * (modulus n : ℕ) = 16 := by subst hn4; rfl
  rw [hM] at hc₁ hc₂
  have hrows := (five_signed_degree_product_three_alternatives).1 _ _ _ δ₁ δ₂ δ₃ hf₁ hf₂ hf₃
    ho₁ ho₂ ho₃ hsigns hsum (by rw [hprod]; norm_num)
    (by have h := hc₁; rw [show δ₁ * (2 - 1 * ((5 : ℕ) : ℤ)) = -3 * δ₁ by push_cast; ring] at h
        exact h)
    (by have h := hc₂; rw [show -δ₂ * 1 * ((5 : ℕ) : ℤ) = -5 * δ₂ by push_cast; ring] at h
        exact h)
  have hCt : Nat.card (C t) = 240 * a₀ * b₀ := by rw [hCcard]; ring
  have hDt : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * a₀ := by
    have h : (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) = 12 * a₀ := by
      rw [hDcard]
      push_cast
      ring
    exact_mod_cast h
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hdist : ∀ (K₁ I₁ K₂ I₂ : ℕ), I₁ ≠ I₂ →
      ¬ (X = (K₁ * a₀ * b₀ ^ 3, I₁ * b₀ ^ 2) ∧ X = (K₂ * a₀ * b₀ ^ 3, I₂ * b₀ ^ 2)) := by
    rintro K₁ I₁ K₂ I₂ hI ⟨h₁, h₂⟩
    have h := congrArg Prod.snd (h₁.symm.trans h₂)
    exact hI (Nat.eq_of_mul_eq_mul_right (pow_pos hb 2) h)
  have hX : X = P₁ ∨ X = P₂ ∨ X = P₃ := by
    rcases hrows with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨⟨rfl, rfl, rfl⟩, h1, -, -⟩ := h
    · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 19 := by
        exact_mod_cast h1
      rw [hf1] at horder
      exact Or.inl (order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
        (by norm_num) hCt hDt horder (by norm_num) (by norm_num))
    · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 125 := by
        exact_mod_cast h1
      rw [hf1] at horder
      exact Or.inr (Or.inl (order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
        (by norm_num) hCt hDt horder (by norm_num) (by norm_num)))
    · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 35 := by
        exact_mod_cast h1
      rw [hf1] at horder
      exact Or.inr (Or.inr (order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
        (by norm_num) hCt hDt horder (by norm_num) (by norm_num)))
  refine ⟨hn4, hCt, hDt, hX, hdist _ _ _ _ (by norm_num), hdist _ _ _ _ (by norm_num),
    hdist _ _ _ _ (by norm_num), ?_⟩
  rcases hX with h | h | h <;> rw [show (C t).index = X.2 from rfl, h] <;>
    exact Dvd.intro_left _ rfl

end CFSG.Semidihedral.Principal
