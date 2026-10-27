module

public import CFSG.CharacterTheory.Semidihedral.Principal.PureFivePowerNontrivialOddCoreSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.PureFivePowerTorusAlternatingFour

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.LyonsUnitaryFour

theorem perfect_field_factor_one_pure_five_power_parameter_has_nontrivial_odd_core
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (a : ℕ) (ha : 1 ≤ a) :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    ((q : ℤ) + e) / 2 = 5 ^ a → N t ≠ ⊥ := by
  intro q e hqa hN
  have := Fintype.ofFinite G
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq' : 3 < q := hq
  set s₀ : G := ((fS (s n) : S) : G) with hs₀def
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ with hVdef
  set D : Subgroup G := Subgroup.centralizer (V : Set G) with hDdef
  set W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype with hWdef
  set H : Subgroup G := Subgroup.normalizer (W : Set G) with hHdef
  set K : Subgroup G := Subgroup.centralizer (W : Set G) with hKdef
  obtain ⟨hzt, ht2, -, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨hWcyc, hW5, hR, hA4, -, -, ⟨P, hPW⟩, -⟩ :=
    perfect_trivial_core_pure_five_power_torus_has_alternating_four_centralizer_quotient n hn S fS
      t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY a ha hqa
  have hWcyc : IsCyclic W := hWcyc
  have hW5 : Nat.card W = 5 ^ a := hW5
  have hR : (CFSG.pPrimeCore 2 K).map K.subtype = W := hR
  have hA4 : Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) := hA4
  have hPW : (P : Subgroup G) = W := hPW
  obtain ⟨hC, -, -, -, -, ⟨hsup, hdisj, -⟩, -, -, -, ⟨d₀, -, -, -, -, -, ⟨eD⟩, -, P₂, hP₂⟩, -, -,
      -, hKH, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hC : Nat.card (C t) = 2 * q * (q ^ 2 - 1) := hC
  have hsup : V ⊔ W = D := hsup
  have hdisj : Disjoint V W := hdisj
  have hKH : K.relIndex H = 2 := hKH
  have hP₂ : (P₂ : Subgroup H).map H.subtype = Subgroup.zpowers d₀ ⊔ Subgroup.zpowers s₀ := hP₂
  have hdih : ∃ Q : Sylow 2 H, Nonempty ((Q : Subgroup H) ≃* DihedralGroup 4) :=
    ⟨P₂, ⟨(Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
      ((MulEquiv.subgroupCongr hP₂).trans eD)⟩⟩
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have hWodd : Odd (Nat.card W) := by rw [hW5]; exact Odd.pow (by decide)
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨hDcard, -, hDK, -, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have htD : t ∈ D := by
    rw [hDdef, Subgroup.mem_centralizer_iff]
    intro v hv
    have hcomm := mul_comm_of_exponent_two hV.exponent_two (⟨v, hv⟩ : V) ⟨t, htV⟩
    exact congrArg Subtype.val hcomm
  have htK : t ∈ K := hDK htD
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨⟨ideal₂, hmax₂, h2mem⟩, hchar₂⟩ := CFSG.BlockBasics.residue_prime_existence 2
    Nat.prime_two
  have : ideal₂.IsMaximal := hmax₂
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2 := hchar₂ ideal₂ hmax₂ h2mem
  obtain ⟨⟨ideal₅, hmax₅, h5mem⟩, hchar₅⟩ := CFSG.BlockBasics.residue_prime_existence 5
    (by norm_num)
  have : ideal₅.IsMaximal := hmax₅
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₅) 5 := hchar₅ ideal₅ hmax₅ h5mem
  obtain ⟨χ₁, χ₂, χ₃, δ₁, δ₂, δ₃, hodd, hf₁, hf₂, hf₃, ho₃, hd₁₂, hd₁₃, hd₂₃, hδ₁, hδ₂, hδ₃,
      h₁t, h₂t, h₃t, hvalw, hM, hne₁, hne₂, hOF₁, hOF₂⟩ :=
    PureFiveNontrivialCore.pure_five_principal_tuple n hn S fS t ht hnonab hcentral hnc p f hp
      hpodd hf hq hmodel hN hY a ha basis principal hprincipal ideal₂ hqa
  have h₁t : (basis.representation χ₁).character t = δ₁ * e * q := h₁t
  have h₂t : (basis.representation χ₂).character t = -(δ₂ * e * q) := h₂t
  have hvalw : ∀ w ∈ W, Subgroup.zpowers w = W →
      (basis.representation χ₁).character (t * w) = -δ₁ ∧
      (basis.representation χ₂).character (t * w) = δ₂ ∧
      (basis.representation χ₃).character (t * w) = -δ₃ := hvalw
  have hne₁ : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) - e * δ₁ * q ≠ 0 := hne₁
  have hne₂ : (Module.finrank ℂ (basis.representation χ₂).vector : ℚ) + e * δ₂ * q ≠ 0 := hne₂
  have hOF₁ : (Nat.card G : ℚ) = (Nat.card (C t) : ℚ) ^ 3 / (Nat.card D : ℚ) ^ 2 *
      ((Module.finrank ℂ (basis.representation χ₁).vector : ℚ) *
          (Module.finrank ℂ (basis.representation χ₁).vector + δ₁) /
        (Module.finrank ℂ (basis.representation χ₁).vector - e * δ₁ * q) ^ 2) *
      ((q + e) / q) := hOF₁
  have hOF₂ : (Nat.card G : ℚ) = (Nat.card (C t) : ℚ) ^ 3 / (Nat.card D : ℚ) ^ 2 *
      ((Module.finrank ℂ (basis.representation χ₂).vector : ℚ) *
          (Module.finrank ℂ (basis.representation χ₂).vector + δ₂) /
        (Module.finrank ℂ (basis.representation χ₂).vector + e * δ₂ * q) ^ 2) *
      ((q - e) / q) := hOF₂
  have hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t := by
    obtain ⟨-, -, h⟩ :=
      CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn S fS
    have hz : (((fS (r n)) ^ 2 ^ (n - 2) : S) : G) = t := by rw [ht, Subgroup.coe_pow]
    intro x
    rw [← hz]
    exact h Group.IsPerfect.commutator_eq_top x
  have hWfact : Nat.card W = 5 ^ (Nat.card G).factorization 5 := by
    rw [← hPW]
    exact P.card_eq_multiplicity
  have : IsCyclic ((Sylow.ofCard W hWfact : Sylow 5 G) : Subgroup G) := hWcyc
  obtain ⟨ρ, δ, hδ, hcase, hpos, hcol⟩ :=
    PureFiveNontrivialCore.two_generator_column_identity basis principal hprincipal ideal₂ ideal₅
      (Sylow.ofCard W hWfact) a ha hW5 hKH hR hA4 hdih t htK hinvol χ₁ χ₂ χ₃ hodd hd₁₂ hd₁₃ hd₂₃
      (-(δ₁ : ℂ)) δ₂ (-(δ₃ : ℂ)) (fun w hw => hvalw w w.2 hw)
  have he : e = 1 ∨ e = -1 := by
    show (if q % 4 = 1 then (1 : ℤ) else -1) = 1 ∨ (if q % 4 = 1 then (1 : ℤ) else -1) = -1
    split_ifs <;> simp
  have hm : 2 * ((5 ^ a : ℕ) : ℤ) = q + e := by
    have hqodd : Odd q := hpodd.pow
    have hev : Even ((q : ℤ) + e) := by
      obtain ⟨k, hk⟩ := hqodd
      rcases he with h | h <;> rw [h]
      · exact ⟨(k : ℤ) + 1, by rw [hk]; push_cast; ring⟩
      · exact ⟨(k : ℤ), by rw [hk]; push_cast; ring⟩
    push_cast
    rw [← hqa]
    exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp hev)
  have hcZ : ((Nat.card (C t) : ℕ) : ℤ) = 2 * q * ((q : ℤ) ^ 2 - 1) := by
    have h1q : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h := congrArg (Nat.cast : ℕ → ℤ) hC
    push_cast [Nat.cast_sub h1q] at h
    linear_combination h
  have hdZ : ((Nat.card D : ℕ) : ℤ) = 2 * ((q : ℤ) + e) := by
    rw [hDcard, hW5, ← hm]
    push_cast
    ring
  have hq3 : (3 : ℤ) < q := by exact_mod_cast hq'
  have hD0 : (Nat.card D : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hFρ : (basis.representation ρ).character 1 =
      (Module.finrank ℂ (basis.representation ρ).vector : ℂ) := (basis_character_one basis ρ).1
  rcases hcase with ⟨hρ, hδv⟩ | ⟨hρ, hδv⟩ | ⟨hρ, hδv⟩
  ·
    have hδ' : δ = -δ₁ := by exact_mod_cast hδv
    rw [hρ, h₁t, hδ', Int.cast_neg] at hcol
    have hcolZ : (Nat.card G : ℤ) * ((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) -
        δ₁ * e * q) ^ 2 = 3 * ((5 ^ a : ℕ) : ℤ) * (Nat.card (C t) : ℤ) ^ 2 *
          ((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) *
            ((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) - δ₁)) := by
      have h : (((Nat.card G : ℤ) * ((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) -
          δ₁ * e * q) ^ 2 : ℤ) : ℂ) = ((3 * ((5 ^ a : ℕ) : ℤ) * (Nat.card (C t) : ℤ) ^ 2 *
            ((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) *
              ((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) - δ₁)) : ℤ) : ℂ) := by
        push_cast
        linear_combination hcol
      exact_mod_cast h
    have hOFZ : (Nat.card G : ℤ) * (Nat.card D : ℤ) ^ 2 *
        (((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) - e * δ₁ * q) ^ 2 * q) =
        (Nat.card (C t) : ℤ) ^ 3 * ((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) *
          ((Module.finrank ℂ (basis.representation χ₁).vector : ℤ) + δ₁) * (q + e)) := by
      have h := PrimeTorusExclusion.cleared_order_formula hD0 hne₁ hq0 hOF₁
      exact_mod_cast h
    exact PureFiveNontrivialCore.case_one_false hcZ hdZ hm
      (by have : 5 ≤ 5 ^ a := Nat.le_self_pow (by omega) 5; exact_mod_cast this) hq3 he
      (by exact_mod_cast hf₁) hδ₁ hcolZ hOFZ
  ·
    have hδ' : δ = δ₂ := by exact_mod_cast hδv
    rw [hρ, h₂t, hδ'] at hcol
    have hcolZ : (Nat.card G : ℤ) * ((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) +
        δ₂ * e * q) ^ 2 = 3 * ((5 ^ a : ℕ) : ℤ) * (Nat.card (C t) : ℤ) ^ 2 *
          ((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) *
            ((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) + δ₂)) := by
      have h : (((Nat.card G : ℤ) * ((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) +
          δ₂ * e * q) ^ 2 : ℤ) : ℂ) = ((3 * ((5 ^ a : ℕ) : ℤ) * (Nat.card (C t) : ℤ) ^ 2 *
            ((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) *
              ((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) + δ₂)) : ℤ) : ℂ) := by
        push_cast
        linear_combination hcol
      exact_mod_cast h
    have hOFZ : (Nat.card G : ℤ) * (Nat.card D : ℤ) ^ 2 *
        (((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) + e * δ₂ * q) ^ 2 * q) =
        (Nat.card (C t) : ℤ) ^ 3 * ((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) *
          ((Module.finrank ℂ (basis.representation χ₂).vector : ℤ) + δ₂) * (q - e)) := by
      have h := PrimeTorusExclusion.cleared_order_formula hD0 hne₂ hq0 hOF₂
      exact_mod_cast h
    exact PureFiveNontrivialCore.case_two_false hcZ hdZ hm
      (by exact_mod_cast dvd_pow_self 5 (by omega : a ≠ 0)) hq3 he (by exact_mod_cast hf₂) hδ₂
      hcolZ hOFZ
  ·
    have hδ' : δ = -δ₃ := by exact_mod_cast hδv
    rw [hρ, h₃t, hδ', Int.cast_neg] at hcol
    have hcolZ : 1 * (Nat.card G : ℤ) * ((Module.finrank ℂ (basis.representation χ₃).vector : ℤ) +
        δ₃) ^ 2 = 3 * ((5 ^ a : ℕ) : ℤ) * (Nat.card (C t) : ℤ) ^ 2 *
          ((Module.finrank ℂ (basis.representation χ₃).vector : ℤ) *
            ((Module.finrank ℂ (basis.representation χ₃).vector : ℤ) - δ₃)) := by
      have h : ((1 * (Nat.card G : ℤ) * ((Module.finrank ℂ (basis.representation χ₃).vector : ℤ) +
          δ₃) ^ 2 : ℤ) : ℂ) = ((3 * ((5 ^ a : ℕ) : ℤ) * (Nat.card (C t) : ℤ) ^ 2 *
            ((Module.finrank ℂ (basis.representation χ₃).vector : ℤ) *
              ((Module.finrank ℂ (basis.representation χ₃).vector : ℤ) - δ₃)) : ℤ) : ℂ) := by
        push_cast
        linear_combination hcol
      exact_mod_cast h
    have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff, ← hzt]
      have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn))
        (fS.symm ⟨x, hx⟩)
      have h' := congrArg (fun w => ((fS w : S) : G)) h
      simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using h'
    obtain ⟨g₀, hg₀, hGcard⟩ := PrimeTorusExclusion.card_eq_two_pow_mul_odd (by omega) S fS ⊤
      le_top
    obtain ⟨c₀, hc₀, hCcard⟩ := PrimeTorusExclusion.card_eq_two_pow_mul_odd (by omega) S fS (C t)
      hSC
    rw [Subgroup.card_top] at hGcard
    exact PrimeTorusExclusion.case_alpha_three_false (G := (Nat.card G : ℤ))
      (c := (Nat.card (C t) : ℤ)) hn ⟨g₀, by exact_mod_cast hg₀, by exact_mod_cast hGcard⟩
      ⟨c₀, by exact_mod_cast hc₀, by exact_mod_cast hCcard⟩ hM (by exact_mod_cast ho₃) hδ₃
      (by exact_mod_cast (Odd.pow (by decide) : Odd (5 ^ a))) (Or.inl ⟨rfl, rfl⟩) hcolZ

end CFSG.Semidihedral.Principal
