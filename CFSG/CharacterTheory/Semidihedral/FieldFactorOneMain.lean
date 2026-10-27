module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSignedDegrees
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneExtension
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneNumerics
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneAssembly
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Semidihedral.Principal
open CFSG.Wreathed.LinearLocalTwistMoment

theorem centralizer_linear_character_extends
    (G : Type) [Group G] [Finite G] (hindex : ∀ V : Subgroup G, V.index ≠ 2)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hLnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 7 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (θ : C t →* ℂˣ) (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c) :
    ∃ lam : G →* ℂˣ, ∀ c : C t, lam c = θ c := by
  let _ : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨normalizerBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
  obtain ⟨hM4, hKeven, hK2, hhalf⟩ := modulus_eq_four_mul hn
  set k : ℕ := 2 ^ (n - 3) with hk
  have hkpow : ∃ m : ℕ, k = 2 ^ m := ⟨n - 3, rfl⟩
  obtain ⟨lambdaLabel, hlambda, B, hB⟩ := exists_typeStar_block fS hn ht hindex θ hθS hθT basis
    ideal normalizerBasis
  obtain ⟨e, a₀, a₁, a₂, a₃, c₀, he1, he3, he, hqe, ha₀, ha₁, ha₂, ha₃, h01, h02, hsum, hrec,
      hc₀, hc₁, hc₂, hc₃, hSa, -, -, hext⟩ :=
    typeStar_signed_degrees fS hn ht hindex hLnonab hcentral hnc p f hp hpodd hf hmodel θ hθS
      hθT basis ideal normalizerBasis lambdaLabel hlambda B hB
  obtain ⟨e', b₀, b₁, b₂, b₃, -, he1', he3', -, -, hb₀, hb₁, hb₂, hb₃, h01b, h02b, hsumb, hrecb,
      hc₀b, hc₁b, hc₂b, hc₃b, hSb, hprin, -, -⟩ :=
    typeStar_signed_degrees fS hn ht hindex hLnonab hcentral hnc p f hp hpodd hf hmodel 1
      (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl) basis ideal normalizerBasis
      (principalCharacterLabel normalizerBasis)
      (fun x q c _ _ => by
        rw [principalCharacterLabel_character, Pi.one_apply, thetaG_one, Units.val_one])
      (principalCharacterLabel basis)
      (brauerNormalizer_principal_residue_image basis ideal 2 _ S.isPGroup' _
        (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis _
        (principalCharacterLabel_character basis) _
        (principalCharacterLabel_character normalizerBasis))
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hee : e = e' := by
    have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
      obtain ⟨m, hm⟩ := hqodd
      omega
    rcases h4 with h | h
    · rw [he1 h, he1' h]
    · rw [he3 h, he3' h]
  subst hee
  have hb01 : b₀ = 1 := by
    have hprincipal := principalCharacterLabel_character basis
    have hM : (0 : ℤ) < modulus n := by exact_mod_cast (show 0 < modulus n by omega)
    have hL := multiplicityColumn_principal hn fS basis hprincipal
    apply hprin (principalCharacterLabel basis) (coefficientBlock_self_mem _ _ _)
    · have h := (basis_character_one basis (principalCharacterLabel basis)).1
      rw [hprincipal, Pi.one_apply] at h
      exact_mod_cast h.symm
    · rw [hL, hL, ite_eq_left (dvd_zero _), ite_eq_right]
      · norm_num
      · intro hdvd
        have := Int.le_of_dvd (by exact_mod_cast (show 0 < modulus n / 2 by omega)) hdvd
        have h2 : ((modulus n / 2 : ℕ) : ℤ) < modulus n := by
          exact_mod_cast (show modulus n / 2 < modulus n by omega)
        omega
    · rw [hL, hL, ite_eq_left (dvd_zero _), ite_eq_right]
      · norm_num
      · intro hdvd
        have := Int.le_of_dvd (by norm_num) hdvd
        have h8 : (8 : ℤ) ≤ modulus n := by exact_mod_cast (show 8 ≤ modulus n by omega)
        omega
  subst hb01
  set q : ℤ := ((p ^ f : ℕ) : ℤ) with hqdef
  have hq7 : 7 ≤ q := by rw [hqdef]; exact_mod_cast hq
  have hq3 : 3 ≤ q := by omega
  have hqoddZ : Odd q := by rw [hqdef]; exact_mod_cast hqodd
  obtain ⟨hconic, -, hQrel⟩ := type_star_signed_degree_relations q e he k hK2 a₀ a₁ a₂ a₃ ha₀
    ha₁ ha₂ ha₃ h01 h02 hsum hrec hc₀ hc₃
  obtain ⟨hconicb, -, hQrelb⟩ := type_star_signed_degree_relations q e he k hK2 1 b₁ b₂ b₃ hb₀
    hb₁ hb₂ hb₃ h01b h02b hsumb hrecb hc₀b hc₃b
  have hmom := typeStar_cubic_moment fS hn ht hindex θ hθS hθT basis ideal normalizerBasis
    lambdaLabel hlambda B hB
  rw [hSa, hSb] at hmom
  have heC : (e : ℂ) = 1 ∨ (e : ℂ) = -1 := by
    rcases he with h | h <;> rw [h] <;> norm_num
  have hqC : ((p ^ f : ℕ) : ℂ) = (q : ℂ) := by rw [hqdef, Int.cast_natCast]
  have hq1C : (q : ℂ) ^ 2 ≠ 1 := by
    intro h
    have h' : q ^ 2 = 1 := by exact_mod_cast h
    nlinarith
  have hqeC : (q : ℂ) + e ≠ 0 := by
    intro h
    have h' : q + e = 0 := by exact_mod_cast h
    rcases he with rfl | rfl <;> omega
  have hfa := cubic_moment_formula (q := (q : ℂ)) (e := (e : ℂ)) (a₀ := (a₀ : ℂ))
    (a₁ := (a₁ : ℂ)) (a₂ := (a₂ : ℂ)) (a₃ := (a₃ : ℂ)) heC hq1C hqeC (by exact_mod_cast ha₀)
    (by exact_mod_cast ha₁) (by exact_mod_cast h01) (by exact_mod_cast hsum)
    (by exact_mod_cast hconic)
  have hfb := cubic_moment_formula (q := (q : ℂ)) (e := (e : ℂ)) (a₀ := (1 : ℂ))
    (a₁ := (b₁ : ℂ)) (a₂ := (b₂ : ℂ)) (a₃ := (b₃ : ℂ)) heC hq1C hqeC one_ne_zero
    (by exact_mod_cast hb₁) (by exact_mod_cast h01b) (by exact_mod_cast hsumb)
    (by exact_mod_cast hconicb)
  rw [hqC] at hmom
  push_cast at hmom
  rw [hfa, hfb] at hmom
  have hfac : (4 : ℂ) * q / (q + e) ≠ 0 := by
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    exact div_ne_zero (mul_ne_zero (by norm_num) hq0) hqeC
  have hQ₁C := mul_left_cancel₀ hfac hmom
  have hQ₁ : ((a₁ - e * q * a₀) ^ 2 / (a₀ * a₁ * (a₀ + a₁)) : ℚ) =
      ((b₁ - e * q * 1) ^ 2 / (1 * b₁ * (1 + b₁)) : ℚ) := by
    have h : (((a₁ - e * q * a₀) ^ 2 / (a₀ * a₁ * (a₀ + a₁)) : ℚ) : ℂ) =
        (((b₁ - e * q * 1) ^ 2 / (1 * b₁ * (1 + b₁)) : ℚ) : ℂ) := by
      push_cast
      exact hQ₁C
    exact_mod_cast h
  have hqeQ : (q : ℚ) + e ≠ 0 := by
    intro h
    have h' : q + e = 0 := by exact_mod_cast h
    rcases he with rfl | rfl <;> omega
  have hQ₂ : ((a₂ + e * q * a₀) ^ 2 / (a₀ * a₂ * (a₀ + a₂)) : ℚ) =
      ((b₂ + e * q * 1) ^ 2 / (1 * b₂ * (1 + b₂)) : ℚ) := by
    apply mul_right_cancel₀ hqeQ
    simp only [Int.cast_one] at hQrelb
    rw [← hQrel, ← hQrelb, hQ₁]
  have hqe' : e * q - 1 ≡ 2 * k [ZMOD 4 * k] := hqe
  obtain ⟨hB₁, hB₂⟩ := principal_quotient_bounds p hp hpodd f hf q (by rw [hqdef]; push_cast; rfl)
    hq7 e he k hK2 hkpow hqe' b₁ b₂ b₃
    (one_lt_abs_of_signed_degree_congruences hK2 hqe' hb₁ (Or.inl hc₁b))
    (one_lt_abs_of_signed_degree_congruences hK2 hqe' hb₂ (Or.inr (Or.inl hc₂b)))
    (one_lt_abs_of_signed_degree_congruences hK2 hqe' hb₃ (Or.inr (Or.inr hc₃b)))
    hsumb (by linear_combination hconicb) hc₁b hc₂b hc₃b
  have ha01 : a₀ = 1 := type_star_degree_one q hq3 hqoddZ e he k hK2 hkpow hqe' a₀ a₁ a₂ a₃ ha₀
    ha₁ ha₂ ha₃ h01 h02 hsum hrec hc₀ hc₁ hc₂ hc₃
    (by rw [hQ₁]; simpa using hB₁) (by rw [hQ₂]; simpa using hB₂)
  obtain ⟨hdeg, hval⟩ := hext ha01
  exact extends_of_degree_one fS hn ht hindex θ hθS basis c₀ hdeg hval

theorem simple_centralizer_linear_character_trivial
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hLnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 7 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (θ : C t →* ℂˣ) (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c) :
    ∀ c : C t, θ c = 1 := by
  have hindex : ∀ V : Subgroup G, V.index ≠ 2 := by
    intro V h2
    have hN : V.Normal := Subgroup.normal_of_index_eq_two h2
    rcases hN.eq_bot_or_eq_top with hb | htop
    · subst hb
      rw [Subgroup.index_bot] at h2
      obtain ⟨a, b, hab⟩ := hGnonab
      have hc : IsCyclic G := isCyclic_of_prime_card (p := 2) (by rw [h2])
      exact hab (hc.commGroup.mul_comm a b)
    · subst htop
      rw [Subgroup.index_top] at h2
      omega
  obtain ⟨lam, hlam⟩ := centralizer_linear_character_extends G hindex n hn S fS t ht hLnonab
    hcentral hnc p f hp hpodd hf hq hmodel θ hθS hθT
  have hker : lam.ker = ⊤ := by
    rcases (MonoidHom.normal_ker lam).eq_bot_or_eq_top with hb | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hGnonab
      apply hab
      apply (MonoidHom.ker_eq_bot_iff lam).mp hb
      rw [map_mul, map_mul, mul_comm]
    · exact htop
  intro c
  rw [← hlam c]
  exact MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top _)

theorem field_factor_one
    : SimpleLayerFrontier.FieldFactorOneStatement :=
  field_factor_one_of_trivial fun G _ _ _ => simple_centralizer_linear_character_trivial G

end CFSG.Semidihedral.FieldFactorOne
