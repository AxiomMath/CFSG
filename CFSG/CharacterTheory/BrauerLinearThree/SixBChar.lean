module

public import CFSG.CharacterTheory.BrauerLinearThree.LayerOrder

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers

theorem card_centralizer_mul_dvd_of_character_eq_neg_one {X : Type} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (χ : basis.index) (x : X)
    (hx : (basis.representation χ).character x = -1) :
    Nat.card (Subgroup.centralizer ({x} : Set X)) *
      Module.finrank ℂ (basis.representation χ).vector ∣ Nat.card X := by
  set d := Module.finrank ℂ (basis.representation χ).vector
  set m := (Subgroup.centralizer ({x} : Set X)).index
  have hint := centralCharacterScalar_conjugacyClassSum_integral basis (ConjClasses.mk x) χ
  have hdeg : (basis.representation χ).character 1 = (d : ℂ) := Representation.char_one _
  rw [CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk, hx, hdeg] at hint
  have hd0 : (d : ℂ) ≠ 0 := by
    rw [← hdeg]
    exact irreducible_character_degree_ne_zero _ (basis.irreducible χ)
  have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast (by exact_mod_cast hd0 : (d : ℕ) ≠ 0)
  have hrat : IsIntegral ℤ (-(m : ℚ) / d) :=
    IsIntegral.tower_bot_of_field (B := ℂ) (by
      have e : (algebraMap ℚ ℂ) (-(m : ℚ) / d) = (m : ℂ) * -1 / d := by
        push_cast
        ring
      rw [e]
      exact hint)
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrat
  change (k : ℚ) = _ at hk
  have hmk : (m : ℤ) = -k * d := by
    have h : (m : ℚ) = -k * d := by
      rw [hk]
      field_simp
    exact_mod_cast h
  have hdvd : d ∣ m := by
    have : (d : ℤ) ∣ (m : ℤ) := ⟨-k, by rw [hmk]; ring⟩
    exact_mod_cast this
  calc Nat.card (Subgroup.centralizer ({x} : Set X)) * d ∣
      Nat.card (Subgroup.centralizer ({x} : Set X)) * m := Nat.mul_dvd_mul_left _ hdvd
    _ = Nat.card X := by rw [mul_comm]; exact Subgroup.index_mul_card _

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem exists_principal_characters
    [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    (basis : FiniteIrreducibleCharacterBasis G) :
    ∃ χ₁ ν₀ : basis.index, Module.finrank ℂ (basis.representation χ₁).vector = Nat.card F ^ 3 ∧
      Module.finrank ℂ (basis.representation ν₀).vector = Nat.card F ^ 3 - 1 ∧
      ∀ x : G, Odd (orderOf x) →
        (basis.representation ν₀).character x = (basis.representation χ₁).character x - 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have hqodd := odd_card_F h2
      rw [hF, h] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
    · exact h
  obtain ⟨hs, hnab, hcen, hnc, hmodel⟩ :=
    layer_hypotheses φ hZ hZodd h2 hJ hq p f hp hf hF (by omega)
  have := hs
  obtain ⟨hn4, S, e', he'r, he's⟩ := exists_semidihedral_sylow_of_G φ hZ hZodd h2 hJ hq
  obtain ⟨principal, hprincipal⟩ :=
    CFSG.Semidihedral.Principal.finiteIrreducibleCharacterBasis_exists_principal_label basis
  obtain ⟨localBasis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer ({J} : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    CFSG.Semidihedral.Principal.finiteIrreducibleCharacterBasis_exists_principal_label localBasis
  obtain ⟨⟨ideal, hmax, h2mem⟩, hchar⟩ :=
    CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2mem
  obtain ⟨hvc, hvd⟩ := padicValNat_centralizers φ hZ hZodd h2 p f hp hF
  have hvG : padicValNat p (Nat.card G) = 3 * f := by
    have hcop := coprime_facts hZ
    have hpc : ringChar F = p := by
      have hrc : (ringChar F).Prime := CharP.char_is_prime F _
      obtain ⟨f', hf', hq'⟩ := exists_card_eq_ringChar_pow F
      have hdvd : ringChar F ∣ p ^ f := by
        rw [← hF, hq']
        exact dvd_pow_self _ hf'.ne'
      exact (Nat.prime_dvd_prime_iff_eq hrc hp).mp (hrc.dvd_of_dvd_pow hdvd)
    rw [hpc] at hcop
    have h1 : padicValNat p (Nat.card G * Nat.card Z) = padicValNat p (Nat.card G) := by
      rw [padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne',
        padicValNat.eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop.1), add_zero]
    have hq1 : 1 < Nat.card F := by omega
    have e1 : padicValNat p (Nat.card F ^ 3) = 3 * f := by
      rw [hF, ← pow_mul, padicValNat.prime_pow]
      ring
    have e2 : padicValNat p ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) = 0 :=
      padicValNat.eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop.2.2)
    have hne : (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) ≠ 0 := by
      have h3' : 1 < Nat.card F ^ 3 := Nat.one_lt_pow (by norm_num) hq1
      have h2' : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) hq1
      exact Nat.mul_ne_zero (by omega) (by omega)
    have h3 : padicValNat p (Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) =
        3 * f := by
      rw [mul_assoc, padicValNat.mul (by positivity) hne, e1, e2, add_zero]
    rw [← h1, hcard, h3]
  have hval : 3 * (padicValNat p (Nat.card (Subgroup.centralizer ({J} : Set G))) : ℤ) -
      2 * (padicValNat p (Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({(e' (CFSG.Semidihedral.s _) : G)} : Set G) : Subgroup G)) : ℤ) ≤
      padicValNat p (Nat.card G) := by
    rw [he's, hvc, hvd, hvG]
    push_cast
    omega
  obtain ⟨F', _, _, ρ, hF', -, -, -, hrest⟩ :=
    CFSG.Semidihedral.Principal.actual_simple_layer_characteristic_valuation_degree_formulas
      hnonab _ hn4 S e' J hJ hnab hcen hnc p f hp hpodd hf hmodel ideal basis principal
      hprincipal localBasis localPrincipal hlocalPrincipal e' he'r hval
  obtain ⟨-, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, -, hvals⟩ := hrest
  obtain ⟨hδ₁, -, -, -, hχ₁, -, -, -, -, hν1, -, -⟩ := hvals
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hodd⟩ := hfam
  have hq' : Nat.card F' = Nat.card F := hF'.trans hF.symm
  have he : (if Nat.card F' % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    rw [hq']
    exact ite_eq_right_iff.mpr (fun h => by omega)
  have hk : 0 ∈ Finset.range (2 ^ ((Nat.card F + 1).factorization 2 + 2 - 3)) := by
    rw [Finset.mem_range]
    positivity
  refine ⟨χ₁, ν 0, ?_, ?_, fun x hx => ?_⟩
  · rw [hq'] at hχ₁
    exact_mod_cast hχ₁
  · have h1 := hν1 0 hk
    rw [he, hq'] at h1
    have hdeg : (basis.representation (ν 0)).character 1 =
        (Module.finrank ℂ (basis.representation (ν 0)).vector : ℂ) := Representation.char_one _
    rw [hdeg] at h1
    have hq3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow _ _ (by omega)
    have : ((Module.finrank ℂ (basis.representation (ν 0)).vector : ℕ) : ℂ) =
        ((Nat.card F ^ 3 - 1 : ℕ) : ℂ) := by
      rw [h1]
      push_cast [Nat.cast_sub hq3]
      ring
    exact_mod_cast this
  · obtain ⟨-, hν, -, -⟩ := hodd x hx
    rw [hν 0 hk, hδ₁, he]
    push_cast
    ring

end CFSG.BrauerLinearThree
