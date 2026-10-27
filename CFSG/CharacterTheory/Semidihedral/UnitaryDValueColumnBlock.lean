module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueBrauer
public import CFSG.CharacterTheory.Wreathed.CoprimeClassUnitRatio

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.UnitaryDValue.Columns

open CFSG.TwoRankLowerBound.Helpers

theorem exists_maximal_ideal_residue_three :
    ∃ ideal : Ideal ComplexAlgebraicIntegers, ideal.IsMaximal ∧
      CharP (ComplexAlgebraicIntegers ⧸ ideal) 3 := by
  obtain ⟨⟨m, hm, h3⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 3 Nat.prime_three
  exact ⟨m, hm, hchar m hm h3⟩

theorem exists_principal_label {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    ∃ label : basis.index, (basis.representation label).character = 1 := by
  obtain ⟨label, hlabel⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  exact ⟨label, hlabel.trans (principalFiniteComplexRepresentation_character G)⟩

theorem principal_column_norm {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (u : G) (e : ℕ) (hu : orderOf u ∣ prime ^ e) (h : ℕ)
    (hsyl : (Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G))).factorization prime =
      h)
    (hcompl : ∃ (K : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
      (_ : K.Normal), Nat.Coprime prime (Nat.card K) ∧
        IsPGroup prime (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ K)) :
    ∑ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation c).character u * (basis.representation c).character u⁻¹ =
        (prime : ℂ) ^ h := by
  obtain ⟨K, hKn, hcop, hquot⟩ := hcompl
  obtain ⟨localBasis⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer (Subgroup.zpowers u : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := exists_principal_label localBasis
  obtain ⟨h1, h2, h3⟩ :=
    CFSG.RankTwoShapes.principal_primary_column_centralizer_norm_of_normal_complement basis
      ideal prime principal hprincipal u e hu localBasis localPrincipal hlocalPrincipal K hcop
      hquot
  obtain ⟨S⟩ :=
    (inferInstance : Nonempty (Sylow prime (Subgroup.centralizer (Subgroup.zpowers u : Set G))))
  have hS : Nat.card S = prime ^ h := by rw [Sylow.card_eq_multiplicity, hsyl]
  have hconj : ∀ c, (basis.representation c).character u⁻¹ =
      starRingEnd ℂ ((basis.representation c).character u) := fun c =>
    (finite_character_conjugate_inverse _ u).symm
  simp only [hconj]
  rw [h1, h2, h3 S, hS]
  push_cast
  rfl

theorem block_column_orthogonal {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (label : basis.index)
    (u u' : G) (e e' : ℕ) (hu : orderOf u ∣ prime ^ e) (hu' : orderOf u' ∣ prime ^ e')
    (hnot : ¬ IsConj u u') :
    ∑ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      (basis.representation c).character u * (basis.representation c).character u'⁻¹ = 0 := by
  have h := coefficientBlock_section_column_orthogonality basis ideal prime label u u' 1 1 e e'
    hu hu' (by simp) (by simp) (Commute.one_right u) (Commute.one_right u') hnot
  simpa only [mul_one] using h

theorem odd_orderOf_of_isConj {G : Type*} [Group G] [Finite G] {v a b : G}
    (hcent : Odd (Nat.card (Subgroup.centralizer (Subgroup.zpowers v : Set G))))
    (hab : Commute a b) (hconj : IsConj v a) : Odd (orderOf (a * b)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  set y := c⁻¹ * (a * b) * c with hy
  have hva : v = c⁻¹ * a * c := by rw [← hc]; group
  have hcomm : Commute v y := by
    change v * y = y * v
    rw [hva, hy]
    have hab' : a * b = b * a := hab.eq
    calc c⁻¹ * a * c * (c⁻¹ * (a * b) * c) = c⁻¹ * (a * (a * b)) * c := by group
      _ = c⁻¹ * (a * (b * a)) * c := by rw [hab']
      _ = c⁻¹ * (a * b * a) * c := by group
      _ = c⁻¹ * (a * b) * c * (c⁻¹ * a * c) := by group
  have hmem : y ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hcomm.zpow_left k).eq
  have hodd : Odd (orderOf y) :=
    Odd.of_dvd_nat hcent (Subgroup.orderOf_dvd_natCard _ hmem)
  have horder : orderOf y = orderOf (a * b) := by
    have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective (a * b)
    rw [← this, hy]
    simp
  rwa [← horder]

theorem mem_block_and_eq_neg_one {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (χ₁ ψ : basis.index)
    (hψ : ψ ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hodd : ∀ g : G, Odd (orderOf g) →
      (basis.representation ψ).character g = (basis.representation χ₁).character g + 1)
    (v : G) (e : ℕ) (hv : orderOf v ∣ prime ^ e)
    (hcent : Odd (Nat.card (Subgroup.centralizer (Subgroup.zpowers v : Set G)))) :
    χ₁ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      (basis.representation χ₁).character v = -1 := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set χ : basis.index → G → ℂ := fun c => (basis.representation c).character with hχ
  set θ : G → ℂ := fun g => χ ψ g - χ χ₁ g - 1 with hθ
  have hterm : ∀ g : G, θ g * ∑ c ∈ B, χ c v * χ c g⁻¹ = 0 := by
    intro g
    obtain ⟨a, b, n, -, -, hab, hg, ha, hb⟩ :=
      finite_prime_primary_factorization g prime Fact.out
    by_cases hconj : IsConj v a
    · have hgodd : Odd (orderOf g) := hg ▸ odd_orderOf_of_isConj hcent hab hconj
      have hθg : θ g = 0 := by
        simp only [hθ, hχ, hodd g hgodd]
        ring
      rw [hθg, zero_mul]
    · have h0 := coefficientBlock_section_column_orthogonality basis ideal prime principal v a 1 b
        e n hv ha (by simp) hb (Commute.one_right v) hab hconj
      rw [mul_one, hg] at h0
      rw [h0, mul_zero]
  have hsum : ∑ g : G, θ g * ∑ c ∈ B, χ c v * χ c g⁻¹ = 0 :=
    Finset.sum_eq_zero fun g _ => hterm g
  have hswap : ∑ g : G, θ g * ∑ c ∈ B, χ c v * χ c g⁻¹ =
      (Nat.card G : ℂ) * ∑ c ∈ B, characterPairing θ (χ c) * χ c v := by
    have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hc : ∀ c, (Nat.card G : ℂ) * (characterPairing θ (χ c) * χ c v) =
        ∑ g : G, θ g * (χ c v * χ c g⁻¹) := by
      intro c
      rw [characterPairing, mul_assoc, ← mul_assoc (Nat.card G : ℂ), mul_inv_cancel₀ hG, one_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun g _ => by ring
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => (hc c).symm
  have hbasis : ∀ c d : basis.index, characterPairing (χ c) (χ d) = if c = d then 1 else 0 := by
    intro c d
    rw [characterPairing_irreducible _ _ (basis.irreducible c) (basis.irreducible d)]
    simp only [basis.distinct.eq_iff]
  have hθeq : θ = χ ψ - χ χ₁ - χ principal := by
    funext g
    simp only [hθ, hχ, hprincipal, Pi.sub_apply, Pi.one_apply]
  have hpair : ∀ c, characterPairing θ (χ c) * χ c v =
      (if ψ = c then χ c v else 0) - (if χ₁ = c then χ c v else 0) -
        (if principal = c then χ c v else 0) := by
    intro c
    rw [hθeq, characterPairing_sub_left, characterPairing_sub_left, hbasis, hbasis, hbasis]
    split_ifs <;> ring
  simp_rw [hpair] at hswap
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
    Finset.sum_ite_eq, ite_eq_right hψ, ite_eq_left (coefficientBlock_self_mem _ _ _)] at hswap
  have hmain : (if χ₁ ∈ B then χ χ₁ v else 0) = -1 := by
    have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have h1 : χ principal v = 1 := by simp only [hχ, hprincipal, Pi.one_apply]
    rw [h1] at hswap
    have := hsum.symm.trans hswap
    have h2 : (0 : ℂ) - (if χ₁ ∈ B then χ χ₁ v else 0) - 1 = 0 :=
      (mul_eq_zero.mp this.symm).resolve_left hG
    linear_combination -h2
  by_cases hmem : χ₁ ∈ B
  · rw [ite_eq_left hmem] at hmain
    exact ⟨hmem, hmain⟩
  · rw [ite_eq_right hmem] at hmain
    norm_num at hmain

end CFSG.Semidihedral.UnitaryDValue.Columns

namespace CFSG.Semidihedral.UnitaryDValue.DValueData

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem index_N :
    (Subgroup.centralizer ({D.x} : Set G)).index = D.q ^ 2 * (D.q ^ 2 - D.q + 1) := by
  have h := (Subgroup.centralizer ({D.x} : Set G)).card_mul_index
  have hcardN := D.card_N
  have hcardG := D.card_G_eq
  change Nat.card (Subgroup.centralizer ({D.x} : Set G)) =
    D.m * Nat.card D.A * (D.q * (D.q ^ 2 - 1)) at hcardN
  rw [hcardN, hcardG] at h
  have hq := D.seven_le_q
  have hsq : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    have h1 : 1 ≤ D.q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, show 1 ≤ D.q by omega]
    ring
  rw [hsq] at h
  have hpos : 0 < D.m * Nat.card D.A * (D.q * ((D.q - 1) * (D.q + 1))) :=
    Nat.mul_pos (Nat.mul_pos D.m_pos D.card_A_pos)
      (Nat.mul_pos D.q_pos (Nat.mul_pos (by omega) (by omega)))
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h]
  ring

theorem not_mem_principal_block (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 3]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (h3 : 3 ∣ D.q + 1) (ψ : basis.index)
    (hψdeg : Module.finrank ℂ (basis.representation ψ).vector = D.q ^ 3 + 1)
    (hψx : (basis.representation ψ).character D.x = (D.q : ℂ) + 1 ∨
      (basis.representation ψ).character D.x = -((D.q : ℂ) + 1)) :
    ψ ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
  intro hψ
  set k := (Subgroup.centralizer ({D.x} : Set G)).index with hk
  set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk D.x)
    with hv
  have hsame : centralCharacterResidueHom basis ideal ψ =
      centralCharacterResidueHom basis ideal principal :=
    (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal ψ principal).mp
      (sameCoefficientBlock_symm basis _ ((coefficientBlock_mem_iff _ _ _ _).mp hψ))
  have hval : ∀ label, (localCentralCharacterHom basis ideal label v : ℂ) =
      (k : ℂ) * (basis.representation label).character D.x /
        (basis.representation label).character 1 := fun label =>
    CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis D.x label
  have hprin : localCentralCharacterHom basis ideal principal v =
      (k : localizedComplexIntegerRing ideal) := by
    apply Subtype.ext
    rw [hval, hprincipal]
    simp
  have hcube : (D.q : ℂ) ^ 3 + 1 = ((D.q : ℂ) + 1) * ((D.q ^ 2 - D.q + 1 : ℕ) : ℂ) := by
    exact_mod_cast D.cube_add_one_eq
  have hψ1 : (basis.representation ψ).character 1 = (D.q : ℂ) ^ 3 + 1 := by
    rw [FiniteComplexRepresentation.character, Representation.char_one, hψdeg]
    push_cast
    ring
  have hkval : (k : ℂ) = (D.q : ℂ) ^ 2 * ((D.q ^ 2 - D.q + 1 : ℕ) : ℂ) := by
    rw [hk, D.index_N]
    push_cast
    ring
  have hq1 : (D.q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero D.q
  have hQ : ((D.q ^ 2 - D.q + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast D.Q_pos.ne'
  obtain ⟨ε, hε, hεval⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (localCentralCharacterHom basis ideal ψ v : ℂ) = (ε : ℂ) * (D.q : ℂ) ^ 2 := by
    rw [hval, hψ1, hcube, hkval]
    rcases hψx with hx | hx
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [hx]
      field_simp
      push_cast
      ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [hx]
      field_simp
      push_cast
      ring
  have heq : localCentralCharacterHom basis ideal ψ v =
      ((ε * (D.q : ℤ) ^ 2 : ℤ) : localizedComplexIntegerRing ideal) := by
    apply Subtype.ext
    rw [hεval]
    push_cast
    rfl
  have hres := congrArg (fun f => f v) hsame
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal ψ v) =
    localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal v)
    at hres
  have hk3 : 3 ∣ k := by
    rw [hk, D.index_N]
    have h1 := D.three_factorization_Q h3
    have h2 : 3 ∣ D.q ^ 2 - D.q + 1 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three D.Q_pos.ne').mpr (by omega)
    exact Dvd.dvd.mul_left h2 _
  rw [hprin, heq, localizedComplexIntegerResidue_integer, map_natCast,
    (CharP.cast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) 3 k).mpr hk3,
    CharP.intCast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) 3] at hres
  have hq3 : ¬ 3 ∣ D.q := D.not_dvd_q_of_dvd Nat.prime_three h3
  apply hq3
  have hdvd : (3 : ℤ) ∣ (D.q : ℤ) ^ 2 := by
    rcases hε with rfl | rfl
    · simpa using hres
    · simpa using hres
  have hdvd' : 3 ∣ D.q ^ 2 := by exact_mod_cast hdvd
  exact Nat.prime_three.dvd_of_dvd_pow hdvd'

end CFSG.Semidihedral.UnitaryDValue.DValueData
