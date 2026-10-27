module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.PrincipalNonvanishing

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem centralCharacterScalar_conjugacyClassSum_mk (basis : FiniteIrreducibleCharacterBasis G)
    (g : G) (label : basis.index) :
    centralCharacterScalar basis (conjugacyClassSum (ConjClasses.mk g)) label =
      ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * (basis.representation label).character g /
        (basis.representation label).character 1 := by
  rw [CFSG.LyonsUnitaryFour.centralCharacterScalar_conjugacyClassSum]
  congr 1
  have hterm : ∀ h : G, (if ConjClasses.mk h = ConjClasses.mk g then
      (basis.representation label).character h else 0) =
      (if ConjClasses.mk h = ConjClasses.mk g then (1 : ℂ) else 0) *
        (basis.representation label).character g := by
    intro h
    split_ifs with hh
    · obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hh)
      rw [one_mul, ← hc]
      exact (Representation.char_conj _ h c).symm
    · rw [zero_mul]
  rw [Finset.sum_congr rfl fun h _ => hterm h, ← Finset.sum_mul]
  congr 1
  rw [← CFSG.LyonsUnitaryFour.card_conjClass_eq_index, Finset.sum_boole]
  congr 1
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1
  ext h
  simp [ConjClasses.mem_carrier_iff_mk_eq]

theorem padicValNat_eq_of_residue_ne_zero (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    {x : localizedComplexIntegerRing ideal} (hx : localizedComplexIntegerResidue ideal x ≠ 0)
    {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (h : (x : ℂ) * M = N) :
    padicValNat p N = padicValNat p M := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨u, hu⟩ := pow_padicValNat_dvd (p := p) (n := N)
  obtain ⟨w, hw⟩ := pow_padicValNat_dvd (p := p) (n := M)
  have hu' : ¬ p ∣ u := fun hd => pow_succ_padicValNat_not_dvd hN (by
    rw [pow_succ]
    nth_rw 2 [hu]
    exact mul_dvd_mul_left _ hd)
  have hw' : ¬ p ∣ w := fun hd => pow_succ_padicValNat_not_dvd hM (by
    rw [pow_succ]
    nth_rw 2 [hw]
    exact mul_dvd_mul_left _ hd)
  have hres : ∀ t : ℕ, localizedComplexIntegerResidue ideal (t : localizedComplexIntegerRing ideal)
      = 0 ↔ p ∣ t := fun t => by
    rw [map_natCast]
    exact CharP.cast_eq_zero_iff _ p t
  have hresp : localizedComplexIntegerResidue ideal (p : localizedComplexIntegerRing ideal) = 0 :=
    (hres p).mpr dvd_rfl
  have hMN : (x : ℂ) * ((p : ℂ) ^ padicValNat p M * w) = (p : ℂ) ^ padicValNat p N * u := by
    have e := h
    rw [hw, hu] at e
    push_cast at e
    exact e
  rcases lt_trichotomy (padicValNat p N) (padicValNat p M) with hlt | heq | hgt
  · exfalso
    obtain ⟨e, he⟩ : ∃ e, padicValNat p M = padicValNat p N + e + 1 :=
      ⟨padicValNat p M - padicValNat p N - 1, by omega⟩
    have hO : x * (p : localizedComplexIntegerRing ideal) ^ (e + 1) * w = u := by
      apply Subtype.ext
      push_cast
      apply mul_left_cancel₀ (pow_ne_zero (padicValNat p N) hp0)
      rw [← hMN, he]
      ring
    have e' := congrArg (localizedComplexIntegerResidue ideal) hO
    rw [map_mul, map_mul, map_pow, hresp, zero_pow (Nat.succ_ne_zero e), mul_zero, zero_mul] at e'
    exact hu' ((hres u).mp e'.symm)
  · exact heq
  · exfalso
    obtain ⟨e, he⟩ : ∃ e, padicValNat p N = padicValNat p M + e + 1 :=
      ⟨padicValNat p N - padicValNat p M - 1, by omega⟩
    have hO : x * w = (p : localizedComplexIntegerRing ideal) ^ (e + 1) * u := by
      apply Subtype.ext
      push_cast
      apply mul_left_cancel₀ (pow_ne_zero (padicValNat p M) hp0)
      calc (p : ℂ) ^ padicValNat p M * ((x : ℂ) * w)
          = (x : ℂ) * ((p : ℂ) ^ padicValNat p M * w) := by ring
        _ = (p : ℂ) ^ padicValNat p N * u := hMN
        _ = (p : ℂ) ^ padicValNat p M * ((p : ℂ) ^ (e + 1) * u) := by rw [he]; ring
    have e' := congrArg (localizedComplexIntegerResidue ideal) hO
    rw [map_mul, map_mul, map_pow, hresp, zero_pow (Nat.succ_ne_zero e), zero_mul] at e'
    exact hw' ((hres w).mp ((mul_eq_zero.mp e').resolve_left hx))

theorem principal_block_coprime_class_size_character_unit_ratio
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (g : G) (hg : ¬ p ∣ (Subgroup.centralizer ({g} : Set G)).index) (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    (∃ u : localizedComplexIntegerRing ideal,
      (u : ℂ) = (basis.representation χ).character g / (basis.representation χ).character 1 ∧
        localizedComplexIntegerResidue ideal u = 1 ∧ IsUnit u) ∧
      (basis.representation χ).character g ≠ 0 ∧
      ∀ (n : ℤ) (m : ℕ), (basis.representation χ).character g = n →
        (basis.representation χ).character 1 = m → padicValNat p m = padicValNat p n.natAbs := by
  set k := (Subgroup.centralizer ({g} : Set G)).index with hk
  set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk g)
  have hsame : centralCharacterResidueHom basis ideal χ =
      centralCharacterResidueHom basis ideal principal :=
    (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal χ principal).mp
      (sameCoefficientBlock_symm basis _ ((coefficientBlock_mem_iff _ _ _ _).mp hχ))
  have hval : ∀ label, (localCentralCharacterHom basis ideal label v : ℂ) =
      (k : ℂ) * (basis.representation label).character g /
        (basis.representation label).character 1 := fun label =>
    centralCharacterScalar_conjugacyClassSum_mk basis g label
  have hprin : localCentralCharacterHom basis ideal principal v =
      (k : localizedComplexIntegerRing ideal) := by
    apply Subtype.ext
    rw [hval, hprincipal]
    simp
  have hkunit : IsUnit (k : localizedComplexIntegerRing ideal) := by
    have e := (localizedComplexInteger_integer_unit_iff ideal p (k : ℤ)).mpr
      (fun hd => hg (Int.natCast_dvd_natCast.mp hd))
    rwa [Int.cast_natCast] at e
  obtain ⟨c, hc⟩ := hkunit
  set q : localizedComplexIntegerRing ideal := ↑c⁻¹ * localCentralCharacterHom basis ideal χ v
    with hqdef
  have hk0 : (k : ℂ) ≠ 0 := by
    rw [hk]
    exact_mod_cast (Subgroup.centralizer ({g} : Set G)).index_ne_zero_of_finite
  have hcinv : ((↑c⁻¹ : localizedComplexIntegerRing ideal) : ℂ) = (k : ℂ)⁻¹ := by
    have e : ((↑c⁻¹ : localizedComplexIntegerRing ideal) : ℂ) * (k : ℂ) = 1 := by
      have e' : ((↑c⁻¹ * ↑c : localizedComplexIntegerRing ideal) : ℂ) = 1 := by
        rw [Units.inv_mul]
        rfl
      rw [Subring.coe_mul, hc] at e'
      exact_mod_cast e'
    exact eq_inv_of_mul_eq_one_left e
  have hq : (q : ℂ) = (basis.representation χ).character g /
      (basis.representation χ).character 1 := by
    rw [hqdef, Subring.coe_mul, hcinv, hval]
    field_simp
  have hres : localizedComplexIntegerResidue ideal q = 1 := by
    have e : localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ v) =
        localizedComplexIntegerResidue ideal (k : localizedComplexIntegerRing ideal) := by
      have e' := congrArg (fun f => f v) hsame
      change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ v) =
        localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal v)
        at e'
      rw [e', hprin]
    rw [hqdef, map_mul, e, ← hc, ← map_mul, Units.inv_mul, map_one]
  have hunit : IsUnit q :=
    (localizedComplexIntegerResidue_isUnit_iff ideal q).mpr (by rw [hres]; exact one_ne_zero)
  have hne : (basis.representation χ).character g ≠ 0 := by
    intro h0
    have hq0 : q = 0 := Subtype.ext (by rw [hq, h0, zero_div]; rfl)
    rw [hq0, map_zero] at hres
    exact zero_ne_one hres
  refine ⟨⟨q, hq, hres, hunit⟩, hne, fun n m hn hm => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    have hq0 : q = 0 := Subtype.ext (by rw [hq, hm, Nat.cast_zero, div_zero]; rfl)
    rw [hq0, map_zero] at hres
    exact zero_ne_one hres
  have hn0 : n.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    rintro rfl
    exact hne (by rw [hn, Int.cast_zero])
  have hqm : (q : ℂ) * m = n := by
    rw [hq, hn, hm]
    field_simp
  rcases Int.natAbs_eq n with hpos | hneg
  · refine (padicValNat_eq_of_residue_ne_zero ideal p (x := q)
      (by rw [hres]; exact one_ne_zero) hm0 hn0 ?_).symm
    rw [hqm]
    conv_lhs => rw [hpos]
    rw [Int.cast_natCast]
  · refine (padicValNat_eq_of_residue_ne_zero ideal p (x := -q)
      (by rw [map_neg, hres]; exact neg_ne_zero.mpr one_ne_zero) hm0 hn0 ?_).symm
    rw [Subring.coe_neg, neg_mul, hqm]
    conv_lhs => rw [hneg]
    rw [Int.cast_neg, Int.cast_natCast, neg_neg]

theorem principal_block_character_unit_ratio_of_centralizes_sylow
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow p G) (g : G) (hg : g ∈ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    (∃ u : localizedComplexIntegerRing ideal,
      (u : ℂ) = (basis.representation χ).character g / (basis.representation χ).character 1 ∧
        localizedComplexIntegerResidue ideal u = 1 ∧ IsUnit u) ∧
      (basis.representation χ).character g ≠ 0 ∧
      ∀ (n : ℤ) (m : ℕ), (basis.representation χ).character g = n →
        (basis.representation χ).character 1 = m → padicValNat p m = padicValNat p n.natAbs := by
  refine principal_block_coprime_class_size_character_unit_ratio basis ideal p principal
    hprincipal g ?_ χ hχ
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({g} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hg) s hs
  intro hdvd
  exact P.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hle))

theorem principal_block_character_unit_ratio_of_mem_center_sylow
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow p G) (g : G)
    (hg : g ∈ (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    (∃ u : localizedComplexIntegerRing ideal,
      (u : ℂ) = (basis.representation χ).character g / (basis.representation χ).character 1 ∧
        localizedComplexIntegerResidue ideal u = 1 ∧ IsUnit u) ∧
      (basis.representation χ).character g ≠ 0 ∧
      ∀ (n : ℤ) (m : ℕ), (basis.representation χ).character g = n →
        (basis.representation χ).character 1 = m → padicValNat p m = padicValNat p n.natAbs := by
  refine principal_block_character_unit_ratio_of_centralizes_sylow basis ideal p principal
    hprincipal P g ?_ χ hχ
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have e := (Subgroup.mem_center_iff.mp hz) ⟨s, hs⟩
  exact congrArg Subtype.val e

end CFSG.Wreathed
