module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.PrincipalNonvanishing
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormOne
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

theorem localizedComplexIntegerResidue_eq_one_of_pow_eq_one
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (ζ : localizedComplexIntegerRing ideal)
    (a : ℕ) (hζ : ζ ^ p ^ a = 1) : localizedComplexIntegerResidue ideal ζ = 1 := by
  have hpow := congrArg (localizedComplexIntegerResidue ideal) hζ
  rw [map_pow, map_one] at hpow
  have hzero : (localizedComplexIntegerResidue ideal ζ - 1) ^ p ^ a = 0 := by
    rw [sub_pow_char_pow, hpow, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero a (Fact.out : p.Prime).ne_zero)).mp hzero)

@[expose] noncomputable def linearTwist {G : Type*} [Group G] (lam : G →* ℂˣ)
    (data : FiniteComplexRepresentation G) : FiniteComplexRepresentation G where
  vector := data.vector
  representation :=
    { toFun := fun w => (lam w : ℂ) • data.representation w
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, Units.val_mul, smul_mul_smul_comm] }

theorem linearTwist_character {G : Type*} [Group G] (lam : G →* ℂˣ)
    (data : FiniteComplexRepresentation G) (w : G) :
    (linearTwist lam data).character w = lam w * data.character w := by
  change LinearMap.trace ℂ data.vector ((lam w : ℂ) • data.representation w) = _
  rw [map_smul, smul_eq_mul]
  rfl

theorem linearTwist_characterPairing {G : Type*} [Group G] [Fintype G] (lam : G →* ℂˣ)
    (data : FiniteComplexRepresentation G) :
    characterPairing (linearTwist lam data).character (linearTwist lam data).character =
      characterPairing data.character data.character := by
  unfold characterPairing
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [linearTwist_character, linearTwist_character]
  have hunit : (lam w : ℂ) * (lam w⁻¹ : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  linear_combination (data.character w * data.character w⁻¹) * hunit

theorem character_mul_of_degree_eq_one {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G)
    (hdegree : data.character 1 = 1) (x y : G) :
    data.character (x * y) = data.character x * data.character y := by
  have hdim : Module.finrank ℂ data.vector = 1 := by
    have h := hdegree
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    exact_mod_cast h
  have hscalar : ∀ g, data.representation g =
      data.character g • (1 : Module.End ℂ data.vector) := by
    intro g
    obtain ⟨c, hc, -⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (data.representation g)
    have htrace : data.character g = c := by
      change LinearMap.trace ℂ _ (data.representation g) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, mul_one]
    rw [hc, htrace]
    rfl
  change LinearMap.trace ℂ data.vector (data.representation (x * y)) = _
  rw [map_mul, hscalar x, hscalar y, smul_mul_smul_comm, one_mul, map_smul, LinearMap.trace_one,
    hdim, Nat.cast_one, smul_eq_mul, mul_one]

variable {G : Type*} [Group G] [Fintype G]

theorem exists_linearTwist_label_mem_coefficientBlock
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (lam : G →* ℂˣ) (a : ℕ) (hlam : ∀ w, lam w ^ p ^ a = 1) (χ : basis.index) :
    ∃ ψ : basis.index,
      (∀ w, (basis.representation ψ).character w = lam w * (basis.representation χ).character w) ∧
        ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) χ := by
  obtain ⟨ψ, hψ⟩ := character_norm_one_basis_character basis
    (linearTwist lam (basis.representation χ))
    (by rw [linearTwist_characterPairing, characterPairing_irreducible _ _ (basis.irreducible χ)
      (basis.irreducible χ), ite_eq_left rfl])
  have hvalue : ∀ w, (basis.representation ψ).character w =
      lam w * (basis.representation χ).character w := fun w => by
    rw [hψ, linearTwist_character]
  refine ⟨ψ, hvalue, ?_⟩
  have hmem : ∀ w, ((lam w : ℂˣ) : ℂ) ∈ localizedComplexIntegerRing ideal := fun w =>
    rootOfUnity_mem_localizedComplexIntegerRing ideal (p ^ a) (pow_pos (Fact.out : p.Prime).pos a)
      _ (by rw [← Units.val_pow_eq_pow_val, hlam w, Units.val_one])
  have hclass : ∀ g c : G, IsConj g c → (lam g : ℂ) = lam c := fun g c hgc => by
    obtain ⟨x, rfl⟩ := isConj_iff.mp hgc
    rw [map_mul, map_mul, map_inv, mul_comm (lam x), mul_inv_cancel_right]
  rw [coefficientBlock_mem_iff, sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
  apply centralCharacterResidueHom_eq_of_class_values
  intro C
  set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) C
  set c := conjugacyClassRepresentative C
  have hscalar : localCentralCharacterHom basis ideal ψ v =
      ⟨(lam c : ℂ), hmem c⟩ * localCentralCharacterHom basis ideal χ v := by
    apply Subtype.ext
    rw [Subring.coe_mul, localCentralCharacterHom_coe, localCentralCharacterHom_coe]
    change centralCharacterScalar basis (conjugacyClassSum C) ψ =
      (lam c : ℂ) * centralCharacterScalar basis (conjugacyClassSum C) χ
    rw [centralCharacterScalar_conjugacyClassSum, centralCharacterScalar_conjugacyClassSum,
      hvalue 1, map_one, Units.val_one, one_mul, mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs with hg
    · rw [hvalue g, hclass g c (ConjClasses.mk_eq_mk_iff_isConj.mp
        (hg.trans (conjugacyClassRepresentative_spec C).symm))]
    · rw [mul_zero]
  have hone : localizedComplexIntegerResidue ideal ⟨(lam c : ℂ), hmem c⟩ = 1 := by
    apply localizedComplexIntegerResidue_eq_one_of_pow_eq_one ideal p _ a
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subring.coe_one, ← Units.val_pow_eq_pow_val, hlam c,
      Units.val_one]
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ v) =
    localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal ψ v)
  rw [hscalar, map_mul, hone, one_mul]

theorem prime_power_linear_twists_preserve_blocks
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (lam : G →* ℂˣ) (a : ℕ) (hlam : ∀ w, lam w ^ p ^ a = 1)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    (∀ χ : basis.index, ∃ ψ : basis.index,
      (∀ w, (basis.representation ψ).character w = lam w * (basis.representation χ).character w) ∧
        ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) χ) ∧
    (∃ ψ : basis.index, (∀ w, (basis.representation ψ).character w = lam w) ∧
      ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
    ∃ σ : basis.index ≃ basis.index,
      (∀ χ w, (basis.representation (σ χ)).character w =
        lam w * (basis.representation χ).character w) ∧
      ∀ χ ψ, σ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) χ ↔
        ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) χ := by
  have htwist := exists_linearTwist_label_mem_coefficientBlock basis ideal p lam a hlam
  have hinv : ∀ w, lam⁻¹ w ^ p ^ a = 1 := fun w => by
    rw [MonoidHom.inv_apply, inv_pow, hlam w, inv_one]
  have htwistInv := exists_linearTwist_label_mem_coefficientBlock basis ideal p lam⁻¹ a hinv
  refine ⟨htwist, ?_, ?_⟩
  · obtain ⟨ψ, hψ, hmem⟩ := htwist principal
    exact ⟨ψ, fun w => by rw [hψ w, hprincipal, Pi.one_apply, mul_one], hmem⟩
  · choose f hf hfmem using htwist
    choose g hg _ using htwistInv
    have hcancel : ∀ w, (lam w : ℂ) * (lam⁻¹ w : ℂ) = 1 ∧ (lam⁻¹ w : ℂ) * (lam w : ℂ) = 1 :=
      fun w => by
        rw [MonoidHom.inv_apply, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
          inv_mul_cancel, Units.val_one]
        exact ⟨rfl, rfl⟩
    have hfg : ∀ χ, f (g χ) = χ := fun χ => basis.distinct (funext fun w => by
      change (basis.representation (f (g χ))).character w = (basis.representation χ).character w
      rw [hf, hg, ← mul_assoc, (hcancel w).1, one_mul])
    have hgf : ∀ χ, g (f χ) = χ := fun χ => basis.distinct (funext fun w => by
      change (basis.representation (g (f χ))).character w = (basis.representation χ).character w
      rw [hg, hf, ← mul_assoc, (hcancel w).2, one_mul])
    refine ⟨⟨f, g, hgf, hfg⟩, hf, fun χ ψ => ?_⟩
    change f ψ ∈ _ ↔ ψ ∈ _
    constructor
    · intro hmem
      rw [← coefficientBlock_eq_of_mem basis _ hmem, coefficientBlock_eq_of_mem basis _ (hfmem ψ)]
      exact coefficientBlock_self_mem basis _ ψ
    · intro hmem
      rw [← coefficientBlock_eq_of_mem basis _ hmem]
      exact hfmem ψ

theorem principal_degree_one_residue_eq_one (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hdegree : (basis.representation χ).character 1 = 1) (P : Sylow p G) (c : G)
    (hc : c ∈ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hmem : (basis.representation χ).character c ∈ localizedComplexIntegerRing ideal) :
    localizedComplexIntegerResidue ideal ⟨_, hmem⟩ = 1 := by
  set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk c)
  have hsame : centralCharacterResidueHom basis ideal χ =
      centralCharacterResidueHom basis ideal principal :=
    (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal χ principal).mp
      (sameCoefficientBlock_symm basis _ ((coefficientBlock_mem_iff _ _ _ _).mp hχ))
  have hclass : (∑ g : G, if ConjClasses.mk g = ConjClasses.mk c then (1 : ℂ) else 0) =
      ((Subgroup.centralizer ({c} : Set G)).index : ℂ) := by
    rw [← card_conjClass_eq_index, Finset.sum_boole]
    congr 1
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 1
    ext g
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  have hprincipalValue : localCentralCharacterHom basis ideal principal v =
      ((Subgroup.centralizer ({c} : Set G)).index : localizedComplexIntegerRing ideal) := by
    apply Subtype.ext
    rw [localCentralCharacterHom_coe]
    change centralCharacterScalar basis (conjugacyClassSum (ConjClasses.mk c)) principal = _
    rw [centralCharacterScalar_conjugacyClassSum, hprincipal]
    simp only [Pi.one_apply, div_one]
    rw [hclass]
    simp
  have hχValue : localCentralCharacterHom basis ideal χ v =
      ((Subgroup.centralizer ({c} : Set G)).index : localizedComplexIntegerRing ideal) *
        ⟨_, hmem⟩ := by
    apply Subtype.ext
    rw [localCentralCharacterHom_coe, Subring.coe_mul]
    change centralCharacterScalar basis (conjugacyClassSum (ConjClasses.mk c)) χ = _
    rw [centralCharacterScalar_conjugacyClassSum, hdegree, div_one]
    have hterm : ∀ g : G, (if ConjClasses.mk g = ConjClasses.mk c then
        (basis.representation χ).character g else 0) =
        (if ConjClasses.mk g = ConjClasses.mk c then (1 : ℂ) else 0) *
          (basis.representation χ).character c := by
      intro g
      split_ifs with hg
      · obtain ⟨x, hx⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hg)
        rw [← hx, one_mul]
        exact (Representation.char_conj (basis.representation χ).representation g x).symm
      · rw [zero_mul]
    rw [Finset.sum_congr rfl fun g _ => hterm g, ← Finset.sum_mul, hclass]
    simp
  have hres := congrArg (fun φ => φ v) hsame
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ v) =
    localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal v) at hres
  rw [hχValue, hprincipalValue, map_mul, map_natCast] at hres
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({c} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hc) s hs)
  have hne : (((Subgroup.centralizer ({c} : Set G)).index : ℕ) :
      ComplexAlgebraicIntegers ⧸ ideal) ≠ 0 := by
    intro hzero
    rw [CharP.cast_eq_zero_iff _ p] at hzero
    exact P.not_dvd_index (hzero.trans (Subgroup.index_dvd_of_le hle))
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  exact mul_left_cancel₀ hne (hres.trans (mul_one _).symm)

theorem principal_degree_one_character_pow_eq_one (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G)
    (hnormalizer : Subgroup.normalizer ((P : Subgroup G) : Set G) =
      (P : Subgroup G) ⊔ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hdegree : (basis.representation χ).character 1 = 1) (g : G) :
    (basis.representation χ).character g ^ p ^ (Nat.card G).factorization p = 1 := by
  have hp : p.Prime := Fact.out
  have hcard : p ^ (Nat.card G).factorization p *
      (Nat.card G / p ^ (Nat.card G).factorization p) = Nat.card G :=
    Nat.ordProj_mul_ordCompl_eq_self _ p
  have hcoprime : Nat.Coprime p (Nat.card G / p ^ (Nat.card G).factorization p) :=
    Nat.coprime_ordCompl hp Nat.card_pos.ne'
  have hmul := character_mul_of_degree_eq_one (basis.representation χ) hdegree
  have hpow : ∀ (x : G) (n : ℕ), (basis.representation χ).character (x ^ n) =
      (basis.representation χ).character x ^ n := by
    intro x n
    induction n with
    | zero => rw [pow_zero, pow_zero, hdegree]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hroot : ∀ x : G, (basis.representation χ).character x ^ Nat.card G = 1 := fun x => by
    rw [← hpow, pow_card_eq_one', hdegree]
  let ψ : G →* ℂ :=
    { toFun := fun x => (basis.representation χ).character x ^ p ^ (Nat.card G).factorization p
      map_one' := by simp only [hdegree, one_pow]
      map_mul' := fun x y => by simp only [hmul, mul_pow] }
  have hψ : ∀ x, ψ x = (basis.representation χ).character x ^ p ^ (Nat.card G).factorization p :=
    fun x => rfl
  have hP : (P : Subgroup G) ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ]
    have hxpow : x ^ p ^ (Nat.card G).factorization p = 1 := by
      have h1 := pow_card_eq_one' (G := (P : Subgroup G)) (x := ⟨x, hx⟩)
      rw [P.card_eq_multiplicity] at h1
      exact congrArg Subtype.val h1
    rw [← hpow, hxpow, hdegree]
  have hC : Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ ψ.ker := by
    intro c hc
    rw [MonoidHom.mem_ker, hψ]
    have hmem : (basis.representation χ).character c ∈ localizedComplexIntegerRing ideal :=
      rootOfUnity_mem_localizedComplexIntegerRing ideal (Nat.card G) Nat.card_pos _ (hroot c)
    set ζ : localizedComplexIntegerRing ideal :=
      ⟨_, hmem⟩ ^ p ^ (Nat.card G).factorization p with hζ
    have hζval : (ζ : ℂ) =
        (basis.representation χ).character c ^ p ^ (Nat.card G).factorization p := by
      rw [hζ, SubmonoidClass.coe_pow]
    have hresidue : localizedComplexIntegerResidue ideal ζ = 1 := by
      rw [hζ, map_pow, principal_degree_one_residue_eq_one basis ideal p principal hprincipal χ hχ
        hdegree P c hc hmem, one_pow]
    have hζroot : (ζ : ℂ) ^ (Nat.card G / p ^ (Nat.card G).factorization p) = 1 := by
      rw [hζval, ← pow_mul, hcard, hroot]
    rw [← hζval]
    by_contra hne
    have hgeom : (∑ i ∈ Finset.range (Nat.card G / p ^ (Nat.card G).factorization p),
        (ζ : ℂ) ^ i) = 0 := by
      have h := geom_sum_mul (ζ : ℂ) (Nat.card G / p ^ (Nat.card G).factorization p)
      rw [hζroot, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
    have hgeomRing : (∑ i ∈ Finset.range (Nat.card G / p ^ (Nat.card G).factorization p),
        ζ ^ i) = 0 := by
      apply Subtype.ext
      rw [Subring.coe_zero, ← hgeom]
      push_cast
      rfl
    have hres := congrArg (localizedComplexIntegerResidue ideal) hgeomRing
    simp only [map_sum, map_pow, hresidue, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, map_zero] at hres
    rw [CharP.cast_eq_zero_iff _ p] at hres
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hcoprime hres)
  have hN : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ ψ.ker := by
    rw [hnormalizer]
    exact sup_le hP hC
  have htop : ψ.ker = ⊤ := by
    rw [eq_top_iff, ← Sylow.normalizer_sup_eq_top' (N := ψ.ker) P hP]
    exact sup_le hN le_rfl
  have hg : g ∈ ψ.ker := htop ▸ Subgroup.mem_top g
  rw [MonoidHom.mem_ker, hψ] at hg
  exact hg

@[expose] noncomputable def degreeOneCharacterUnits {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (hdegree : data.character 1 = 1) : G →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := data.character
      map_one' := hdegree
      map_mul' := character_mul_of_degree_eq_one data hdegree }

theorem degreeOneCharacterUnits_val {G : Type*} [Group G] (data : FiniteComplexRepresentation G)
    (hdegree : data.character 1 = 1) (g : G) :
    (degreeOneCharacterUnits data hdegree g : ℂ) = data.character g := rfl

theorem card_range_degreeOneCharacterUnits {G : Type*} [Group G] [Finite G]
    (data : FiniteComplexRepresentation G) (hdegree : data.character 1 = 1) :
    Nat.card (degreeOneCharacterUnits data hdegree).range =
      Nat.card (Set.range data.character) := by
  have hrange : Set.range data.character =
      Units.val '' Set.range (degreeOneCharacterUnits data hdegree) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, Nat.card_image_of_injective Units.val_injective]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => MonoidHom.mem_range)

theorem principal_linear_character_prime_power_from_sylow_normalizer
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow p G)
    (hnormalizer : Subgroup.normalizer ((P : Subgroup G) : Set G) =
      (P : Subgroup G) ⊔ Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character 1 = 1 →
        ∃ k : ℕ, Nat.card (Set.range (basis.representation χ).character) = p ^ k) ∧
    ((∀ H : Subgroup G, H.index ≠ p) →
      ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character 1 = 1 → χ = principal) := by
  have hp : p.Prime := Fact.out
  have hcardRange : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ hdegree : (basis.representation χ).character 1 = 1, ∃ k : ℕ,
        Nat.card (degreeOneCharacterUnits (basis.representation χ) hdegree).range = p ^ k := by
    intro χ hχ hdegree
    let : Finite (degreeOneCharacterUnits (basis.representation χ) hdegree).range :=
      Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    apply IsPGroup.iff_card.mp
    rintro ⟨z, g, rfl⟩
    refine ⟨(Nat.card G).factorization p, Subtype.ext (Units.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, degreeOneCharacterUnits_val,
      OneMemClass.coe_one, Units.val_one]
    exact principal_degree_one_character_pow_eq_one basis ideal p principal hprincipal P
      hnormalizer χ hχ hdegree g
  refine ⟨fun χ hχ hdegree => ?_, fun hindex χ hχ hdegree => ?_⟩
  · obtain ⟨k, hk⟩ := hcardRange χ hχ hdegree
    exact ⟨k, (card_range_degreeOneCharacterUnits _ hdegree).symm.trans hk⟩
  · by_contra hne
    set u := degreeOneCharacterUnits (basis.representation χ) hdegree
    obtain ⟨k, hk⟩ := hcardRange χ hχ hdegree
    have hnontrivial : u ≠ 1 := by
      intro hone
      apply hne
      apply basis.distinct
      change (basis.representation χ).character = (basis.representation principal).character
      rw [hprincipal]
      funext g
      rw [← degreeOneCharacterUnits_val _ hdegree, show u g = 1 by rw [hone]; rfl, Units.val_one,
        Pi.one_apply]
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hnontrivial
      rw [pow_zero, Subgroup.card_eq_one, MonoidHom.range_eq_bot_iff] at hk
      exact hk
    let : Finite u.range := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := u.range) p
      (n := k - 1) (hk ▸ pow_dvd_pow p (Nat.sub_le k 1))
    have hKindex : K.index = p := by
      have hmulIndex := K.card_mul_index
      rw [hK, hk] at hmulIndex
      have hsplit : p ^ k = p ^ (k - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
      rw [hsplit] at hmulIndex
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) hmulIndex
    apply hindex (K.comap u.rangeRestrict)
    rw [Subgroup.index_comap_of_surjective K (MonoidHom.rangeRestrict_surjective u), hKindex]

end CFSG.Semidihedral.Principal
