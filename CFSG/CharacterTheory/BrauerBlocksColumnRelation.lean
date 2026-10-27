module

public import CFSG.CharacterTheory.Semidihedral.Principal.NormalKernelBlockInflation
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasisDegreeSum
public import CFSG.CharacterTheory.OddOrderBasics.Schur
public import CFSG.CharacterTheory.Wreathed.AbelianQuotientTwists

public section

open scoped BigOperators Classical

namespace CFSG.BrauerBlocks

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G]

@[expose] noncomputable def classFinset (g : G) : Finset G :=
  Finset.univ.filter fun x => IsConj g x

theorem exists_classSum_eq_smul (data : FiniteComplexRepresentation G)
    (hirr : data.IsIrreducible) (k : G) :
    ∃ c : ℂ, ∑ x ∈ classFinset k, data.representation x = c • LinearMap.id ∧
      ((classFinset k).card : ℂ) * data.character k = c * data.character 1 := by
  have hT : ∀ g : G, (∑ x ∈ classFinset k, data.representation x) ∘ₗ data.representation g =
      data.representation g ∘ₗ (∑ x ∈ classFinset k, data.representation x) := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_nbij' (fun x => g⁻¹ * x * g) (fun x => g * x * g⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [classFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    · intro x hx
      simp only [classFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.trans (isConj_iff.mpr ⟨g, rfl⟩)
    · intro x _
      group
    · intro x _
      group
    · intro x _
      rw [← map_mul, ← map_mul]
      congr 1
      group
  obtain ⟨c, hc⟩ := CFSG.OddOrderBasics.complex_irreducible_commuting_scalar
    data.representation hirr _ hT
  refine ⟨c, hc, ?_⟩
  have htr := congrArg (LinearMap.trace ℂ data.vector) hc
  rw [map_sum, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  have hconst : ∀ x ∈ classFinset k, LinearMap.trace ℂ data.vector (data.representation x) =
      data.character k := by
    intro x hx
    simp only [classFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨u, hu⟩ := isConj_iff.mp hx
    rw [← hu]
    exact Representation.char_conj data.representation k u
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at htr
  rw [htr, FiniteComplexRepresentation.character, Representation.char_one]

theorem sum_classFinset_mul_character (data : FiniteComplexRepresentation G)
    (hirr : data.IsIrreducible) (g h : G) :
    ∑ x ∈ classFinset g, ∑ y ∈ classFinset h, data.character (x * y) =
      (classFinset g).card * (classFinset h).card * data.character g * data.character h /
        data.character 1 := by
  have : Nontrivial data.vector :=
    CFSG.Wreathed.nontrivial_of_isIrreducible data.representation hirr
  have h1 : data.character 1 ≠ 0 := by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
    exact_mod_cast Module.finrank_pos.ne'
  obtain ⟨cg, hcg, hcg'⟩ := exists_classSum_eq_smul data hirr g
  obtain ⟨ch, hch, hch'⟩ := exists_classSum_eq_smul data hirr h
  have hsum : ∑ x ∈ classFinset g, ∑ y ∈ classFinset h, data.character (x * y) =
      LinearMap.trace ℂ data.vector ((∑ x ∈ classFinset g, data.representation x) *
        (∑ y ∈ classFinset h, data.representation y)) := by
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [FiniteComplexRepresentation.character, Representation.character, map_mul]
  rw [hsum, hcg, hch, smul_mul_smul_comm, Module.End.mul_eq_comp, LinearMap.id_comp, map_smul,
    LinearMap.trace_id, smul_eq_mul]
  rw [eq_div_iff h1]
  have hdim : (Module.finrank ℂ data.vector : ℂ) = data.character 1 := by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  rw [hdim]
  linear_combination (-((classFinset h).card * data.character h)) * hcg' +
    (-(cg * data.character 1)) * hch'

omit [Fintype G] in
theorem sq_eq_one_of_isConj {σ x : G} (hσ : orderOf σ = 2) (hx : IsConj σ x) : x ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hx
  rw [conj_pow, ← hσ, pow_orderOf_eq_one, mul_one, mul_inv_cancel]

omit [Fintype G] in
theorem isConj_inv_of_mem_zpowers_mul {x y a : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (ha : a ∈ Subgroup.zpowers (x * y)) : IsConj a a⁻¹ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx])
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy])
  have hconj : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxinv, hyinv, ← mul_assoc, ← sq, hx, one_mul]
  refine isConj_iff.mpr ⟨x, ?_⟩
  rw [← conj_zpow, hconj, inv_zpow]

omit [Fintype G] in
theorem isConj_inv_inv {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨c, by group⟩

variable (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]

theorem nonreal_column_relation (blockLabel : basis.index) {π σ τ : G}
    (hπ : ∃ k, orderOf π = 2 ^ k) (hπinv : ¬ IsConj π π⁻¹) (hσ : orderOf σ = 2)
    (hτ : orderOf τ = 2) {ρ : G} (hρ : ρ ∈ Subgroup.centralizer {π}) (hρodd : Odd (orderOf ρ)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
      (basis.representation χ).character (π * ρ) * (basis.representation χ).character σ *
        (basis.representation χ).character τ / (basis.representation χ).character 1 = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hπ
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel
  have hcard : ((classFinset σ).card : ℂ) * (classFinset τ).card ≠ 0 := by
    have h1 : σ ∈ classFinset σ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl σ⟩
    have h2 : τ ∈ classFinset τ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl τ⟩
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem h1))
      (Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem h2))
  have hρπ : Commute π ρ := (Subgroup.mem_centralizer_singleton_iff.mp hρ).symm
  have key : ((classFinset σ).card : ℂ) * (classFinset τ).card *
      ∑ χ ∈ B, (basis.representation χ).character (π * ρ) *
        (basis.representation χ).character σ * (basis.representation χ).character τ /
          (basis.representation χ).character 1 = 0 := by
    calc ((classFinset σ).card : ℂ) * (classFinset τ).card *
          ∑ χ ∈ B, (basis.representation χ).character (π * ρ) *
            (basis.representation χ).character σ * (basis.representation χ).character τ /
              (basis.representation χ).character 1 =
        ∑ χ ∈ B, (basis.representation χ).character (π * ρ) *
          ∑ x ∈ classFinset σ, ∑ y ∈ classFinset τ,
            (basis.representation χ).character (x * y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [sum_classFinset_mul_character _ (basis.irreducible χ)]
          ring
      _ = ∑ x ∈ classFinset σ, ∑ y ∈ classFinset τ, ∑ χ ∈ B,
            (basis.representation χ).character (x * y) *
              (basis.representation χ).character (π * ρ) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun χ _ => ?_
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
          simp only [classFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
          obtain ⟨a, b, e, ha, -, hab, hprod, hord, hcop⟩ :=
            finite_prime_primary_factorization (x * y) 2 Nat.prime_two
          have hconj : ¬ IsConj a π⁻¹ := by
            intro h
            have h1 := isConj_inv_of_mem_zpowers_mul (sq_eq_one_of_isConj hσ hx)
              (sq_eq_one_of_isConj hτ hy) ha
            have h2 := isConj_inv_inv h
            rw [inv_inv] at h2
            exact hπinv ((h2.symm.trans h1.symm).trans h)
          have h := coefficientBlock_section_column_orthogonality basis ideal 2 blockLabel
            a π⁻¹ b ρ⁻¹ e k hord (by rw [orderOf_inv, hk]) hcop
            (by rw [orderOf_inv]; exact Nat.coprime_two_left.mpr hρodd) hab hρπ.inv_inv hconj
          have hinv : (π⁻¹ * ρ⁻¹)⁻¹ = π * ρ := by rw [mul_inv_rev, inv_inv, inv_inv, hρπ.eq]
          rw [hprod, hinv] at h
          exact h
  exact (mul_eq_zero.mp key).resolve_left hcard

theorem nonreal_column_relation_span (blockLabel : basis.index) {π σ τ : G}
    (hπ : ∃ k, orderOf π = 2 ^ k) (hπinv : ¬ IsConj π π⁻¹) (hσ : orderOf σ = 2)
    (hτ : orderOf τ = 2) (c : basis.index → ℂ)
    (hc : c ∈ Submodule.span ℂ (Set.range fun ρ : {ρ : G // ρ ∈ Subgroup.centralizer {π} ∧
      Odd (orderOf ρ)} => fun χ : basis.index => (basis.representation χ).character (π * ρ))) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
      c χ * (basis.representation χ).character σ * (basis.representation χ).character τ /
        (basis.representation χ).character 1 = 0 := by
  induction hc using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨ρ, hρ, hρodd⟩, rfl⟩ := hf
      exact nonreal_column_relation basis ideal blockLabel hπ hπinv hσ hτ hρ hρodd
  | zero => simp
  | add f g _ _ hf hg =>
      simp only [Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib, hf, hg, add_zero]
  | smul a f _ hf =>
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_div_assoc] at hf ⊢
      rw [← Finset.mul_sum, hf, mul_zero]

omit [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] in
theorem sum_degree_sq_of_inflations {Q : Type} [Group Q] [Fintype Q] (π : G →* Q)
    (hπ : Function.Surjective π) (quotientBasis : FiniteIrreducibleCharacterBasis Q)
    (B : Finset basis.index)
    (hB : ∀ χ, χ ∈ B ↔ ∃ θ, (basis.representation χ).character =
      (quotientBasis.representation θ).character ∘ π) :
    ∑ χ ∈ B, (basis.representation χ).character 1 ^ 2 = Nat.card Q := by
  choose χ' hχ' using fun θ => CFSG.Semidihedral.Principal.exists_inflated_label π hπ basis
    quotientBasis θ
  have hinj : Function.Injective χ' := by
    intro θ θ' h
    apply quotientBasis.distinct
    funext q
    obtain ⟨g, rfl⟩ := hπ q
    have h1 : (quotientBasis.representation θ).character ∘ π =
        (quotientBasis.representation θ').character ∘ π := by
      rw [← hχ' θ, ← hχ' θ', h]
    exact congrFun h1 g
  have himage : Finset.univ.image χ' = B := by
    ext χ
    rw [Finset.mem_image, hB]
    constructor
    · rintro ⟨θ, -, rfl⟩
      exact ⟨θ, hχ' θ⟩
    · rintro ⟨θ, hθ⟩
      exact ⟨θ, Finset.mem_univ _, basis.distinct ((hχ' θ).trans hθ.symm)⟩
  rw [← himage, Finset.sum_image fun θ _ θ' _ h => hinj h]
  have hdeg : ∀ θ, (basis.representation (χ' θ)).character 1 =
      (Module.finrank ℂ (quotientBasis.representation θ).vector : ℂ) := by
    intro θ
    rw [hχ' θ, Function.comp_apply, map_one, FiniteComplexRepresentation.character,
      Representation.char_one]
  simp only [hdeg]
  exact_mod_cast finiteIrreducibleCharacterBasis_sum_finrank_sq quotientBasis

theorem brauer_blocks_nonreal_involution_column_relation (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∀ (blockLabel : basis.index) (π σ τ : G), (∃ k, orderOf π = 2 ^ k) →
      ¬ IsConj π π⁻¹ → orderOf σ = 2 → orderOf τ = 2 →
      (∀ ρ ∈ Subgroup.centralizer {π}, Odd (orderOf ρ) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
          (basis.representation χ).character (π * ρ) * (basis.representation χ).character σ *
            (basis.representation χ).character τ / (basis.representation χ).character 1 = 0) ∧
      ∀ c : basis.index → ℂ, c ∈ Submodule.span ℂ (Set.range fun ρ : {ρ : G //
          ρ ∈ Subgroup.centralizer {π} ∧ Odd (orderOf ρ)} =>
            fun χ : basis.index => (basis.representation χ).character (π * ρ)) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
          c χ * (basis.representation χ).character σ * (basis.representation χ).character τ /
            (basis.representation χ).character 1 = 0) ∧
    (∀ (K : Subgroup G) [K.Normal], Odd (Nat.card K) → IsPGroup 2 (G ⧸ K) →
      (∀ g : G, g ∈ K ↔ Odd (orderOf g)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal, ∀ y ∈ K,
        (basis.representation χ).character y = (basis.representation χ).character 1) ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character 1 ^ 2 = K.index ∧
      K.index = 2 ^ (Nat.card G).factorization 2) ∧
    (∀ (W : Subgroup G) [W.Normal], Odd (Nat.card W) →
      ∀ (quotientBasis : FiniteIrreducibleCharacterBasis (G ⧸ W))
        (quotientPrincipal : quotientBasis.index),
        (quotientBasis.representation quotientPrincipal).character = 1 →
        (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          ∃ θ ∈ coefficientBlock quotientBasis (localizedComplexIntegerRing ideal)
            quotientPrincipal,
            (basis.representation χ).character =
              (quotientBasis.representation θ).character ∘ QuotientGroup.mk' W) ∧
        ∀ θ ∈ coefficientBlock quotientBasis (localizedComplexIntegerRing ideal) quotientPrincipal,
          ∃ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            (basis.representation χ).character =
              (quotientBasis.representation θ).character ∘ QuotientGroup.mk' W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun blockLabel π σ τ hπ hπinv hσ hτ => ⟨fun ρ hρ hρodd =>
      nonreal_column_relation basis ideal blockLabel hπ hπinv hσ hτ hρ hρodd,
    fun c hc => nonreal_column_relation_span basis ideal blockLabel hπ hπinv hσ hτ c hc⟩,
    fun K _ hK hquot => ?_, fun W _ hW quotientBasis quotientPrincipal hqp => ?_⟩
  ·
    have hcop : Nat.Coprime 2 (Nat.card K) := Nat.coprime_two_left.mpr hK
    obtain ⟨hker, hinfl, -⟩ := CFSG.LyonsUnitaryFour.normal_p_complement_principal_block basis
      ideal 2 principal hprincipal K hcop hquot
    have hodd : ∀ g : G, g ∈ K ↔ Odd (orderOf g) := by
      intro g
      constructor
      · intro hg
        exact Odd.of_dvd_nat hK (Subgroup.orderOf_dvd_natCard K hg)
      · intro hg
        obtain ⟨n, hn⟩ := hquot (QuotientGroup.mk' K g)
        have h1 : orderOf (QuotientGroup.mk' K g) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
        have h2 : orderOf (QuotientGroup.mk' K g) ∣ orderOf g := orderOf_map_dvd _ g
        have h3 : orderOf (QuotientGroup.mk' K g) = 1 :=
          Nat.eq_one_of_dvd_coprimes
            (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hg)) h1 h2
        rw [orderOf_eq_one_iff] at h3
        exact (QuotientGroup.eq_one_iff g).mp h3
    refine ⟨hodd, fun χ hχ y hy => ?_, ?_, ?_⟩
    · have h1 := (hker χ).mp hχ hy
      rw [MonoidHom.mem_ker] at h1
      change Representation.character _ y = Representation.character _ 1
      rw [Representation.character, h1, ← map_one (basis.representation χ).representation]
      rfl
    · obtain ⟨quotientBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := G ⧸ K)
      have h := sum_degree_sq_of_inflations basis (QuotientGroup.mk' K)
        (QuotientGroup.mk'_surjective K) quotientBasis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (fun χ => by
          rw [hinfl χ]
          constructor
          · rintro ⟨data, hdata, hχ⟩
            obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible quotientBasis
              data hdata
            exact ⟨θ, by rw [hχ, hθ]⟩
          · rintro ⟨θ, hθ⟩
            exact ⟨quotientBasis.representation θ, quotientBasis.irreducible θ, hθ⟩)
      rw [h, Subgroup.index]
    ·
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hquot
      have hcard : Nat.card G = Nat.card K * 2 ^ m := by
        rw [← hm, mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
      have hKodd : ¬ 2 ∣ Nat.card K := by
        rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
        exact hK
      have hf : (Nat.card K * 2 ^ m).factorization 2 = m := by
        rw [Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero _ two_ne_zero), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hKodd, zero_add, Nat.factorization_pow,
          Finsupp.smul_apply, smul_eq_mul, Nat.prime_two.factorization_self, mul_one]
      rw [Subgroup.index, hm, hcard, hf]
  ·
    have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' W).ker := by
      rw [QuotientGroup.ker_mk', ← even_iff_two_dvd, Nat.not_even_iff_odd]
      exact hW
    obtain ⟨hinfl, -, -, -⟩ :=
      CFSG.Semidihedral.Principal.normal_prime_kernel_principal_block_inflation_of_surjective
        (QuotientGroup.mk' W) (QuotientGroup.mk'_surjective W) basis ideal 2 hker quotientBasis
        principal hprincipal quotientPrincipal hqp
    refine ⟨fun χ hχ => (hinfl χ).mp hχ, fun θ hθ => ?_⟩
    obtain ⟨χ, hχ⟩ := CFSG.Semidihedral.Principal.exists_inflated_label (QuotientGroup.mk' W)
      (QuotientGroup.mk'_surjective W) basis quotientBasis θ
    exact ⟨χ, (hinfl χ).mpr ⟨θ, hθ, hχ⟩, hχ⟩

end CFSG.BrauerBlocks
