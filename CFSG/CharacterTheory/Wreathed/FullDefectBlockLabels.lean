module

public import CFSG.CharacterTheory.Wreathed.BaseFourCentralizerStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.NormalAbelianCentralizerOrbitIdempotents
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.BlockOrbits
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.OrbitIdempotents

namespace FullDefectLabels

variable {G : Type*} [Group G]

section Embedding

variable {K E : Subgroup G} (hEK : E ≤ K)

theorem inclusion_central_of_conj [Fintype G]
    (hconj : ∀ k : K, ∃ y : E, ∀ x : E,
      k * Subgroup.inclusion hEK x * k⁻¹ = Subgroup.inclusion hEK (y * x * y⁻¹))
    (z : MonoidAlgebra ℂ E) (hz : ∀ o, Commute z o) :
    ∀ o : MonoidAlgebra ℂ K, Commute (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) z)
      o := by
  have hι : Function.Injective (Subgroup.inclusion hEK) := Subgroup.inclusion_injective hEK
  apply groupAlgebra_central_of_coeff_conjugation
  intro v w
  obtain ⟨y, hy⟩ := hconj w
  by_cases hv : v ∈ Set.range (Subgroup.inclusion hEK)
  · obtain ⟨x, rfl⟩ := hv
    rw [hy, embedded_coeff _ hι, embedded_coeff _ hι]
    exact central_groupAlgebra_coeff_conjugation z hz x y
  · have hv' : w * v * w⁻¹ ∉ Set.range (Subgroup.inclusion hEK) := by
      rintro ⟨x, hx⟩
      apply hv
      obtain ⟨y', hy'⟩ := hconj w⁻¹
      refine ⟨y' * x * y'⁻¹, ?_⟩
      rw [← hy', hx]
      group
    rw [embedded_coeff_zero _ _ _ hv', embedded_coeff_zero _ _ _ hv]

theorem scalar_inclusion_of_character_eq [Fintype G] (kb : FiniteIrreducibleCharacterBasis K)
    (eb : FiniteIrreducibleCharacterBasis E) {χ : kb.index} {θ : eb.index}
    (hχ : ∀ x : E, (kb.representation χ).character (Subgroup.inclusion hEK x) =
      (eb.representation θ).character x) (z : MonoidAlgebra ℂ E) :
    centralCharacterScalar kb (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) z) χ =
      centralCharacterScalar eb z θ := by
  have hι : Function.Injective (Subgroup.inclusion hEK) := Subgroup.inclusion_injective hEK
  have hK : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hE : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 : (kb.representation χ).character 1 = (eb.representation θ).character 1 := by
    have h := hχ 1
    rwa [map_one] at h
  have hsumK : ∑ k : K, (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) z).coeff k⁻¹ *
      (kb.representation χ).character k⁻¹ =
      ∑ x : E, z.coeff x * (eb.representation θ).character x := by
    rw [← Equiv.sum_comp (Equiv.inv K)]
    simp only [Equiv.inv_apply, inv_inv]
    symm
    apply Fintype.sum_of_injective (Subgroup.inclusion hEK) hι
    · intro k hk
      rw [embedded_coeff_zero _ _ _ hk, zero_mul]
    · intro x
      rw [embedded_coeff _ hι, hχ]
  have hsumE : ∑ x : E, z.coeff x⁻¹ * (eb.representation θ).character x⁻¹ =
      ∑ x : E, z.coeff x * (eb.representation θ).character x := by
    rw [← Equiv.sum_comp (Equiv.inv E)]
    simp only [Equiv.inv_apply, inv_inv]
  unfold centralCharacterScalar characterPairing
  rw [hsumK, hsumE, h1]
  field_simp

theorem scalar_embedded_of_scalar_eq_one [Fintype G] (kb : FiniteIrreducibleCharacterBasis K)
    (eb : FiniteIrreducibleCharacterBasis E)
    (hcent : ∀ z : MonoidAlgebra ℂ E, (∀ o, Commute z o) →
      ∀ o, Commute (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) z) o)
    {θ : eb.index} {χ : kb.index}
    (hχ : centralCharacterScalar kb (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK)
      (complexCharacterIdempotent (eb.representation θ).character)) χ = 1)
    (z : MonoidAlgebra ℂ E) (hz : ∀ o, Commute z o) :
    centralCharacterScalar kb (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) z) χ =
      centralCharacterScalar eb z θ := by
  have hεc := hcent _ (complexCharacterIdempotent_central (eb.representation θ))
  have hprod : MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK)
      (complexCharacterIdempotent (eb.representation θ).character) *
      MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) z =
      centralCharacterScalar eb z θ • MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK)
        (complexCharacterIdempotent (eb.representation θ).character) := by
    rw [← map_mul, complexCharacterIdempotent_mul_central eb θ z hz, mapDomainRingHom_smul]
  have h1 := congrArg (fun x => centralCharacterScalar kb x χ) hprod
  rw [scalar_mul kb _ _ hεc (hcent z hz), scalar_smul kb _ _ hεc, hχ, one_mul, mul_one] at h1
  exact h1

end Embedding

section Product

variable [Fintype G] {K Z E : Subgroup G} (hZK : Z ≤ K) (hEK : E ≤ K)

abbrev toK (a : Z) : K := ⟨a, hZK a.2⟩

@[expose] noncomputable def component (z : MonoidAlgebra ℂ K) (a : Z) : MonoidAlgebra ℂ E :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun x : E =>
    z.coeff (toK hZK a * Subgroup.inclusion hEK x))

theorem component_coeff (z : MonoidAlgebra ℂ K) (a : Z) (x : E) :
    (component hZK hEK z a).coeff x = z.coeff (toK hZK a * Subgroup.inclusion hEK x) := rfl

omit [Fintype G] in
theorem mem_range_iff (hZE : Z ⊓ E = ⊥) (a b : Z) (x : E) :
    (toK hZK a)⁻¹ * (toK hZK b * Subgroup.inclusion hEK x) ∈
        Set.range (Subgroup.inclusion hEK) ↔ a = b := by
  constructor
  · rintro ⟨y, hy⟩
    have hval := congrArg Subtype.val hy
    change (y : G) = (a : G)⁻¹ * (b * x) at hval
    have hab : (a : G)⁻¹ * b = y * (x : G)⁻¹ := by
      calc (a : G)⁻¹ * b = (a : G)⁻¹ * (b * x) * (x : G)⁻¹ := by group
        _ = y * (x : G)⁻¹ := by rw [hval]
    have hmem : (a : G)⁻¹ * b ∈ Z ⊓ E := ⟨Z.mul_mem (Z.inv_mem a.property) b.property, by
      rw [hab]
      exact E.mul_mem y.property (E.inv_mem x.property)⟩
    rw [hZE, Subgroup.mem_bot] at hmem
    apply Subtype.ext
    calc (a : G) = a * ((a : G)⁻¹ * b) := by rw [hmem, mul_one]
      _ = b := by group
  · rintro rfl
    refine ⟨x, Subtype.ext ?_⟩
    change (x : G) = (a : G)⁻¹ * (a * x)
    group

theorem decomposition (hZE : Z ⊓ E = ⊥) (z : MonoidAlgebra ℂ K)
    (hsupp : ∀ k : K, z.coeff k ≠ 0 → ∃ a ∈ Z, ∃ x ∈ E, (k : G) = a * x) :
    z = ∑ a : Z, MonoidAlgebra.single (toK hZK a) (1 : ℂ) *
      MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) (component hZK hEK z a) := by
  have hι : Function.Injective (Subgroup.inclusion hEK) := Subgroup.inclusion_injective hEK
  ext k
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply' (s := Finset.univ)]
  by_cases hk : ∃ a ∈ Z, ∃ x ∈ E, (k : G) = a * x
  · obtain ⟨b, hb, x, hx, hkbx⟩ := hk
    have hk' : k = toK hZK ⟨b, hb⟩ * Subgroup.inclusion hEK ⟨x, hx⟩ := Subtype.ext hkbx
    rw [Finset.sum_eq_single (⟨b, hb⟩ : Z)]
    · rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, hk']
      obtain ⟨y, hy⟩ := (mem_range_iff hZK hEK hZE ⟨b, hb⟩ ⟨b, hb⟩ ⟨x, hx⟩).mpr rfl
      rw [← hy, embedded_coeff _ hι, component_coeff]
      congr 1
      rw [hy]
      group
    · intro a _ hab
      rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, hk']
      apply embedded_coeff_zero
      intro hmem
      exact hab ((mem_range_iff hZK hEK hZE a ⟨b, hb⟩ ⟨x, hx⟩).mp hmem)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hz : z.coeff k = 0 := by
      by_contra h
      exact hk (hsupp k h)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro a _
    rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]
    apply embedded_coeff_zero
    rintro ⟨x, hx⟩
    apply hk
    have hkx : k = toK hZK a * Subgroup.inclusion hEK x := by
      rw [hx]
      group
    exact ⟨a, a.2, x, x.2, congrArg Subtype.val hkx⟩

theorem component_central (hZc : ∀ (a : Z) (k : K), toK hZK a * k = k * toK hZK a)
    (z : MonoidAlgebra ℂ K) (hz : ∀ o, Commute z o) (a : Z) :
    ∀ o : MonoidAlgebra ℂ E, Commute (component hZK hEK z a) o := by
  apply groupAlgebra_central_of_coeff_conjugation
  intro x c
  rw [component_coeff, component_coeff]
  have hconj : toK hZK a * Subgroup.inclusion hEK (c * x * c⁻¹) =
      Subgroup.inclusion hEK c * (toK hZK a * Subgroup.inclusion hEK x) *
        (Subgroup.inclusion hEK c)⁻¹ := by
    rw [map_mul (Subgroup.inclusion hEK), map_mul (Subgroup.inclusion hEK),
      map_inv (Subgroup.inclusion hEK)]
    calc toK hZK a * (Subgroup.inclusion hEK c * Subgroup.inclusion hEK x *
          (Subgroup.inclusion hEK c)⁻¹) =
        (toK hZK a * Subgroup.inclusion hEK c) * Subgroup.inclusion hEK x *
          (Subgroup.inclusion hEK c)⁻¹ := by group
      _ = (Subgroup.inclusion hEK c * toK hZK a) * Subgroup.inclusion hEK x *
          (Subgroup.inclusion hEK c)⁻¹ := by rw [hZc a]
      _ = _ := by group
  rw [hconj]
  exact central_groupAlgebra_coeff_conjugation z hz _ _

theorem single_mem (hZc : ∀ (a : Z) (k : K), toK hZK a * k = k * toK hZK a) (ring : Subring ℂ)
    (a : Z) :
    MonoidAlgebra.single (toK hZK a) (1 : ℂ) ∈ centralCoefficientSubring (G := K) ring := by
  have hcent : ∀ o : MonoidAlgebra ℂ K, Commute (MonoidAlgebra.single (toK hZK a) (1 : ℂ)) o := by
    apply groupAlgebra_central_of_coeff_conjugation
    intro v w
    have hconj : w⁻¹ * toK hZK a * w = toK hZK a := by
      rw [mul_assoc, hZc a w, ← mul_assoc, inv_mul_cancel, one_mul]
    have hiff : toK hZK a = w * v * w⁻¹ ↔ toK hZK a = v := by
      constructor
      · intro h
        calc toK hZK a = w⁻¹ * toK hZK a * w := hconj.symm
          _ = w⁻¹ * (w * v * w⁻¹) * w := by rw [← h]
          _ = v := by group
      · intro h
        rw [← h, ← hZc a w, mul_inv_cancel_right]
    change (Finsupp.single (toK hZK a) (1 : ℂ)) (w * v * w⁻¹) =
      (Finsupp.single (toK hZK a) (1 : ℂ)) v
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hv : toK hZK a = v
    · rw [ite_eq_left hv, ite_eq_left (hiff.mpr hv)]
    · rw [ite_eq_right hv, ite_eq_right fun h => hv (hiff.mp h)]
  refine Subring.mem_inf.mpr ⟨fun w => ?_, Subring.mem_center_iff.mpr fun o =>
    (hcent o).eq.symm⟩
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs
  · exact ring.one_mem
  · exact ring.zero_mem

theorem residue_single_eq_one (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hZp : IsPGroup p Z)
    (kb : FiniteIrreducibleCharacterBasis K) (χ : kb.index) (a : Z)
    (s : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal))
    (hs : s.val = MonoidAlgebra.single (toK hZK a) (1 : ℂ)) :
    centralCharacterResidueHom kb ideal χ s = 1 := by
  obtain ⟨k, hk⟩ := hZp a
  have hak : toK hZK a ^ (p ^ k) = 1 := Subtype.ext (by
    have hval := congrArg Subtype.val hk
    simpa using hval)
  have hpow : s ^ (p ^ k) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hs, MonoidAlgebra.single_pow, one_pow, hak]
    rfl
  have hres := congrArg (centralCharacterResidueHom kb ideal χ) hpow
  rw [map_pow, map_one] at hres
  have hsub : (centralCharacterResidueHom kb ideal χ s - 1) ^ (p ^ k) = 0 := by
    rw [sub_pow_char_pow, hres, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero)).mp hsub)

theorem residue_eq_of_scalar_eq (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hZp : IsPGroup p Z)
    (hZE : Z ⊓ E = ⊥) (hZc : ∀ (a : Z) (k : K), toK hZK a * k = k * toK hZK a)
    (hcent : ∀ z : MonoidAlgebra ℂ E, (∀ o, Commute z o) →
      ∀ o, Commute (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) z) o)
    (kb : FiniteIrreducibleCharacterBasis K) {χ χ' : kb.index}
    (hscalar : ∀ y : MonoidAlgebra ℂ E, (∀ o, Commute y o) →
      centralCharacterScalar kb (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) y) χ =
        centralCharacterScalar kb (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) y) χ')
    (z : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal))
    (hsupp : ∀ k : K, z.val.coeff k ≠ 0 → ∃ a ∈ Z, ∃ x ∈ E, (k : G) = a * x) :
    centralCharacterResidueHom kb ideal χ z = centralCharacterResidueHom kb ideal χ' z := by
  have hι : Function.Injective (Subgroup.inclusion hEK) := Subgroup.inclusion_injective hEK
  have hzc := centralCoefficientSubring_commutes _ z
  have hmem : ∀ a : Z, MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK)
      (component hZK hEK z.val a) ∈
        centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal) := by
    intro a
    refine Subring.mem_inf.mpr ⟨fun w => ?_, Subring.mem_center_iff.mpr fun o =>
      (hcent _ (component_central hZK hEK hZc z.val hzc a) o).eq.symm⟩
    by_cases hw : w ∈ Set.range (Subgroup.inclusion hEK)
    · obtain ⟨x, rfl⟩ := hw
      rw [embedded_coeff _ hι, component_coeff]
      exact centralCoefficientSubring_coefficients _ z _
    · rw [embedded_coeff_zero _ _ _ hw]
      exact (localizedComplexIntegerRing ideal).zero_mem
  let s : Z → centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal) :=
    fun a => ⟨_, single_mem hZK hZc _ a⟩
  let t : Z → centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal) :=
    fun a => ⟨_, hmem a⟩
  have hz : z = ∑ a, s a * t a := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul]
    exact decomposition hZK hEK hZE z.val hsupp
  rw [hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, residue_single_eq_one hZK ideal hZp kb χ a (s a) rfl,
    residue_single_eq_one hZK ideal hZp kb χ' a (s a) rfl, one_mul, one_mul]
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom kb ideal χ (t a)) =
    localizedComplexIntegerResidue ideal (localCentralCharacterHom kb ideal χ' (t a))
  congr 1
  apply Subtype.ext
  rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe]
  exact hscalar _ (component_central hZK hEK hZc z.val hzc a)

end Product

section Support

variable [Fintype G] {K E : Subgroup G} (hEK : E ≤ K)
  (kb : FiniteIrreducibleCharacterBasis K) (eb : FiniteIrreducibleCharacterBasis E)

@[expose] noncomputable def embIdem (θ : eb.index) : MonoidAlgebra ℂ K :=
  MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK)
    (complexCharacterIdempotent (eb.representation θ).character)

theorem embIdem_isIdempotent (θ : eb.index) : IsIdempotentElem (embIdem hEK eb θ) := by
  have h := characterSubsetIdempotent_isIdempotent eb {θ}
  rw [characterSubsetIdempotent_singleton] at h
  unfold embIdem
  rw [IsIdempotentElem, ← map_mul, h.eq]

theorem embIdem_mul_of_ne {θ ν : eb.index} (h : θ ≠ ν) :
    embIdem hEK eb θ * embIdem hEK eb ν = 0 := by
  have hinter : ({θ} : Finset eb.index) ∩ {ν} = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro rfl
    exact h
  unfold embIdem
  rw [← map_mul, ← characterSubsetIdempotent_singleton, ← characterSubsetIdempotent_singleton,
    ← characterSubsetIdempotent_inter, hinter, characterSubsetIdempotent_empty, map_zero]

theorem embIdem_injective : Function.Injective (embIdem hEK eb) := by
  intro θ ν h
  have h' : complexCharacterIdempotent (eb.representation θ).character =
      complexCharacterIdempotent (eb.representation ν).character :=
    MonoidAlgebra.mapDomain_injective (R := ℂ) (Subgroup.inclusion_injective hEK) h
  rw [← characterSubsetIdempotent_singleton, ← characterSubsetIdempotent_singleton] at h'
  exact Finset.singleton_injective (characterSubsetIdempotent_injective eb h')

theorem embIdem_sum : ∑ θ, embIdem hEK eb θ = 1 := by
  unfold embIdem
  rw [← map_sum, ← characterSubsetIdempotent_eq_sum eb, characterSubsetIdempotent_univ, map_one]

theorem embIdem_coeff_mem (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hEp : ¬ p ∣ Nat.card E) (θ : eb.index) (k : K) :
    (embIdem hEK eb θ).coeff k ∈ localizedComplexIntegerRing ideal := by
  have hadm := singleton_admissible_of_full_prime_part_dvd_degree eb ideal p θ (by
    rw [Nat.factorization_eq_zero_of_not_dvd hEp, pow_zero]
    exact one_dvd _)
  have hadm' : ∀ x, (characterSubsetIdempotent eb {θ}).coeff x ∈
      localizedComplexIntegerRing ideal := hadm
  unfold embIdem
  by_cases hk : k ∈ Set.range (Subgroup.inclusion hEK)
  · obtain ⟨x, rfl⟩ := hk
    rw [embedded_coeff _ (Subgroup.inclusion_injective hEK),
      ← characterSubsetIdempotent_singleton]
    exact hadm' x
  · rw [embedded_coeff_zero _ _ _ hk]
    exact (localizedComplexIntegerRing ideal).zero_mem

@[expose] noncomputable def embSupport (θ : eb.index) : Finset kb.index :=
  Finset.univ.filter fun χ => centralCharacterScalar kb (embIdem hEK eb θ) χ = 1

theorem mem_embSupport (θ : eb.index) (χ : kb.index) :
    χ ∈ embSupport hEK kb eb θ ↔ centralCharacterScalar kb (embIdem hEK eb θ) χ = 1 := by
  simp only [embSupport, Finset.mem_filter, Finset.mem_univ, true_and]

variable (hcent : ∀ z : MonoidAlgebra ℂ E, (∀ o, Commute z o) →
  ∀ o, Commute (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEK) z) o)

include hcent in
theorem embIdem_central (θ : eb.index) : ∀ o, Commute (embIdem hEK eb θ) o :=
  hcent _ (complexCharacterIdempotent_central _)

include hcent in
theorem embIdem_eq_support (θ : eb.index) :
    embIdem hEK eb θ = characterSubsetIdempotent kb (embSupport hEK kb eb θ) := by
  obtain ⟨T, hT, -⟩ := central_idempotent_eq_character_subset kb _
    (embIdem_central hEK eb hcent θ) (embIdem_isIdempotent hEK eb θ)
  have hTS : T = embSupport hEK kb eb θ := by
    ext χ
    rw [mem_embSupport, hT, scalar_characterSubsetIdempotent]
    by_cases hχ : χ ∈ T
    · simp [hχ]
    · simp [hχ]
  rw [hT, hTS]

include hcent in
theorem embSupport_admissible (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hEp : ¬ p ∣ Nat.card E) (θ : eb.index) :
    characterSubsetAdmissible kb (localizedComplexIntegerRing ideal) (embSupport hEK kb eb θ) := by
  change characterSubsetIdempotent kb _ ∈ groupAlgebraCoefficientSubring _
  rw [← embIdem_eq_support hEK kb eb hcent θ]
  exact fun k => embIdem_coeff_mem hEK eb ideal p hEp θ k

include hcent in
theorem exists_mem_embSupport (χ : kb.index) : ∃ θ, χ ∈ embSupport hEK kb eb θ := by
  have h1 := congrArg (fun x => centralCharacterScalar kb x χ) (embIdem_sum hEK eb)
  rw [scalar_sum kb _ _ (fun θ => embIdem_central hEK eb hcent θ), scalar_one] at h1
  by_contra hnone
  have hzero : ∀ θ, centralCharacterScalar kb (embIdem hEK eb θ) χ = 0 := by
    intro θ
    rcases central_idempotent_scalar_zero_or_one kb _ (embIdem_central hEK eb hcent θ)
      (embIdem_isIdempotent hEK eb θ) χ with h | h
    · exact h
    · exact absurd ⟨θ, (mem_embSupport hEK kb eb θ χ).mpr h⟩ hnone
  rw [Finset.sum_congr rfl fun θ _ => hzero θ, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

include hcent in
theorem embSupport_unique {θ ν : eb.index} {χ : kb.index} (hθ : χ ∈ embSupport hEK kb eb θ)
    (hν : χ ∈ embSupport hEK kb eb ν) : θ = ν := by
  by_contra hne
  have h0 := congrArg (fun x => centralCharacterScalar kb x χ) (embIdem_mul_of_ne hEK eb hne)
  rw [scalar_mul kb _ _ (embIdem_central hEK eb hcent θ) (embIdem_central hEK eb hcent ν),
    (mem_embSupport hEK kb eb θ χ).mp hθ, (mem_embSupport hEK kb eb ν χ).mp hν, one_mul,
    scalar_zero] at h0
  exact one_ne_zero h0

end Support

omit [Group G] in
theorem mem_centralizer_subgroupOf_iff {G : Type*} [Group G] {S K : Subgroup G} (hSK : S ≤ K)
    (x : K) : x ∈ Subgroup.centralizer ((S.subgroupOf K : Subgroup K) : Set K) ↔
      (x : G) ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    exact congrArg Subtype.val (h ⟨g, hSK hg⟩ (Subgroup.mem_subgroupOf.mpr hg))
  · intro h y hy
    exact Subtype.ext (h y (Subgroup.mem_subgroupOf.mp hy))

theorem coefficientBlockDefect_of_normal_sylow [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (P : Sylow p G) [(P : Subgroup G).Normal] (χ : basis.index) :
    coefficientBlockDefect basis ideal p χ P := by
  obtain ⟨D, hD⟩ := coefficientBlockDefect_exists basis ideal p χ
  have hPD := normal_p_le_coefficientBlockDefect basis ideal p P P.isPGroup' hD
  have hDP := CompatibleFamily.pSubgroup_subconjugate_sylow P
    (coefficientBlockDefect_isPGroup basis ideal hD)
  have heq : (P : Subgroup G) = D :=
    Subgroup.eq_of_le_of_card_ge hPD (subgroupSubconjugate_card_le hDP)
  rw [heq]
  exact hD

omit [Group G] in
theorem brauer_eq_of_same {K : Type*} [Group K] [Fintype K]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup K) (hP : IsPGroup p P)
    (L : Subgroup K) (hCL : Subgroup.centralizer (P : Set K) ≤ L)
    (hLN : L ≤ Subgroup.normalizer (P : Set K)) (lb : FiniteIrreducibleCharacterBasis L)
    {γ₁ γ₂ : lb.index} (hsame : sameCoefficientBlock lb (localizedComplexIntegerRing ideal) γ₁ γ₂) :
    brauerNormalizerCharacterResidueHom ideal p P hP L hCL hLN lb γ₁ =
      brauerNormalizerCharacterResidueHom ideal p P hP L hCL hLN lb γ₂ := by
  apply RingHom.ext
  intro z
  change centralCharacterResidueHom lb ideal γ₁ _ = centralCharacterResidueHom lb ideal γ₂ _
  rw [(sameCoefficientBlock_iff_centralCharacterResidueHom_eq lb ideal γ₁ γ₂).mp hsame]

theorem oddCore_le_normalizer (S : Sylow 2 G) :
    BaseFourCentralizerStructure.ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ≤
      Subgroup.normalizer ((S : Subgroup G) : Set G) :=
  (BaseFourCentralizerStructure.ambientOddCore_le _).trans (Subgroup.centralizer_le_normalizer _)

end FullDefectLabels

open FullDefectLabels

@[expose] def InflatedLabel {G : Type*} [Group G] [Fintype G] {S E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (S : Set G))
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (S : Set G)))
    (eb : FiniteIrreducibleCharacterBasis E) (θ : eb.index) (θhat : nb.index) : Prop :=
  ∀ (v : S) (x : E), (nb.representation θhat).character
      ⟨(v : G) * x, (Subgroup.normalizer (S : Set G)).mul_mem (Subgroup.le_normalizer v.2)
        (hEN x.2)⟩ = (eb.representation θ).character x

theorem full_defect_block_canonical_sylow_centralizer_labels {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G))))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    (∀ θ : eb.index, ∃! θhat : nb.index, InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat) ∧
    (∀ χ : nb.index, ∃ (θ : eb.index) (θhat : nb.index),
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat ∧
        sameCoefficientBlock nb (localizedComplexIntegerRing ideal) θhat χ) ∧
    (∀ (θ₁ θ₂ : eb.index) (θhat₁ θhat₂ : nb.index),
      InflatedLabel (oddCore_le_normalizer S) nb eb θ₁ θhat₁ →
      InflatedLabel (oddCore_le_normalizer S) nb eb θ₂ θhat₂ →
      sameCoefficientBlock nb (localizedComplexIntegerRing ideal) θhat₁ θhat₂ → θ₁ = θ₂) ∧
    (∀ χ : nb.index, coefficientBlockDefect nb ideal 2 χ
      ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G)))) ∧
    (∀ (θ : eb.index) (θhat : nb.index), InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat →
      characterSubsetIdempotent nb (coefficientBlock nb (localizedComplexIntegerRing ideal) θhat) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion (oddCore_le_normalizer S))
            (complexCharacterIdempotent (eb.representation θ).character) ∧
        blockIdempotent ideal nb θhat =
          MonoidAlgebra.mapDomainRingHom (localizedComplexIntegerRing ideal)
            (Subgroup.inclusion (oddCore_le_normalizer S)) (blockIdempotent ideal eb θ) ∧
        MonoidAlgebra.mapRingHom _ (localizedComplexIntegerRing ideal).subtype
            (blockIdempotent ideal eb θ) =
          complexCharacterIdempotent (eb.representation θ).character) ∧
    (∀ (θ : eb.index) (θhat : nb.index), InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat →
      ∃ B : basis.index, brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G)
          S.isPGroup' (Subgroup.normalizer ((S : Subgroup G) : Set G))
          (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat =
            centralCharacterResidueHom basis ideal B ∧
        coefficientBlockDefect basis ideal 2 B S) ∧
    (∀ B : basis.index, coefficientBlockDefect basis ideal 2 B S →
      ∃ (θ : eb.index) (θhat : nb.index), InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat ∧
        brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
          (Subgroup.normalizer ((S : Subgroup G) : Set G))
          (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat =
            centralCharacterResidueHom basis ideal B) ∧
    (∀ (θ₁ θ₂ : eb.index) (θhat₁ θhat₂ : nb.index),
      InflatedLabel (oddCore_le_normalizer S) nb eb θ₁ θhat₁ →
      InflatedLabel (oddCore_le_normalizer S) nb eb θ₂ θhat₂ →
      brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
          (Subgroup.normalizer ((S : Subgroup G) : Set G))
          (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat₁ =
        brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
          (Subgroup.normalizer ((S : Subgroup G) : Set G))
          (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat₂ → θ₁ = θ₂) ∧
    (∀ (θ : eb.index) (θhat : nb.index), (eb.representation θ).character = 1 →
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat →
      brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
          (Subgroup.normalizer ((S : Subgroup G) : Set G))
          (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat =
        centralCharacterResidueHom basis ideal principal) := by
  have hstruct :=
    BaseFourCentralizerStructure.sylow_and_base_four_group_centralizer_structure n hn S e
  obtain ⟨d, hd⟩ := hstruct.normalizer_direct
  obtain ⟨dW, hdW⟩ := hstruct.centralizer_direct
  have hEodd : Odd (Nat.card (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) :=
    BaseFourCentralizerStructure.ambientOddCore_odd _
  have hE2 : ¬ 2 ∣ Nat.card (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G))) := fun h =>
    (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr h)
  have hSE : ∀ v ∈ (S : Subgroup G), ∀ x ∈ (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G))), x * v = v * x := fun v hv x hx =>
    Subgroup.mem_centralizer_iff.mp (hstruct.normalizer_commuting hv) x hx
  have hmulmem : ∀ (v : (S : Subgroup G)) (x : (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))),
      (v : G) * x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := fun v x =>
    (Subgroup.normalizer ((S : Subgroup G) : Set G)).mul_mem (Subgroup.le_normalizer v.2)
      ((oddCore_le_normalizer S) x.2)
  have hNprod : ∀ h : (Subgroup.normalizer ((S : Subgroup G) : Set G)),
      ∃ v ∈ (S : Subgroup G), ∃ x ∈ (BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))), (h : G) = v * x := by
    intro h
    refine ⟨(d.symm h).1, (d.symm h).1.2, (d.symm h).2, (d.symm h).2.2, ?_⟩
    have hdh := hd (d.symm h)
    rw [MulEquiv.apply_symm_apply] at hdh
    exact hdh
  have hWprod : ∀ g ∈ (Subgroup.centralizer ((S : Subgroup G) : Set G)),
      ∃ a ∈ modelCenter S e, ∃ x ∈ (BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))), g = a * x := by
    intro g hg
    refine ⟨(dW.symm ⟨g, hg⟩).1, (dW.symm ⟨g, hg⟩).1.2, (dW.symm ⟨g, hg⟩).2,
      (dW.symm ⟨g, hg⟩).2.2, ?_⟩
    have hdg := hdW (dW.symm ⟨g, hg⟩)
    rw [MulEquiv.apply_symm_apply] at hdg
    exact hdg
  have hconj : ∀ k : (Subgroup.normalizer ((S : Subgroup G) : Set G)),
      ∃ y : (BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      ∀ x : (BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      k * Subgroup.inclusion (oddCore_le_normalizer S) x * k⁻¹ =
        Subgroup.inclusion (oddCore_le_normalizer S) (y * x * y⁻¹) := by
    intro k
    obtain ⟨v, hv, y, hy, hk⟩ := hNprod k
    refine ⟨⟨y, hy⟩, fun x => Subtype.ext ?_⟩
    change (k : G) * x * (k : G)⁻¹ = y * x * y⁻¹
    have hyx : y * (x : G) * y⁻¹ ∈ (BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hy x.2) (Subgroup.inv_mem _ hy)
    rw [hk]
    calc v * y * x * (v * y)⁻¹ = v * (y * x * y⁻¹) * v⁻¹ := by group
      _ = (y * x * y⁻¹) * v * v⁻¹ := by rw [← hSE v hv _ hyx]
      _ = y * x * y⁻¹ := by group
  have hcent := inclusion_central_of_conj (oddCore_le_normalizer S) hconj
  have hZS : modelCenter S e ≤ (S : Subgroup G) := by
    rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  have hZp : IsPGroup 2 (modelCenter S e) := S.isPGroup'.to_le hZS
  have hZW : ∀ a ∈ modelCenter S e, a ∈ (Subgroup.centralizer ((S : Subgroup G) : Set G)) := by
    intro a ha
    have h := (dW (⟨a, ha⟩, 1)).2
    rw [hdW] at h
    simpa using h
  have hZN : modelCenter S e ≤ (Subgroup.normalizer ((S : Subgroup G) : Set G)) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (hZW a ha)
  have hZc : ∀ (a : modelCenter S e) (k : (Subgroup.normalizer ((S : Subgroup G) : Set G))),
      toK hZN a * k = k * toK hZN a := by
    intro a k
    apply Subtype.ext
    obtain ⟨v, hv, x, hx, hk⟩ := hNprod k
    change (a : G) * k = k * a
    rw [hk]
    have hav : v * a = a * v := Subgroup.mem_centralizer_iff.mp (hZW a a.2) v hv
    have hax : x * a = a * x :=
      Subgroup.mem_centralizer_iff.mp (hstruct.centralizer_commuting a.2) x hx
    calc (a : G) * (v * x) = (a * v) * x := by group
      _ = (v * a) * x := by rw [hav]
      _ = v * (a * x) := by group
      _ = v * (x * a) := by rw [hax]
      _ = v * x * a := by group
  have hZE : modelCenter S e ⊓ (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G))) = ⊥ := hstruct.centralizer_disjoint
  let π : (Subgroup.normalizer ((S : Subgroup G) : Set G)) →*
      (BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))) :=
    (MonoidHom.snd _ _).comp d.symm.toMonoidHom
  have hπ : ∀ (v : (S : Subgroup G)) (x : (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))), π ⟨(v : G) * x, hmulmem v x⟩ = x := by
    intro v x
    have hdvx : d (v, x) = ⟨(v : G) * x, hmulmem v x⟩ := Subtype.ext (hd (v, x))
    change (d.symm ⟨(v : G) * x, hmulmem v x⟩).2 = x
    rw [← hdvx, MulEquiv.symm_apply_apply]
  have hπsurj : Function.Surjective π := fun x => ⟨d (1, x), by
    change (d.symm (d (1, x))).2 = x
    rw [MulEquiv.symm_apply_apply]⟩
  have hinfl : ∀ θ : eb.index, ∃ θhat : nb.index,
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat := by
    intro θ
    have hirr : (inflatedFiniteComplexRepresentation π (eb.representation θ)).IsIrreducible :=
      CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective π hπsurj _ (eb.irreducible θ)
    obtain ⟨θhat, hθhat⟩ := finiteIrreducibleCharacterBasis_contains_irreducible nb _ hirr
    refine ⟨θhat, fun v x => ?_⟩
    rw [hθhat, inflatedFiniteComplexRepresentation_character, Function.comp_apply]
    exact congrArg (eb.representation θ).character (hπ v x)
  have hinfl_unique : ∀ (θ : eb.index) (θhat₁ θhat₂ : nb.index),
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat₁ →
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat₂ → θhat₁ = θhat₂ := by
    intro θ θhat₁ θhat₂ h₁ h₂
    apply nb.distinct
    funext k
    obtain ⟨v, hv, x, hx, hk⟩ := hNprod k
    have hk' : k = ⟨((⟨v, hv⟩ : (S : Subgroup G)) : G) *
        ((⟨x, hx⟩ : (BaseFourCentralizerStructure.ambientOddCore
          (Subgroup.centralizer ((S : Subgroup G) : Set G)))) : G),
        hmulmem ⟨v, hv⟩ ⟨x, hx⟩⟩ := Subtype.ext hk
    subst hk'
    exact (h₁ ⟨v, hv⟩ ⟨x, hx⟩).trans (h₂ ⟨v, hv⟩ ⟨x, hx⟩).symm
  have hres : ∀ (θ : eb.index) (θhat : nb.index),
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat →
      ∀ x : (BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      (nb.representation θhat).character (Subgroup.inclusion (oddCore_le_normalizer S) x) =
        (eb.representation θ).character x := by
    intro θ θhat h x
    have hk : Subgroup.inclusion (oddCore_le_normalizer S) x =
        ⟨((1 : (S : Subgroup G)) : G) * x, hmulmem 1 x⟩ := Subtype.ext (one_mul _).symm
    rw [hk]
    exact h 1 x
  have hmem_supp : ∀ (θ : eb.index) (θhat : nb.index),
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat →
      θhat ∈ embSupport (oddCore_le_normalizer S) nb eb θ := by
    intro θ θhat h
    rw [mem_embSupport]
    unfold embIdem
    rw [scalar_inclusion_of_character_eq (oddCore_le_normalizer S) nb eb (hres θ θhat h),
      ← characterSubsetIdempotent_singleton, scalar_characterSubsetIdempotent,
      ite_eq_left (Finset.mem_singleton_self θ)]
  have hP : IsPGroup 2 ((S : Subgroup G).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))) := S.isPGroup'.comap_subtype
  have hconst : ∀ (θ : eb.index) (χ χ' : nb.index),
      χ ∈ embSupport (oddCore_le_normalizer S) nb eb θ →
      χ' ∈ embSupport (oddCore_le_normalizer S) nb eb θ →
      centralCharacterResidueHom nb ideal χ = centralCharacterResidueHom nb ideal χ' := by
    intro θ χ χ' hχ hχ'
    apply RingHom.ext
    intro z
    let z' := commonCentralCoefficientInclusion (localizedComplexIntegerRing ideal)
      (Subgroup.centralizer ((((S : Subgroup G).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))) :
          Subgroup (Subgroup.normalizer ((S : Subgroup G) : Set G))) :
        Set (Subgroup.normalizer ((S : Subgroup G) : Set G))))
      ⟨centralSubgroupCoefficientProjection _ _ z, normalCentralizer_projection_common _ _ z⟩
    have hproj := commonCentralCoefficientInclusion_projection
      (localizedComplexIntegerRing ideal) (Subgroup.centralizer ((((S : Subgroup G).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))) :
          Subgroup (Subgroup.normalizer ((S : Subgroup G) : Set G))) :
        Set (Subgroup.normalizer ((S : Subgroup G) : Set G))))
      ⟨centralSubgroupCoefficientProjection _ _ z, normalCentralizer_projection_common _ _ z⟩
    rw [normal_p_central_residue_determined_by_projection nb ideal 2 _ hP z z' hproj.symm χ,
      normal_p_central_residue_determined_by_projection nb ideal 2 _ hP z z' hproj.symm χ']
    apply residue_eq_of_scalar_eq hZN (oddCore_le_normalizer S) ideal hZp hZE hZc hcent nb
    · intro y hy
      rw [scalar_embedded_of_scalar_eq_one (oddCore_le_normalizer S) nb eb hcent
          ((mem_embSupport (oddCore_le_normalizer S) nb eb θ χ).mp hχ) y hy,
        scalar_embedded_of_scalar_eq_one (oddCore_le_normalizer S) nb eb hcent
          ((mem_embSupport (oddCore_le_normalizer S) nb eb θ χ').mp hχ') y hy]
    · intro k hk
      have hkC : k ∈ Subgroup.centralizer ((((S : Subgroup G).subgroupOf
          (Subgroup.normalizer ((S : Subgroup G) : Set G))) :
            Subgroup (Subgroup.normalizer ((S : Subgroup G) : Set G))) :
          Set (Subgroup.normalizer ((S : Subgroup G) : Set G))) := by
        by_contra hnot
        apply hk
        exact embedded_coeff_zero _ _ _ fun ⟨c, hc⟩ => hnot (hc ▸ c.2)
      rw [mem_centralizer_subgroupOf_iff Subgroup.le_normalizer k] at hkC
      exact hWprod k hkC
  have hblock : ∀ (θ : eb.index) (θ' : nb.index),
      θ' ∈ embSupport (oddCore_le_normalizer S) nb eb θ →
      coefficientBlock nb (localizedComplexIntegerRing ideal) θ' =
        embSupport (oddCore_le_normalizer S) nb eb θ := by
    intro θ θ' hθ'
    apply Finset.Subset.antisymm
    · exact coefficientBlock_subset_admissible nb _ _
        (embSupport_admissible (oddCore_le_normalizer S) nb eb hcent ideal 2 hE2 θ) θ' hθ'
    · intro χ hχ
      rw [coefficientBlock_mem_iff, sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
      exact hconst θ θ' χ hθ' hχ
  have hlabel_inj : ∀ (θ₁ θ₂ : eb.index) (θhat₁ θhat₂ : nb.index),
      InflatedLabel (oddCore_le_normalizer S) nb eb θ₁ θhat₁ →
      InflatedLabel (oddCore_le_normalizer S) nb eb θ₂ θhat₂ →
      sameCoefficientBlock nb (localizedComplexIntegerRing ideal) θhat₁ θhat₂ → θ₁ = θ₂ := by
    intro θ₁ θ₂ θhat₁ θhat₂ h₁ h₂ hsame
    have hθhat₂ : θhat₂ ∈ embSupport (oddCore_le_normalizer S) nb eb θ₁ := by
      rw [← hblock θ₁ θhat₁ (hmem_supp θ₁ θhat₁ h₁), coefficientBlock_mem_iff]
      exact hsame
    exact embSupport_unique (oddCore_le_normalizer S) nb eb hcent hθhat₂ (hmem_supp θ₂ θhat₂ h₂)
  have hcover : ∀ χ : nb.index, ∃ (θ : eb.index) (θhat : nb.index),
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat ∧
        sameCoefficientBlock nb (localizedComplexIntegerRing ideal) θhat χ := by
    intro χ
    obtain ⟨θ, hθ⟩ := exists_mem_embSupport (oddCore_le_normalizer S) nb eb hcent χ
    obtain ⟨θhat, h⟩ := hinfl θ
    refine ⟨θ, θhat, h, ?_⟩
    rw [← coefficientBlock_mem_iff, hblock θ θhat (hmem_supp θ θhat h)]
    exact hθ
  let SN : Sylow 2 (Subgroup.normalizer ((S : Subgroup G) : Set G)) :=
    S.subtype Subgroup.le_normalizer
  have : SN.toSubgroup.Normal := by
    change ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal
    infer_instance
  have hdef : ∀ χ : nb.index, coefficientBlockDefect nb ideal 2 χ
      ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))) := fun χ =>
    coefficientBlockDefect_of_normal_sylow nb ideal 2 SN χ
  obtain ⟨himg, hmapdef, hsurj, hinj⟩ :=
    defect_normalizer_brauer_correspondence basis ideal 2 (S : Subgroup G) S.isPGroup' nb
  have hsingle : ∀ θ : eb.index,
      coefficientBlock eb (localizedComplexIntegerRing ideal) θ = {θ} := fun θ =>
    (full_prime_part_character_degree_singleton_block_singular_vanishing eb ideal 2 θ (by
      rw [Nat.factorization_eq_zero_of_not_dvd hE2, pow_zero]
      exact one_dvd _)).1
  have hblockE : ∀ θ : eb.index,
      MonoidAlgebra.mapRingHom _ (localizedComplexIntegerRing ideal).subtype
        (blockIdempotent ideal eb θ) = complexCharacterIdempotent (eb.representation θ).character :=
    fun θ => by rw [blockIdempotent_map_subtype, hsingle θ, characterSubsetIdempotent_singleton]
  refine ⟨fun θ => ?_, hcover, hlabel_inj, hdef, fun θ θhat h => ?_, fun θ θhat h => ?_,
    fun B hB => ?_, fun θ₁ θ₂ θhat₁ θhat₂ h₁ h₂ hBr => ?_, fun θ θhat h1 h => ?_⟩
  · obtain ⟨θhat, h⟩ := hinfl θ
    exact ⟨θhat, h, fun θhat' h' => hinfl_unique θ θhat' θhat h' h⟩
  · have hC : characterSubsetIdempotent nb
          (coefficientBlock nb (localizedComplexIntegerRing ideal) θhat) =
        MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion (oddCore_le_normalizer S))
          (complexCharacterIdempotent (eb.representation θ).character) := by
      rw [hblock θ θhat (hmem_supp θ θhat h),
        ← embIdem_eq_support (oddCore_le_normalizer S) nb eb hcent θ]
      rfl
    refine ⟨hC, ?_, hblockE θ⟩
    apply groupAlgebraCoefficientEmbedding_injective (localizedComplexIntegerRing ideal)
    rw [blockIdempotent_map_subtype, hC, subtype_mapDomain, hblockE]
  · obtain ⟨B, hB⟩ := himg θhat
    exact ⟨B, hB, hmapdef θhat B (hdef θhat) hB⟩
  · obtain ⟨χ, -, hχ⟩ := hsurj B hB
    obtain ⟨θ, θhat, h, hsame⟩ := hcover χ
    exact ⟨θ, θhat, h, (brauer_eq_of_same ideal 2 _ S.isPGroup' _ _ le_rfl nb hsame).trans hχ⟩
  · exact hlabel_inj θ₁ θ₂ θhat₁ θhat₂ h₁ h₂ (hinj θhat₁ θhat₂ (hdef θhat₁) (hdef θhat₂) hBr)
  · have hchar : (nb.representation θhat).character = 1 := by
      funext k
      obtain ⟨v, hv, x, hx, hk⟩ := hNprod k
      have hk' : k = ⟨((⟨v, hv⟩ : (S : Subgroup G)) : G) *
          ((⟨x, hx⟩ : (BaseFourCentralizerStructure.ambientOddCore
            (Subgroup.centralizer ((S : Subgroup G) : Set G)))) : G),
          hmulmem ⟨v, hv⟩ ⟨x, hx⟩⟩ := Subtype.ext hk
      subst hk'
      exact (h ⟨v, hv⟩ ⟨x, hx⟩).trans (congrFun h1 ⟨x, hx⟩)
    exact brauerNormalizer_principal_residue_image basis ideal 2 (S : Subgroup G) S.isPGroup' _
      (Subgroup.centralizer_le_normalizer _) le_rfl nb principal hprincipal θhat hchar

end CFSG.Wreathed
