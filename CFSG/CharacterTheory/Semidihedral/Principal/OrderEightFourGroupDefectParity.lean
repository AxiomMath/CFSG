module

public import CFSG.CharacterTheory.Semidihedral.Principal.NormalAbelianCentralizerOrbitIdempotents
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.BlockOrbits
  CFSG.Semidihedral.Principal.OrbitIdempotents

namespace FourGroupParity

variable {H : Type*} [Group H]

@[expose] def nonidentityConjEquiv (V : Subgroup H) [V.Normal] (h : H) :
    Equiv.Perm {v : V // v ≠ 1} where
  toFun v := ⟨⟨h * v.1 * h⁻¹, Subgroup.Normal.conj_mem inferInstance _ v.1.2 h⟩,
    fun h1 => v.2 (Subtype.ext (by
      have hval : h * (v.1 : H) * h⁻¹ = 1 := congrArg Subtype.val h1
      exact conj_eq_one_iff.mp hval))⟩
  invFun v := ⟨⟨h⁻¹ * v.1 * h, by
      have hmem := Subgroup.Normal.conj_mem (inferInstance : V.Normal) _ v.1.2 h⁻¹
      simpa only [inv_inv] using hmem⟩,
    fun h1 => v.2 (Subtype.ext (by
      have hval : h⁻¹ * (v.1 : H) * h = 1 := congrArg Subtype.val h1
      calc (v.1 : H) = h * (h⁻¹ * v.1 * h) * h⁻¹ := by group
        _ = 1 := by rw [hval]; group))⟩
  left_inv v := Subtype.ext (Subtype.ext (by dsimp only; group))
  right_inv v := Subtype.ext (Subtype.ext (by dsimp only; group))

omit [Group H] in
theorem nonidentityConjEquiv_apply {H : Type*} [Group H] (V : Subgroup H) [V.Normal] (h : H)
    (v : {v : V // v ≠ 1}) : ((nonidentityConjEquiv V h v).1 : H) = h * v.1 * h⁻¹ := rfl

@[expose] def nonidentityConj (V : Subgroup H) [V.Normal] : H →* Equiv.Perm {v : V // v ≠ 1} where
  toFun := nonidentityConjEquiv V
  map_one' := Equiv.ext fun v => Subtype.ext (Subtype.ext (by
    rw [nonidentityConjEquiv_apply]
    change 1 * (v.1 : H) * 1⁻¹ = v.1
    group))
  map_mul' h k := Equiv.ext fun v => Subtype.ext (Subtype.ext (by
    rw [Equiv.Perm.mul_apply, nonidentityConjEquiv_apply, nonidentityConjEquiv_apply,
      nonidentityConjEquiv_apply]
    group))

omit [Group H] in
theorem nonidentityConj_apply {H : Type*} [Group H] (V : Subgroup H) [V.Normal] (h : H)
    (v : {v : V // v ≠ 1}) : ((nonidentityConj V h v).1 : H) = h * v.1 * h⁻¹ := rfl

theorem mem_ker_nonidentityConj (V : Subgroup H) [V.Normal] (h : H) :
    h ∈ (nonidentityConj V).ker ↔ h ∈ Subgroup.centralizer (V : Set H) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 v hv
    by_cases hv1 : (⟨v, hv⟩ : V) = 1
    · have hv1' : v = 1 := congrArg Subtype.val hv1
      rw [hv1', one_mul, mul_one]
    · have hfix := congrArg
        (fun f : Equiv.Perm {v : V // v ≠ 1} => ((f ⟨⟨v, hv⟩, hv1⟩).1 : H)) h1
      rw [nonidentityConj_apply] at hfix
      change h * v * h⁻¹ = v at hfix
      calc v * h = h * v * h⁻¹ * h := by rw [hfix]
        _ = h * v := by group
  · intro hc
    apply Equiv.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    rw [nonidentityConj_apply]
    change h * (v.1 : H) * h⁻¹ = v.1
    rw [← hc v.1 v.1.2]
    group

theorem ker_nonidentityConj (V : Subgroup H) [V.Normal] :
    (nonidentityConj V).ker = Subgroup.centralizer (V : Set H) :=
  Subgroup.ext (mem_ker_nonidentityConj V)

variable [Finite H]

theorem card_nonidentity (V : Subgroup H) (hV : IsKleinFour V) :
    Nat.card {v : V // v ≠ 1} = 3 := by
  have h4 : Nat.card V = 4 := hV.card_four
  have hopt := Nat.card_congr (Equiv.optionSubtypeNe (1 : V))
  rw [Finite.card_option, h4] at hopt
  omega

theorem index_centralizer_dvd_six (V : Subgroup H) [V.Normal] (hV : IsKleinFour V) :
    (Subgroup.centralizer (V : Set H)).index ∣ 6 := by
  rw [← ker_nonidentityConj V, Subgroup.index_ker]
  have h6 : Nat.card (Equiv.Perm {v : V // v ≠ 1}) = 6 := by
    rw [Nat.card_perm, card_nonidentity V hV]
    rfl
  rw [← h6]
  exact Subgroup.card_subgroup_dvd_card _

omit [Finite H] in
theorem card_centralizer_eq (V E : Subgroup H) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hEW : E ≤ Subgroup.centralizer (V : Set H)) (hVE : V ⊓ E = ⊥)
    (hW : ∀ w ∈ Subgroup.centralizer (V : Set H), ∃ a ∈ V, ∃ x ∈ E, w = a * x) :
    Nat.card (Subgroup.centralizer (V : Set H)) = Nat.card V * Nat.card E := by
  rw [← Nat.card_prod]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun ae : V × E => (⟨ae.1 * ae.2, Subgroup.mul_mem _
    (le_centralizer_self_of_comm V hVab ae.1.2) (hEW ae.2.2)⟩ :
      Subgroup.centralizer (V : Set H))) ⟨?_, ?_⟩
  · rintro ⟨a, x⟩ ⟨b, y⟩ hab
    have hval : (a : H) * x = b * y := congrArg Subtype.val hab
    have hmem : (b : H)⁻¹ * a ∈ V ⊓ E := by
      refine ⟨V.mul_mem (V.inv_mem b.2) a.2, ?_⟩
      have hba : (b : H)⁻¹ * a = y * (x : H)⁻¹ := by
        calc (b : H)⁻¹ * a = (b : H)⁻¹ * (a * x) * (x : H)⁻¹ := by group
          _ = (b : H)⁻¹ * (b * y) * (x : H)⁻¹ := by rw [hval]
          _ = y * (x : H)⁻¹ := by group
      rw [hba]
      exact E.mul_mem y.2 (E.inv_mem x.2)
    rw [hVE, Subgroup.mem_bot] at hmem
    have hab' : (a : H) = b := by
      calc (a : H) = b * ((b : H)⁻¹ * a) := by group
        _ = b := by rw [hmem, mul_one]
    have hxy : (x : H) = y := by
      rw [hab'] at hval
      exact mul_left_cancel hval
    exact Prod.ext (Subtype.ext hab') (Subtype.ext hxy)
  · rintro ⟨w, hw⟩
    obtain ⟨a, ha, x, hx, rfl⟩ := hW w hw
    exact ⟨(⟨a, ha⟩, ⟨x, hx⟩), rfl⟩

omit [Finite H] in
theorem two_dvd_index_centralizer (V E : Subgroup H) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hEW : E ≤ Subgroup.centralizer (V : Set H)) (hVE : V ⊓ E = ⊥)
    (hW : ∀ w ∈ Subgroup.centralizer (V : Set H), ∃ a ∈ V, ∃ x ∈ E, w = a * x)
    (hV4 : Nat.card V = 4) (hEodd : Odd (Nat.card E)) (Q : Subgroup H) (hQ : Nat.card Q = 8) :
    2 ∣ (Subgroup.centralizer (V : Set H)).index := by
  have hcard := card_centralizer_eq V E hVab hEW hVE hW
  have hH := Subgroup.card_mul_index (Subgroup.centralizer (V : Set H))
  have h8 : 8 ∣ Nat.card H := hQ ▸ Subgroup.card_subgroup_dvd_card Q
  rw [← hH, hcard, hV4] at h8
  have h2 : 2 ∣ Nat.card E * (Subgroup.centralizer (V : Set H)).index := by
    have h8' : 4 * 2 ∣ 4 * (Nat.card E * (Subgroup.centralizer (V : Set H)).index) := by
      rw [← mul_assoc]
      exact h8
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h8'
  rcases Nat.prime_two.dvd_mul.mp h2 with hE | hidx
  · exact absurd (even_iff_two_dvd.mpr hE) (Nat.not_even_iff_odd.mpr hEodd)
  · exact hidx

theorem index_centralizer_eq (V E : Subgroup H) [V.Normal] (hV : IsKleinFour V)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hEW : E ≤ Subgroup.centralizer (V : Set H)) (hVE : V ⊓ E = ⊥)
    (hW : ∀ w ∈ Subgroup.centralizer (V : Set H), ∃ a ∈ V, ∃ x ∈ E, w = a * x)
    (hEodd : Odd (Nat.card E)) (Q : Subgroup H) (hQ : Nat.card Q = 8) :
    (Subgroup.centralizer (V : Set H)).index = 2 ∨
      (Subgroup.centralizer (V : Set H)).index = 6 := by
  have h6 := index_centralizer_dvd_six V hV
  have h2 := two_dvd_index_centralizer V E hVab hEW hVE hW hV.card_four hEodd Q hQ
  have hle := Nat.le_of_dvd (by norm_num) h6
  set n := (Subgroup.centralizer (V : Set H)).index with hn
  interval_cases n <;> omega

theorem quotient_centralizer_iso (V : Subgroup H) [V.Normal] (hV : IsKleinFour V)
    (hidx : (Subgroup.centralizer (V : Set H)).index = 2 ∨
      (Subgroup.centralizer (V : Set H)).index = 6) :
    Nonempty (H ⧸ Subgroup.centralizer (V : Set H) ≃* Multiplicative (ZMod 2)) ∨
      Nonempty (H ⧸ Subgroup.centralizer (V : Set H) ≃* Equiv.Perm (Fin 3)) := by
  rcases hidx with h2 | h6
  · left
    refine ⟨mulEquivOfPrimeCardEq (p := 2) h2 ?_⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  · right
    have hsurj : Function.Surjective (nonidentityConj V) := by
      rw [← MonoidHom.range_eq_top]
      apply Subgroup.eq_top_of_card_eq
      rw [← Subgroup.index_ker, ker_nonidentityConj V, h6, Nat.card_perm, card_nonidentity V hV]
      rfl
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (ker_nonidentityConj V)).symm.trans
      ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).trans
        (Finite.equivFinOfCardEq (card_nonidentity V hV)).permCongrHom)⟩

omit [Finite H]
variable [Fintype H]

@[expose] noncomputable def conjLabel (E : Subgroup H) [E.Normal]
    (eb : FiniteIrreducibleCharacterBasis E) (h : H) (μ : eb.index) : eb.index :=
  (conjugateLabel_existsUnique E eb h μ).exists.choose

theorem conjLabel_spec (E : Subgroup H) [E.Normal] (eb : FiniteIrreducibleCharacterBasis E)
    (h : H) (μ : eb.index) : ConjugateLabel E eb h μ (conjLabel E eb h μ) :=
  (conjugateLabel_existsUnique E eb h μ).exists.choose_spec

theorem conjLabel_eq_iff (E : Subgroup H) [E.Normal] (eb : FiniteIrreducibleCharacterBasis E)
    (h : H) (μ μ' : eb.index) : conjLabel E eb h μ = μ' ↔ ConjugateLabel E eb h μ μ' :=
  ⟨fun h' => h' ▸ conjLabel_spec E eb h μ,
    fun h' => (conjugateLabel_existsUnique E eb h μ).unique (conjLabel_spec E eb h μ) h'⟩

omit [Fintype H] in
theorem conjugateLabel_one {H : Type*} [Group H] [Fintype H] (E : Subgroup H)
    (eb : FiniteIrreducibleCharacterBasis E) (μ : eb.index) : ConjugateLabel E eb 1 μ μ := by
  intro x y hxy
  have hyx : y = x := Subtype.ext (by rw [hxy]; group)
  rw [hyx]

@[expose, instance_reducible] noncomputable def labelAction (E : Subgroup H) [E.Normal]
    (eb : FiniteIrreducibleCharacterBasis E) : MulAction H eb.index where
  smul := conjLabel E eb
  one_smul μ := (conjLabel_eq_iff E eb 1 μ μ).mpr (conjugateLabel_one E eb μ)
  mul_smul h k μ := (conjLabel_eq_iff E eb (h * k) μ _).mpr
    (conjugateLabel_mul E eb (conjLabel_spec E eb k μ) (conjLabel_spec E eb h _))

@[expose] noncomputable def labelStabilizer (E : Subgroup H) [E.Normal]
    (eb : FiniteIrreducibleCharacterBasis E) (μ : eb.index) : Subgroup H :=
  @MulAction.stabilizer H eb.index _ (labelAction E eb) μ

theorem mem_labelStabilizer (E : Subgroup H) [E.Normal] (eb : FiniteIrreducibleCharacterBasis E)
    (μ : eb.index) (h : H) : h ∈ labelStabilizer E eb μ ↔ ConjugateLabel E eb h μ μ :=
  conjLabel_eq_iff E eb h μ μ

theorem card_orbit_eq_index (E : Subgroup H) [E.Normal] (eb : FiniteIrreducibleCharacterBasis E)
    (μ : eb.index) :
    (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card =
      (labelStabilizer E eb μ).index := by
  let := labelAction E eb
  change _ = (MulAction.stabilizer H μ).index
  rw [MulAction.index_stabilizer, ← Set.ncard_coe_finset]
  congr 1
  ext μ'
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, (conjLabel_eq_iff E eb h μ μ').mpr hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, (conjLabel_eq_iff E eb h μ μ').mp hh⟩

theorem orbit_eq_of_mem (E : Subgroup H) [E.Normal] (eb : FiniteIrreducibleCharacterBasis E)
    {μ μ' : eb.index} (hμ' : ∃ h : H, ConjugateLabel E eb h μ μ') :
    (Finset.univ.filter fun ν => ∃ h : H, ConjugateLabel E eb h μ' ν) =
      (Finset.univ.filter fun ν => ∃ h : H, ConjugateLabel E eb h μ ν) := by
  obtain ⟨h₀, hh₀⟩ := hμ'
  ext ν
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h * h₀, conjugateLabel_mul E eb hh₀ hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨h * h₀⁻¹, conjugateLabel_mul E eb (conjugateLabel_inv E eb hh₀) hh⟩

theorem centralizer_le_labelStabilizer (V E : Subgroup H) [E.Normal]
    (hEW : E ≤ Subgroup.centralizer (V : Set H))
    (hW : ∀ w ∈ Subgroup.centralizer (V : Set H), ∃ a ∈ V, ∃ x ∈ E, w = a * x)
    (eb : FiniteIrreducibleCharacterBasis E) (μ : eb.index) :
    Subgroup.centralizer (V : Set H) ≤ labelStabilizer E eb μ := by
  intro w hw
  rw [mem_labelStabilizer]
  obtain ⟨a, ha, y, hy, rfl⟩ := hW w hw
  intro x x' hxx'
  have hcomm : ∀ z ∈ E, a * z = z * a := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (hEW hz) a ha)
  have hx' : x' = (⟨y, hy⟩ : E) * x * (⟨y, hy⟩ : E)⁻¹ := by
    apply Subtype.ext
    have hyx : y * (x : H) * y⁻¹ ∈ E := E.mul_mem (E.mul_mem hy x.2) (E.inv_mem hy)
    change (x' : H) = y * x * y⁻¹
    rw [hxx']
    calc a * y * x * (a * y)⁻¹ = a * (y * x * y⁻¹) * a⁻¹ := by group
      _ = (y * x * y⁻¹) * a * a⁻¹ := by rw [hcomm _ hyx]
      _ = y * x * y⁻¹ := by group
  rw [hx']
  exact Representation.char_conj (eb.representation μ).representation x ⟨y, hy⟩

theorem coefficientBlockDefect_of_subgroupsConjugate (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {p : ℕ} [Fact p.Prime]
    {χ : basis.index} {D D' : Subgroup H} (hD : coefficientBlockDefect basis ideal p χ D)
    (hDD' : subgroupsConjugate D D') : coefficientBlockDefect basis ideal p χ D' := by
  obtain ⟨X, hX, hXval⟩ := hD.1
  refine ⟨⟨X, classDefect_of_subgroupsConjugate p hX hDD', hXval⟩, fun Y other hY hYval => ?_⟩
  exact subgroupSubconjugate_trans
    (subgroupsConjugate_subconjugate (subgroupsConjugate_symm hDD')) (hD.2 Y other hY hYval)

omit [Fintype H] in
theorem natCast_eq_one_of_odd {k : Type*} [CommRing k] [CharP k 2] {n : ℕ} (hn : Odd n) :
    (n : k) = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  push_cast
  rw [h2, zero_mul, zero_add]

theorem odd_degree (E : Subgroup H) (eb : FiniteIrreducibleCharacterBasis E)
    (hEodd : Odd (Nat.card E)) (μ : eb.index) :
    Odd (Module.finrank ℂ (eb.representation μ).vector) := by
  let : (eb.representation μ).representation.IsIrreducible := eb.irreducible μ
  exact Odd.of_dvd_nat hEodd (CFSG.Theory.Character.irreducible_dimension_dvd_group_order
    (eb.representation μ).representation)

theorem character_one_eq (E : Subgroup H) (eb : FiniteIrreducibleCharacterBasis E)
    (μ : eb.index) : (eb.representation μ).character 1 =
      (Module.finrank ℂ (eb.representation μ).vector : ℂ) := by
  rw [FiniteComplexRepresentation.character, Representation.char_one]

theorem term_mem (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (E : Subgroup H)
    (eb : FiniteIrreducibleCharacterBasis E) (hEodd : Odd (Nat.card E)) (μ : eb.index) (x : E) :
    (eb.representation μ).character 1 / (Nat.card E : ℂ) * (eb.representation μ).character x⁻¹ ∈
      localizedComplexIntegerRing ideal := by
  have hE2 : ¬ 2 ∣ Nat.card E := fun h => (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr h)
  exact (localizedComplexIntegerRing ideal).mul_mem
    (degree_div_card_mem_localizedComplexIntegerRing ideal 2 _ (by
      rw [Nat.factorization_eq_zero_of_not_dvd hE2, pow_zero]
      exact one_dvd _))
    (complexAlgebraicInteger_mem_localized_ring ideal
      ⟨_, (mem_integralClosure_iff ℤ ℂ).mpr (finite_character_value_isIntegral _ x⁻¹)⟩)

theorem orbitSum_coeff (E : Subgroup H) (eb : FiniteIrreducibleCharacterBasis E)
    (Ω : Finset eb.index) (x : E) :
    (∑ μ' ∈ Ω, MonoidAlgebra.mapDomainRingHom ℂ E.subtype
        (complexCharacterIdempotent (eb.representation μ').character)).coeff (x : H) =
      ∑ μ' ∈ Ω, (eb.representation μ').character 1 / (Nat.card E : ℂ) *
        (eb.representation μ').character x⁻¹ := by
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply' (s := Ω)]
  refine Finset.sum_congr rfl fun μ' _ => ?_
  rw [show (x : H) = E.subtype x from rfl, embedded_coeff _ (Subgroup.subtype_injective E),
    complexCharacterIdempotent_coeff]

theorem orbitSum_coeff_zero (E : Subgroup H) (eb : FiniteIrreducibleCharacterBasis E)
    (Ω : Finset eb.index) (y : H) (hy : y ∉ E) :
    (∑ μ' ∈ Ω, MonoidAlgebra.mapDomainRingHom ℂ E.subtype
        (complexCharacterIdempotent (eb.representation μ').character)).coeff y = 0 := by
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply' (s := Ω)]
  refine Finset.sum_eq_zero fun μ' _ => ?_
  apply embedded_coeff_zero
  rintro ⟨x, rfl⟩
  exact hy x.2

theorem odd_orbit_residue_ne_zero (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (E : Subgroup H)
    (eb : FiniteIrreducibleCharacterBasis E) (hEodd : Odd (Nat.card E)) (Ω : Finset eb.index)
    (hodd : Odd Ω.card) (c : localizedComplexIntegerRing ideal)
    (hc : (c : ℂ) = ∑ μ' ∈ Ω, (eb.representation μ').character 1 / (Nat.card E : ℂ) *
      (eb.representation μ').character (1 : E)⁻¹) :
    localizedComplexIntegerResidue ideal c ≠ 0 := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  have hE : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcE : c * (Nat.card E : localizedComplexIntegerRing ideal) =
      ((∑ μ' ∈ Ω, Module.finrank ℂ (eb.representation μ').vector ^ 2 : ℕ) :
        localizedComplexIntegerRing ideal) := by
    apply Subtype.ext
    push_cast
    rw [hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ' _ => ?_
    rw [inv_one, character_one_eq]
    field_simp
  have hres := congrArg (localizedComplexIntegerResidue ideal) hcE
  rw [map_mul, map_natCast, map_natCast, natCast_eq_one_of_odd hEodd, mul_one] at hres
  rw [hres, Nat.cast_sum]
  have hterm : ∀ μ' ∈ Ω, ((Module.finrank ℂ (eb.representation μ').vector ^ 2 : ℕ) :
      ComplexAlgebraicIntegers ⧸ ideal) = 1 := fun μ' _ => by
    rw [Nat.cast_pow, natCast_eq_one_of_odd (odd_degree E eb hEodd μ'), one_pow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_one, natCast_eq_one_of_odd hodd]
  exact one_ne_zero

theorem even_orbit_residue_eq_zero (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (E : Subgroup H) [E.Normal]
    (eb : FiniteIrreducibleCharacterBasis E) (hEodd : Odd (Nat.card E)) (Q : Sylow 2 H)
    (μ : eb.index)
    (heven : Even (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card)
    (x : E) (hx : ∀ q ∈ (Q : Subgroup H), q * (x : H) = x * q)
    (c : localizedComplexIntegerRing ideal)
    (hc : (c : ℂ) = ∑ μ' ∈ Finset.univ.filter (fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ'),
      (eb.representation μ').character 1 / (Nat.card E : ℂ) *
        (eb.representation μ').character x⁻¹) :
    localizedComplexIntegerResidue ideal c = 0 := by
  let := labelAction E eb
  set Ω := Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ' with hΩ
  let t : eb.index → localizedComplexIntegerRing ideal := fun μ' =>
    ⟨_, term_mem ideal E eb hEodd μ' x⟩
  have hcsum : c = ∑ μ' ∈ Ω, t μ' := Subtype.ext (by
    rw [hc, AddSubmonoidClass.coe_finsetSum])
  rw [hcsum, map_sum, ← Fintype.sum_ite_mem]
  have hinv : ∀ (q : (Q : Subgroup H)) (μ' : eb.index),
      (fun ν => if ν ∈ Ω then localizedComplexIntegerResidue ideal (t ν) else 0) (q • μ') =
        (fun ν => if ν ∈ Ω then localizedComplexIntegerResidue ideal (t ν) else 0) μ' := by
    intro q μ'
    have hspec := conjLabel_spec E eb (q : H) μ'
    change (if conjLabel E eb q μ' ∈ Ω then localizedComplexIntegerResidue ideal
      (t (conjLabel E eb q μ')) else 0) =
        if μ' ∈ Ω then localizedComplexIntegerResidue ideal (t μ') else 0
    have hmemiff : conjLabel E eb q μ' ∈ Ω ↔ μ' ∈ Ω := by
      simp only [hΩ, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, hh⟩
        exact ⟨(q : H)⁻¹ * h, conjugateLabel_mul E eb hh (conjugateLabel_inv E eb hspec)⟩
      · rintro ⟨h, hh⟩
        exact ⟨(q : H) * h, conjugateLabel_mul E eb hh hspec⟩
    have hq : (q : H) * x * (q : H)⁻¹ = x := by
      rw [hx q q.2]
      group
    have h1 := hspec 1 1 (by
      change (1 : H) = q * 1 * (q : H)⁻¹
      group)
    have h2 := hspec x⁻¹ x⁻¹ (by
      change (x : H)⁻¹ = q * (x : H)⁻¹ * (q : H)⁻¹
      calc (x : H)⁻¹ = ((q : H) * x * (q : H)⁻¹)⁻¹ := by rw [hq]
        _ = q * (x : H)⁻¹ * (q : H)⁻¹ := by group)
    have hteq : t (conjLabel E eb q μ') = t μ' := by
      apply Subtype.ext
      show (eb.representation (conjLabel E eb q μ')).character 1 / (Nat.card E : ℂ) *
          (eb.representation (conjLabel E eb q μ')).character x⁻¹ =
        (eb.representation μ').character 1 / (Nat.card E : ℂ) *
          (eb.representation μ').character x⁻¹
      rw [h1, h2]
    rw [hteq]
    simp only [hmemiff]
  rw [p_group_invariant_sum_fixedPoints 2 Q.isPGroup' _ hinv]
  apply Finset.sum_eq_zero
  intro μ' _
  by_cases hfix : μ' ∈ MulAction.fixedPoints (Q : Subgroup H) eb.index
  · rw [ite_eq_left hfix]
    by_cases hmem : μ' ∈ Ω
    · exfalso
      have hQle : (Q : Subgroup H) ≤ labelStabilizer E eb μ' := fun q hq =>
        (mem_labelStabilizer E eb μ' q).mpr ((conjLabel_eq_iff E eb q μ' μ').mp
          (MulAction.mem_fixedPoints.mp hfix ⟨q, hq⟩))
      have hμ' : ∃ h : H, ConjugateLabel E eb h μ μ' := by
        simpa only [hΩ, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
      have hcard : Ω.card = (labelStabilizer E eb μ').index := by
        rw [hΩ, ← orbit_eq_of_mem E eb hμ', card_orbit_eq_index]
      have hodd : Odd Ω.card := by
        rw [hcard]
        refine Odd.of_dvd_nat ?_ (Subgroup.index_dvd_of_le hQle)
        exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Sylow.not_dvd_index Q))
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    · rw [ite_eq_right hmem]
  · rw [ite_eq_right hfix]

end FourGroupParity

open FourGroupParity

theorem order_eight_normal_four_group_orbit_defect_parity {H : Type*} [Group H] [Fintype H]
    (hb : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (V : Subgroup H) [V.Normal] (hV : IsKleinFour V) (hVp : IsPGroup 2 V)
    (Q : Sylow 2 H) (hQ : Nat.card (Q : Subgroup H) = 8)
    (E : Subgroup H) (hEW : E ≤ Subgroup.centralizer (V : Set H)) (hEodd : Odd (Nat.card E))
    (hVE : V ⊓ E = ⊥)
    (hW : ∀ w ∈ Subgroup.centralizer (V : Set H), ∃ a ∈ V, ∃ x ∈ E, w = a * x)
    (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (V : Set H)))
    (eb : FiniteIrreducibleCharacterBasis E) :
    (Nonempty (H ⧸ Subgroup.centralizer (V : Set H) ≃* Multiplicative (ZMod 2)) ∨
      Nonempty (H ⧸ Subgroup.centralizer (V : Set H) ≃* Equiv.Perm (Fin 3))) ∧
    ∀ (χ : hb.index) (μ : eb.index) (β : wb.index),
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ).character) →
      brauerNormalizerCharacterResidueHom ideal 2 V hVp (Subgroup.centralizer (V : Set H)) le_rfl
          (Subgroup.centralizer_le_normalizer _) wb β = centralCharacterResidueHom hb ideal χ →
      ((Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card = 1 ∨
        (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card = 2 ∨
        (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card = 3 ∨
        (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card = 6) ∧
      (Odd (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card →
        coefficientBlockDefect hb ideal 2 χ Q) ∧
      (Even (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card →
        coefficientBlockDefect hb ideal 2 χ V) ∧
      (coefficientBlockDefect hb ideal 2 χ Q ↔
        Odd (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ').card) := by
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb'
    have : IsKleinFour V := hV
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩)
  have hE2 : ¬ 2 ∣ Nat.card E := fun h => (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr h)
  have hEnormal : E.Normal := complement_normal V E hVp hEW hE2 hVE hW
  have hV4 : Nat.card V = 4 := hV.card_four
  have hidx := index_centralizer_eq V E hV hVab hEW hVE hW hEodd Q hQ
  refine ⟨quotient_centralizer_iso V hV hidx, ?_⟩
  intro χ μ β hβ hχ
  set Ω := Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ' with hΩ
  have hμΩ : μ ∈ Ω := by
    simp only [hΩ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, conjugateLabel_one E eb μ⟩
  have hΩdvd : Ω.card ∣ 6 := by
    rw [hΩ, card_orbit_eq_index E eb μ]
    have hdvdW := Subgroup.index_dvd_of_le (centralizer_le_labelStabilizer V E hEW hW eb μ)
    rcases hidx with h2 | h6
    · rw [h2] at hdvdW
      exact hdvdW.trans (by norm_num)
    · rwa [h6] at hdvdW
  have hcardΩ : Ω.card = 1 ∨ Ω.card = 2 ∨ Ω.card = 3 ∨ Ω.card = 6 := by
    have hle := Nat.le_of_dvd (by norm_num) hΩdvd
    have hpos : 0 < Ω.card := Finset.card_pos.mpr ⟨μ, hμΩ⟩
    interval_cases h : Ω.card <;> omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hformula⟩ :=
    normal_abelian_p_centralizer_orbit_idempotents hb ideal 2 V hVp hVab E hEW hE2 hVE hW wb eb
  have hq := (hformula χ μ β hβ hχ).1
  let eB := admissibleCharacterSubsetElement hb (localizedComplexIntegerRing ideal)
    (coefficientBlock hb (localizedComplexIntegerRing ideal) χ) (coefficientBlock_admissible _ _ χ)
  have heBval : eB.val = ∑ μ' ∈ Ω, MonoidAlgebra.mapDomainRingHom ℂ E.subtype
      (complexCharacterIdempotent (eb.representation μ').character) := hq
  have heBχ : centralCharacterResidueHom hb ideal χ eB = 1 := by
    rw [centralCharacterResidueHom_subset, ite_eq_left (coefficientBlock_self_mem _ _ _)]
  have heBidem : IsIdempotentElem eB :=
    Subtype.ext (characterSubsetIdempotent_isIdempotent hb _).eq
  obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer ((Q : Subgroup H) : Set H))
  obtain ⟨D, hD⟩ := coefficientBlockDefect_exists hb ideal 2 χ
  have hlocal := brauerNormalizer_local_block_exists_iff_subconjugate hb ideal 2 (Q : Subgroup H)
    Q.isPGroup' _ le_rfl (Subgroup.centralizer_le_normalizer _) lb hD
  have hoddsub : Odd Ω.card → subgroupSubconjugate (Q : Subgroup H) D := by
    intro hodd
    apply hlocal.mp
    by_contra hnone
    have hzero : ∀ γ : lb.index, centralCharacterResidueHom lb ideal γ
        (centralNormalizerCoefficientProjection _ (Q : Subgroup H) _ le_rfl
          (Subgroup.centralizer_le_normalizer _) eB) = 0 := by
      intro γ
      obtain ⟨χ', hχ'⟩ := brauerNormalizer_block_image_exists hb ideal 2 (Q : Subgroup H)
        Q.isPGroup' _ le_rfl (Subgroup.centralizer_le_normalizer _) lb γ
      have hval := congrArg (fun f => f eB) hχ'
      change centralCharacterResidueHom lb ideal γ (centralNormalizerCoefficientProjection _
        (Q : Subgroup H) _ le_rfl (Subgroup.centralizer_le_normalizer _) eB) =
          centralCharacterResidueHom hb ideal χ' eB at hval
      rw [hval, centralCharacterResidueHom_subset, ite_eq_right]
      intro hmem
      apply hnone
      refine ⟨γ, ?_⟩
      rw [hχ']
      exact ((sameCoefficientBlock_iff_centralCharacterResidueHom_eq hb ideal χ χ').mp
        ((coefficientBlock_mem_iff _ _ _ _).mp hmem)).symm
    have hidem : IsIdempotentElem (centralCoefficientReductionHom ideal
        (centralNormalizerCoefficientProjection _ (Q : Subgroup H) _ le_rfl
          (Subgroup.centralizer_le_normalizer _) eB)) :=
      heBidem.map (reducedBrauerProjectionHom ideal 2 (Q : Subgroup H) Q.isPGroup' _ le_rfl
        (Subgroup.centralizer_le_normalizer _))
    have hred := centralCoefficientReductionHom_idempotent_zero_of_residues_zero lb ideal _ hidem
      hzero
    have hcoeff := congrArg
      (fun z => z.coeff (1 : Subgroup.centralizer ((Q : Subgroup H) : Set H))) hred
    change (reducedBrauerProjectionHom ideal 2 (Q : Subgroup H) Q.isPGroup' _ le_rfl
      (Subgroup.centralizer_le_normalizer _) eB).coeff 1 = _ at hcoeff
    rw [reducedBrauerProjectionHom_coeff,
      ite_eq_left (1 : Subgroup.centralizer ((Q : Subgroup H) : Set H)).property] at hcoeff
    have hne := odd_orbit_residue_ne_zero ideal E eb hEodd Ω hodd
      ⟨eB.val.coeff 1, centralCoefficientSubring_coefficients _ eB 1⟩ (by
        change eB.val.coeff (1 : H) = _
        rw [heBval]
        exact orbitSum_coeff E eb Ω 1)
    refine hne (hcoeff.trans ?_)
    simp
  have hevensub : Even Ω.card → ¬ subgroupSubconjugate (Q : Subgroup H) D := by
    intro heven hsub
    obtain ⟨γ, hγ⟩ := hlocal.mpr hsub
    have hzero : ∀ r : localizedComplexIntegerRing ideal, (r : ℂ) = 0 →
        localizedComplexIntegerResidue ideal r = 0 := by
      intro r hr
      rw [show r = 0 from Subtype.ext hr, map_zero]
    have hred : centralCoefficientReductionHom ideal (centralNormalizerCoefficientProjection _
        (Q : Subgroup H) _ le_rfl (Subgroup.centralizer_le_normalizer _) eB) = 0 := by
      ext c
      change (reducedBrauerProjectionHom ideal 2 (Q : Subgroup H) Q.isPGroup' _ le_rfl
        (Subgroup.centralizer_le_normalizer _) eB).coeff c = _
      rw [reducedBrauerProjectionHom_coeff, ite_eq_left c.property]
      simp only [MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_cases hcE : (c : H) ∈ E
      · apply even_orbit_residue_eq_zero ideal E eb hEodd Q μ heven ⟨c, hcE⟩
          (fun q hq => Subgroup.mem_centralizer_iff.mp c.property q hq)
        change eB.val.coeff (c : H) = _
        rw [heBval]
        exact orbitSum_coeff E eb Ω ⟨c, hcE⟩
      · apply hzero
        change eB.val.coeff (c : H) = 0
        rw [heBval]
        exact orbitSum_coeff_zero E eb Ω _ hcE
    have h1 := congrArg (fun f => f eB) hγ
    change centralCharacterResidueHom lb ideal γ (centralNormalizerCoefficientProjection _
      (Q : Subgroup H) _ le_rfl (Subgroup.centralizer_le_normalizer _) eB) =
        centralCharacterResidueHom hb ideal χ eB at h1
    rw [heBχ, centralCharacterResidueHom_zero_of_coefficient_reduction_zero lb ideal _ hred γ] at h1
    exact zero_ne_one h1
  have hVD : V ≤ D := normal_p_le_coefficientBlockDefect hb ideal 2 V hVp hD
  have hDp : IsPGroup 2 D := coefficientBlockDefect_isPGroup hb ideal hD
  have hDQ : subgroupSubconjugate D (Q : Subgroup H) :=
    CompatibleFamily.pSubgroup_subconjugate_sylow Q hDp
  have hD8 : Nat.card D ≤ 8 := hQ ▸ subgroupSubconjugate_card_le hDQ
  have h4D : 4 ∣ Nat.card D := hV4 ▸ Subgroup.card_dvd_of_le hVD
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hQdef : Odd Ω.card → coefficientBlockDefect hb ideal 2 χ Q := fun hodd => by
    have hsub := hoddsub hodd
    have hle := subgroupSubconjugate_card_le hsub
    have hconj : subgroupsConjugate (Q : Subgroup H) D :=
      subgroupsConjugate_of_subconjugate_card_ge hsub (by omega)
    exact coefficientBlockDefect_of_subgroupsConjugate hb ideal hD (subgroupsConjugate_symm hconj)
  have hVdef : Even Ω.card → coefficientBlockDefect hb ideal 2 χ V := fun heven => by
    have hnot := hevensub heven
    have hD4 : Nat.card D = 4 := by
      by_contra hne
      have hD8' : Nat.card D = 8 := by omega
      apply hnot
      exact subgroupsConjugate_subconjugate (subgroupsConjugate_symm
        (subgroupsConjugate_of_subconjugate_card_ge hDQ (by omega)))
    have hVeq : V = D := Subgroup.eq_of_le_of_card_ge hVD (by omega)
    rw [hVeq]
    exact hD
  refine ⟨hcardΩ, hQdef, hVdef, ⟨fun hQd => ?_, hQdef⟩⟩
  by_contra hnotodd
  have hVd := hVdef (Nat.not_odd_iff_even.mp hnotodd)
  have hconj := coefficientBlockDefect_conjugate hb ideal hQd hVd
  have hle := subgroupSubconjugate_card_le (subgroupsConjugate_subconjugate hconj)
  omega

end CFSG.Semidihedral.Principal
