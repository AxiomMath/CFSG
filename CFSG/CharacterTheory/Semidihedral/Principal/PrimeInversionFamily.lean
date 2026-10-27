module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionSections
public import CFSG.CharacterTheory.Semidihedral.Principal.NormThreeGram
public import CFSG.CharacterTheory.Semidihedral.Principal.FullPrimePartBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientRegular
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormOne

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes

variable {G : Type*} [Group G]

@[expose] noncomputable def inversionTwist (u : G) (ℓ : ℕ) (i : ℤ) : Subgroup.zpowers u → ℂ :=
  fun x => 1 - cyclicLinearCharacter u ℓ i x

theorem cyclicLinearCharacter_zero_apply (u : G) (ℓ : ℕ) (x : Subgroup.zpowers u) :
    cyclicLinearCharacter u ℓ 0 x = 1 := by
  simp [cyclicLinearCharacter]

theorem inversionTwist_one {u : G} {ℓ : ℕ} (hu : orderOf u = ℓ) (i : ℤ) :
    inversionTwist u ℓ i 1 = 0 := by
  simp [inversionTwist, cyclicLinearCharacter_one hu]

theorem inversionTwist_zpow {u : G} {ℓ : ℕ} (hu : orderOf u = ℓ) (i k : ℤ) :
    inversionTwist u ℓ i ⟨u ^ k, Subgroup.zpow_mem_zpowers u k⟩ = 1 - cyclicRoot ℓ ^ (i * k) := by
  simp [inversionTwist, cyclicLinearCharacter_zpow hu]

section Pairing

variable [Fintype G]

theorem characterPairing_inversionTwist (f : G → ℂ) {u : G} {ℓ : ℕ} (hu : orderOf u = ℓ)
    (i : ℤ) :
    characterPairing (fun x : Subgroup.zpowers u => f x) (inversionTwist u ℓ i) =
      cyclicMultiplicity f u ℓ 0 - cyclicMultiplicity f u ℓ i := by
  rw [← characterPairing_zpowers_cyclicLinearCharacter f hu 0,
    ← characterPairing_zpowers_cyclicLinearCharacter f hu i]
  unfold characterPairing inversionTwist
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cyclicLinearCharacter_zero_apply]
  ring

theorem characterPairing_sum_left {H : Type*} [Group H] [Fintype H] {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (F : ι → H → ℂ) (h : H → ℂ) :
    characterPairing (fun x => ∑ i ∈ s, c i * F i x) h =
      ∑ i ∈ s, c i * characterPairing (F i) h := by
  unfold characterPairing
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring

end Pairing

section RootSums

theorem sum_cyclicRoot_pair_eq_neg_one {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {j : ℤ}
    (hj : ¬ (ℓ : ℤ) ∣ j) :
    ∑ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
      (cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j))) = -1 := by
  have hℓpos : 0 < ℓ := hℓ.pos
  have hodd : ℓ % 2 = 1 := hℓ.eq_two_or_odd.resolve_left hℓ2
  set r := (ℓ - 1) / 2 with hr
  have hr2 : 2 * r + 1 = ℓ := by omega
  set f : ℕ → ℂ := fun k => cyclicRoot ℓ ^ (j * (k : ℤ)) with hf
  have htotal : ∑ k ∈ Finset.range ℓ, f k = 0 := by
    rw [hf, sum_range_cyclicRoot_zpow hℓpos j]
    simp [hj]
  have hsplit : ∑ k ∈ Finset.range ℓ, f k = f 0 + ∑ k ∈ Finset.Ico 1 ℓ, f k := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f (Nat.zero_le 1) (by omega : 1 ≤ ℓ)]
    simp
  have hsplit2 : ∑ k ∈ Finset.Ico 1 ℓ, f k =
      ∑ k ∈ Finset.Ico 1 (r + 1), f k + ∑ k ∈ Finset.Ico (r + 1) ℓ, f k :=
    (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm
  have hrefl : ∑ k ∈ Finset.Ico (r + 1) ℓ, f k = ∑ i ∈ Finset.Ico 1 (r + 1), f (ℓ - i) := by
    apply Finset.sum_nbij' (fun k => ℓ - k) (fun i => ℓ - i)
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      congr 1
      omega
  have hf0 : f 0 = 1 := by simp [hf]
  have hterm : ∀ i ∈ Finset.Icc 1 r,
      cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j)) = f i + f (ℓ - i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp only [hf]
    congr 1
    · rw [mul_comm]
    · apply cyclicRoot_zpow_congr
      have hcast : ((ℓ - i : ℕ) : ℤ) = (ℓ : ℤ) - i := by
        rw [Nat.cast_sub (by omega : i ≤ ℓ)]
      rw [hcast]
      exact Int.modEq_iff_dvd.mpr ⟨j, by ring⟩
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.Ico_add_one_right_eq_Icc,
    ← hrefl]
  have h := htotal
  rw [hsplit, hsplit2, hf0] at h
  linear_combination h

theorem sum_cyclicRoot_pair_sq {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {j : ℤ}
    (hj : ¬ (ℓ : ℤ) ∣ j) :
    ∑ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
      (cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j))) ^ 2 = ℓ - 2 := by
  have hodd : ℓ % 2 = 1 := hℓ.eq_two_or_odd.resolve_left hℓ2
  have h2j : ¬ (ℓ : ℤ) ∣ 2 * j := by
    intro h
    rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd h with h' | h'
    · have : (ℓ : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h'
      have := hℓ.two_le
      omega
    · exact hj h'
  have hne : cyclicRoot ℓ ≠ 0 := cyclicRoot_ne_zero ℓ
  have hsq : ∀ i : ℕ, (cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j))) ^ 2 =
      2 + (cyclicRoot ℓ ^ ((i : ℤ) * (2 * j)) + cyclicRoot ℓ ^ (-((i : ℤ) * (2 * j)))) := by
    intro i
    have h1 : cyclicRoot ℓ ^ ((i : ℤ) * j) * cyclicRoot ℓ ^ (-((i : ℤ) * j)) = 1 := by
      rw [← zpow_add₀ hne, add_neg_cancel, zpow_zero]
    have h2 : cyclicRoot ℓ ^ ((i : ℤ) * (2 * j)) =
        cyclicRoot ℓ ^ ((i : ℤ) * j) * cyclicRoot ℓ ^ ((i : ℤ) * j) := by
      rw [← zpow_add₀ hne]
      ring_nf
    have h3 : cyclicRoot ℓ ^ (-((i : ℤ) * (2 * j))) =
        cyclicRoot ℓ ^ (-((i : ℤ) * j)) * cyclicRoot ℓ ^ (-((i : ℤ) * j)) := by
      rw [← zpow_add₀ hne]
      ring_nf
    rw [h2, h3]
    linear_combination 2 * h1
  simp_rw [hsq]
  rw [Finset.sum_add_distrib, sum_cyclicRoot_pair_eq_neg_one hℓ hℓ2 h2j, Finset.sum_const,
    Nat.card_Icc]
  have hr : (ℓ - 1) / 2 + 1 - 1 = (ℓ - 1) / 2 := by omega
  rw [hr, nsmul_eq_mul]
  have hr2 : (ℓ - 1) / 2 * 2 + 1 = ℓ := by omega
  have hcast := congrArg (Nat.cast : ℕ → ℂ) hr2
  push_cast at hcast
  linear_combination hcast

end RootSums

section Labels

variable [Fintype G]

theorem characterPairing_label_label (basis : FiniteIrreducibleCharacterBasis G)
    (x y : basis.index) :
    characterPairing (basis.representation x).character (basis.representation y).character =
      if x = y then 1 else 0 := by
  rw [characterPairing_irreducible _ _ (basis.irreducible x) (basis.irreducible y)]
  by_cases h : x = y
  · subst h
    simp
  · have h' : (basis.representation x).character ≠ (basis.representation y).character :=
      fun hc => h (basis.distinct hc)
    simp [h, h']

theorem exists_conj_label (basis : FiniteIrreducibleCharacterBasis G) (x : basis.index) :
    ∃ x' : basis.index, ∀ g, (basis.representation x').character g =
      starRingEnd ℂ ((basis.representation x).character g) := by
  let data : FiniteComplexRepresentation G :=
    { vector := Module.Dual ℂ (basis.representation x).vector
      representation := (basis.representation x).representation.dual }
  have hchar : ∀ g, data.character g = starRingEnd ℂ ((basis.representation x).character g) := by
    intro g
    change (basis.representation x).representation.dual.character g = _
    rw [Representation.char_dual, finite_character_conjugate_inverse]
  have hself : characterPairing (basis.representation x).character
      (basis.representation x).character = 1 := by
    rw [characterPairing_label_label]
    simp
  have hnorm : characterPairing data.character data.character = 1 := by
    rw [← hself]
    unfold characterPairing
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    change (basis.representation x).representation.dual.character g *
      (basis.representation x).representation.dual.character g⁻¹ = _
    rw [Representation.char_dual, Representation.char_dual, inv_inv, mul_comm]
  obtain ⟨x', hx'⟩ := character_norm_one_basis_character basis data hnorm
  exact ⟨x', fun g => by rw [hx', hchar]⟩

end Labels

section SingularClasses

variable [Fintype G]

theorem exists_isConj_pow_mul_of_dvd_orderOf {ℓ : ℕ} [Fact ℓ.Prime] (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ) {z : G}
    (hz : ℓ ∣ orderOf z) :
    ∃ j ∈ Finset.Icc 1 (ℓ - 1), ∃ y ∈ Subgroup.centralizer (P : Set G),
      ¬ ℓ ∣ orderOf y ∧ IsConj z (u ^ j * y) := by
  have hp : ℓ.Prime := Fact.out
  have hu : orderOf u = ℓ := by rw [← Nat.card_zpowers, ← hPu]; exact hP
  obtain ⟨a, b, e, -, -, hab, habz, ha, hb⟩ := finite_prime_primary_factorization z ℓ hp
  have hane : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at habz
    rw [← habz] at hz
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hb hz
  obtain ⟨k₀, -, hk₀⟩ := (Nat.dvd_prime_pow hp).mp ha
  have hpa : IsPGroup ℓ (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := k₀) (by rw [Nat.card_zpowers, hk₀])
  obtain ⟨Q, hQ⟩ := hpa.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hmem : g * a * g⁻¹ ∈ (P : Subgroup G) := by
    have h := Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (Q : Subgroup G)
      (hQ (Subgroup.mem_zpowers a))
    rw [MulAut.smul_def, MulAut.conj_apply] at h
    rw [← hg, Sylow.coe_subgroup_smul]
    exact h
  rw [hPu] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hone : ∀ m : ℤ, u ^ m = 1 ↔ (ℓ : ℤ) ∣ m := fun m => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hu]
  have hk1 : ¬ (ℓ : ℤ) ∣ k := by
    intro hdvd
    apply hane
    have h1 : u ^ k = 1 := (hone k).mpr hdvd
    rw [hk] at h1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast hp.pos
  set j := (k % ℓ).toNat with hj
  have hmod0 : 0 ≤ k % ℓ := Int.emod_nonneg k hℓ0.ne'
  have hmodlt : k % ℓ < ℓ := Int.emod_lt_of_pos k hℓ0
  have hmodne : k % ℓ ≠ 0 := fun h => hk1 (Int.dvd_of_emod_eq_zero h)
  have hjcast : (j : ℤ) = k % ℓ := Int.toNat_of_nonneg hmod0
  have hujk : u ^ j = u ^ k := by
    rw [← zpow_natCast, hjcast, ← hu, zpow_mod_orderOf]
  have hjmem : j ∈ Finset.Icc 1 (ℓ - 1) := by
    rw [Finset.mem_Icc]
    omega
  refine ⟨j, hjmem, g * b * g⁻¹, ?_, ?_, ?_⟩
  ·
    have hc : Commute (u ^ k) (g * b * g⁻¹) := by
      rw [hk]
      exact hab.map (MulAut.conj g).toMonoidHom
    rw [commute_zpow_iff hu hk1] at hc
    rw [show (P : Set G) = (Subgroup.zpowers u : Set G) by rw [← hPu]; rfl]
    exact CFSG.LyonsUnitaryFour.mem_centralizer_zpowers_of_commute hc
  · rw [orderOf_conj_eq]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hb
  · refine isConj_iff.mpr ⟨g, ?_⟩
    rw [hujk, hk, ← habz]
    group

end SingularClasses

section Projections

variable [Fintype G]

theorem inversionProjection_zpow (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ] (hℓ2 : ℓ ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) (i k : ℤ) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal) u (inversionTwist u ℓ i) (u ^ k) =
      2 - cyclicRoot ℓ ^ (i * k) - cyclicRoot ℓ ^ (-(i * k)) := by
  have hp : ℓ.Prime := Fact.out
  have hu : orderOf u = ℓ := by rw [← Nat.card_zpowers, ← hPu]; exact hP
  by_cases hk : (ℓ : ℤ) ∣ k
  · have h1 : u ^ k = 1 := by rw [← orderOf_dvd_iff_zpow_eq_one, hu]; exact hk
    have hz1 : cyclicRoot ℓ ^ (i * k) = 1 := by
      rw [cyclicRoot_zpow_congr (y := 0) (Int.modEq_zero_iff_dvd.mpr (hk.mul_left i)),
        zpow_zero]
    have hz2 : cyclicRoot ℓ ^ (-(i * k)) = 1 := by
      rw [cyclicRoot_zpow_congr (y := 0)
        (Int.modEq_zero_iff_dvd.mpr ((hk.mul_left i).neg_right)), zpow_zero]
    rw [h1, hz1, hz2, principalCyclicProjection_eq_zero_of_regular basis ideal ℓ principal hu _
      (inversionTwist_one hu i) (by rw [orderOf_one]; exact hp.not_dvd_one)]
    norm_num
  · have h := principalCyclicProjection_prime_inversion_section basis ideal ℓ hℓ2 principal
      hprincipal P u hPu hP hindex (inversionTwist u ℓ i) hk (y := 1) (Commute.one_right u)
      (by rw [orderOf_one]; exact hp.not_dvd_one)
    rw [mul_one] at h
    rw [h, inversionTwist_zpow hu, inversionTwist_zpow hu, mul_neg]
    ring

theorem cyclicMultiplicity_inversionProjection (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ] (hℓ2 : ℓ ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) (i m : ℤ) :
    cyclicMultiplicity (principalCyclicProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) u
        (inversionTwist u ℓ i)) u ℓ m =
      2 * (if (ℓ : ℤ) ∣ m then 1 else 0) - (if (ℓ : ℤ) ∣ i - m then 1 else 0) -
        (if (ℓ : ℤ) ∣ i + m then 1 else 0) := by
  have hp : ℓ.Prime := Fact.out
  have hℓpos : 0 < ℓ := hp.pos
  have hne : cyclicRoot ℓ ≠ 0 := cyclicRoot_ne_zero ℓ
  have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  unfold cyclicMultiplicity
  have hval : ∀ v : ℕ, principalCyclicProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) u
        (inversionTwist u ℓ i) (u ^ v) * cyclicRoot ℓ ^ (-(m * v)) =
      2 * cyclicRoot ℓ ^ (-m * v) - cyclicRoot ℓ ^ ((i - m) * v) -
        cyclicRoot ℓ ^ ((-i - m) * v) := by
    intro v
    rw [← zpow_natCast u v, inversionProjection_zpow basis ideal ℓ hℓ2 principal hprincipal P u
      hPu hP hindex i v]
    have e1 : cyclicRoot ℓ ^ (i * (v : ℤ)) * cyclicRoot ℓ ^ (-(m * v)) =
        cyclicRoot ℓ ^ ((i - m) * v) := by
      rw [← zpow_add₀ hne]
      congr 1
      ring
    have e2 : cyclicRoot ℓ ^ (-(i * (v : ℤ))) * cyclicRoot ℓ ^ (-(m * v)) =
        cyclicRoot ℓ ^ ((-i - m) * v) := by
      rw [← zpow_add₀ hne]
      congr 1
      ring
    have e3 : cyclicRoot ℓ ^ (-(m * (v : ℤ))) = cyclicRoot ℓ ^ (-m * v) := by
      congr 1
      ring
    rw [sub_mul, sub_mul, e1, e2, e3]
  rw [Finset.sum_congr rfl fun v _ => hval v, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_range_cyclicRoot_zpow hℓpos, sum_range_cyclicRoot_zpow hℓpos,
    sum_range_cyclicRoot_zpow hℓpos]
  have hneg : ∀ x : ℤ, (ℓ : ℤ) ∣ -x ↔ (ℓ : ℤ) ∣ x := fun x => dvd_neg
  have hsub : ∀ x y : ℤ, (ℓ : ℤ) ∣ -x - y ↔ (ℓ : ℤ) ∣ x + y := fun x y => by
    rw [show -x - y = -(x + y) by ring, dvd_neg]
  simp only [hneg, hsub]
  split_ifs <;> field_simp <;> ring

end Projections

section Family

variable [Fintype G]

theorem label_character_one (basis : FiniteIrreducibleCharacterBasis G) (c : basis.index) :
    (basis.representation c).character 1 =
        (Module.finrank ℂ (basis.representation c).vector : ℂ) ∧
      0 < Module.finrank ℂ (basis.representation c).vector := by
  have h1 : (basis.representation c).character 1 =
      (Module.finrank ℂ (basis.representation c).vector : ℂ) := by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  refine ⟨h1, Nat.pos_of_ne_zero fun h0 => ?_⟩
  apply irreducible_character_degree_ne_zero _ (basis.irreducible c)
  rw [h1, h0, Nat.cast_zero]

omit [Fintype G] in
theorem cyclicMultiplicity_one_character {u : G} {ℓ : ℕ} (hℓ : 0 < ℓ) (j : ℤ) :
    cyclicMultiplicity (1 : G → ℂ) u ℓ j = if (ℓ : ℤ) ∣ j then 1 else 0 := by
  unfold cyclicMultiplicity
  have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne'
  have h : ∀ v : ℕ, (1 : G → ℂ) (u ^ v) * cyclicRoot ℓ ^ (-(j * v)) =
      cyclicRoot ℓ ^ (-j * v) := fun v => by
    rw [Pi.one_apply, one_mul, neg_mul]
  rw [Finset.sum_congr rfl fun v _ => h v, sum_range_cyclicRoot_zpow hℓ]
  simp only [dvd_neg]
  split_ifs <;> field_simp
  simp

theorem prime_inversion_family_decomposition (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ] (hℓ : 5 ≤ ℓ) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) :
    ∃ (a : basis.index) (b : Finset.Icc 1 ((ℓ - 1) / 2) → basis.index) (δ : ℤ),
      a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      a ≠ principal ∧ Function.Injective b ∧
      (∀ k, b k ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
        b k ≠ principal ∧ b k ≠ a) ∧
      (δ = 1 ∨ δ = -1) ∧
      (∀ k, (Module.finrank ℂ (basis.representation (b k)).vector : ℤ) =
        Module.finrank ℂ (basis.representation a).vector + δ) ∧
      0 < (Module.finrank ℂ (basis.representation a).vector : ℤ) + δ ∧
      ∀ (k : Finset.Icc 1 ((ℓ - 1) / 2)) (g : G),
        principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
          principal) u (inversionTwist u ℓ (k : ℕ)) g =
          1 + δ * (basis.representation a).character g -
            δ * (basis.representation (b k)).character g := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓpos : 0 < ℓ := hp.pos
  have hu : orderOf u = ℓ := by rw [← Nat.card_zpowers, ← hPu]; exact hP
  have hupow : u ^ ℓ = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set r := (ℓ - 1) / 2 with hr
  have hr2 : 2 ≤ r := by omega
  have hrl : 2 * r < ℓ := by omega
  have hprinB : principal ∈ B := coefficientBlock_self_mem _ _ _
  choose m hm using fun (x : basis.index) (k : ℤ) =>
    cyclicMultiplicity_natural (basis.representation x) u hℓpos hupow k
  have hc : ∀ (x : basis.index) (i : ℤ),
      characterPairing (fun y : Subgroup.zpowers u => (basis.representation x).character y)
        (inversionTwist u ℓ i) = (((m x 0 : ℤ) - m x i : ℤ) : ℂ) := by
    intro x i
    rw [characterPairing_inversionTwist _ hu, hm, hm]
    push_cast
    ring
  have hTsum : ∀ (i : ℤ) (g : G), principalCyclicProjection basis B u (inversionTwist u ℓ i) g =
      ∑ x ∈ B, (((m x 0 : ℤ) - m x i : ℤ) : ℂ) * (basis.representation x).character g := by
    intro i g
    unfold principalCyclicProjection
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hc]
  have hgram : ∀ i i' : ℤ, ¬ (ℓ : ℤ) ∣ i → ¬ (ℓ : ℤ) ∣ i' →
      ((∑ x ∈ B, ((m x 0 : ℤ) - m x i) * ((m x 0 : ℤ) - m x i') : ℤ) : ℂ) =
        2 + (if (ℓ : ℤ) ∣ i - i' then 1 else 0) + (if (ℓ : ℤ) ∣ i + i' then 1 else 0) := by
    intro i i' hi hi'
    have h1 := characterPairing_sum_left B (fun x => (((m x 0 : ℤ) - m x i : ℤ) : ℂ))
      (fun x (y : Subgroup.zpowers u) => (basis.representation x).character y)
      (inversionTwist u ℓ i')
    have h2 : (fun y : Subgroup.zpowers u => ∑ x ∈ B, (((m x 0 : ℤ) - m x i : ℤ) : ℂ) *
        (basis.representation x).character y) =
        fun y : Subgroup.zpowers u => principalCyclicProjection basis B u
          (inversionTwist u ℓ i) y := by
      funext y
      rw [hTsum]
    rw [h2, characterPairing_inversionTwist _ hu,
      cyclicMultiplicity_inversionProjection basis ideal ℓ hℓ2 principal hprincipal P u hPu hP
        hindex i 0,
      cyclicMultiplicity_inversionProjection basis ideal ℓ hℓ2 principal hprincipal P u hPu hP
        hindex i i'] at h1
    simp_rw [hc] at h1
    push_cast at h1 ⊢
    simp only [sub_zero, add_zero, dvd_zero, hi, hi', ↓reduceIte, mul_one, mul_zero] at h1
    linear_combination -h1
  have hIcard : 2 ≤ Fintype.card (Finset.Icc 1 r) := by
    rw [Fintype.card_coe, Nat.card_Icc]
    omega
  have hkmem : ∀ k : Finset.Icc 1 r, 1 ≤ (k : ℕ) ∧ (k : ℕ) ≤ r := fun k => Finset.mem_Icc.mp k.2
  have hidx : ∀ k : Finset.Icc 1 r, ¬ (ℓ : ℤ) ∣ ((k : ℕ) : ℤ) := by
    intro k hdvd
    have hk := hkmem k
    have h' := Int.le_of_dvd (by exact_mod_cast (by omega : 0 < (k : ℕ))) hdvd
    omega
  let v : Finset.Icc 1 r → basis.index → ℤ := fun k x =>
    if x ∈ B then (m x 0 : ℤ) - m x ((k : ℕ) : ℤ) else 0
  let d : basis.index → ℤ := fun x => Module.finrank ℂ (basis.representation x).vector
  have hd : ∀ x, 0 < d x := fun x => by
    show (0 : ℤ) < (Module.finrank ℂ (basis.representation x).vector : ℤ)
    exact_mod_cast (label_character_one basis x).2
  have hdo : d principal = 1 := by
    have h := (label_character_one basis principal).1
    rw [hprincipal, Pi.one_apply] at h
    have h' : (Module.finrank ℂ (basis.representation principal).vector : ℂ) = 1 := h.symm
    show (Module.finrank ℂ (basis.representation principal).vector : ℤ) = 1
    exact_mod_cast h'
  have hmprin : ∀ j : ℤ, (m principal j : ℂ) = if (ℓ : ℤ) ∣ j then 1 else 0 := by
    intro j
    have h := hm principal j
    rw [hprincipal, cyclicMultiplicity_one_character hℓpos] at h
    exact h.symm
  have hvo : ∀ k, v k principal = 1 := by
    intro k
    have h0 := hmprin 0
    have hk := hmprin ((k : ℕ) : ℤ)
    simp only [dvd_zero, ↓reduceIte, hidx k] at h0 hk
    have h0' : m principal 0 = 1 := by exact_mod_cast h0
    have hk' : m principal ((k : ℕ) : ℤ) = 0 := by exact_mod_cast hk
    simp only [v, hprinB, ↓reduceIte, h0', hk']
    norm_num
  have hsumB : ∀ F : basis.index → ℤ, ∑ x, (if x ∈ B then F x else 0) = ∑ x ∈ B, F x := by
    intro F
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hnorm : ∀ k, ∑ x, v k x ^ 2 = 3 := by
    intro k
    have h := hgram _ _ (hidx k) (hidx k)
    have hk := hkmem k
    have h2k : ¬ (ℓ : ℤ) ∣ ((k : ℕ) : ℤ) + ((k : ℕ) : ℤ) := by
      intro hdvd
      have h' := Int.le_of_dvd (by omega) hdvd
      omega
    simp only [sub_self, dvd_zero, ↓reduceIte, h2k, add_zero] at h
    have h' : ((∑ x ∈ B, ((m x 0 : ℤ) - m x ((k : ℕ) : ℤ)) * ((m x 0 : ℤ) - m x ((k : ℕ) : ℤ)) :
        ℤ) : ℂ) = ((3 : ℤ) : ℂ) := by
      rw [h]
      norm_num
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v]
    split_ifs <;> ring
  have hdeg : ∀ k, ∑ x, d x * v k x = 0 := by
    intro k
    have hT1 := principalCyclicProjection_eq_zero_of_regular basis ideal ℓ principal hu
      (inversionTwist u ℓ ((k : ℕ) : ℤ)) (inversionTwist_one hu _) (g := 1)
      (by rw [orderOf_one]; exact hp.not_dvd_one)
    rw [hTsum] at hT1
    have h' : ((∑ x ∈ B, (Module.finrank ℂ (basis.representation x).vector : ℤ) *
        ((m x 0 : ℤ) - m x ((k : ℕ) : ℤ)) : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by
      push_cast
      rw [← hT1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [(label_character_one basis x).1]
      push_cast
      ring
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v, d]
    split_ifs <;> ring
  have hgram' : ∀ k k', k ≠ k' → ∑ x, v k x * v k' x = 2 := by
    intro k k' hkk
    have h := hgram _ _ (hidx k) (hidx k')
    have hk := hkmem k
    have hk' := hkmem k'
    have hsub : ¬ (ℓ : ℤ) ∣ ((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) := by
      intro hdvd
      have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
      exact hkk (Subtype.ext (by omega))
    have hadd : ¬ (ℓ : ℤ) ∣ ((k : ℕ) : ℤ) + ((k' : ℕ) : ℤ) := by
      intro hdvd
      have h' := Int.le_of_dvd (by omega) hdvd
      omega
    simp only [hsub, hadd, ↓reduceIte, add_zero] at h
    have h' : ((∑ x ∈ B, ((m x 0 : ℤ) - m x ((k : ℕ) : ℤ)) * ((m x 0 : ℤ) - m x ((k' : ℕ) : ℤ)) :
        ℤ) : ℂ) = ((2 : ℤ) : ℂ) := by
      rw [h]
      norm_num
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v]
    split_ifs <;> ring
  obtain ⟨a, hao, b, hbinj, hbne, δ, hδ, hv⟩ :=
    integral_norm_three_degree_zero_gram_family_common_coordinate hIcard principal d hd hdo v hvo
      hnorm hdeg hgram'
  have hvB : ∀ k x, v k x ≠ 0 → x ∈ B := by
    intro k x hx
    by_contra hxB
    exact hx (by simp only [v, hxB, ↓reduceIte])
  have hk₀ : (1 : ℕ) ∈ Finset.Icc 1 r := Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩
  have haB : a ∈ B := hvB ⟨1, hk₀⟩ a (((hv ⟨1, hk₀⟩).2.2.2 a).mpr (Or.inr (Or.inl rfl)))
  have hbB : ∀ k, b k ∈ B := fun k => hvB k (b k) (((hv k).2.2.2 (b k)).mpr (Or.inr (Or.inr rfl)))
  refine ⟨a, b, δ, haB, hao, hbinj, fun k => ⟨hbB k, (hbne k).1, (hbne k).2⟩, hδ,
    fun k => (hv k).2.1, (hv ⟨1, hk₀⟩).2.2.1, fun k g => ?_⟩
  rw [hTsum]
  have hext : ∑ x ∈ B, (((m x 0 : ℤ) - m x ((k : ℕ) : ℤ) : ℤ) : ℂ) *
      (basis.representation x).character g =
      ∑ x, (v k x : ℂ) * (basis.representation x).character g := by
    rw [← Finset.sum_subset (Finset.subset_univ B)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      simp only [v, hx, ↓reduceIte]
    · intro x _ hx
      simp only [v, hx, ↓reduceIte]
      push_cast
      ring
  rw [hext, (hv k).1]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  push_cast
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hprincipal, Pi.one_apply]

end Family

section Values

variable [Fintype G]

theorem prime_inversion_values_at_powers (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ] (hℓ : 5 ≤ ℓ) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    (a : basis.index) (b : Finset.Icc 1 ((ℓ - 1) / 2) → basis.index) (δ : ℤ)
    (haB : a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hao : a ≠ principal) (hbinj : Function.Injective b)
    (hb : ∀ k, b k ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      b k ≠ principal ∧ b k ≠ a) (hδ : δ = 1 ∨ δ = -1)
    (hT : ∀ (k : Finset.Icc 1 ((ℓ - 1) / 2)) (g : G),
      principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        principal) u (inversionTwist u ℓ (k : ℕ)) g =
        1 + δ * (basis.representation a).character g -
          δ * (basis.representation (b k)).character g)
    {j : ℤ} (hj : ¬ (ℓ : ℤ) ∣ j) :
    (basis.representation a).character (u ^ j) = δ ∧
    (∀ k : Finset.Icc 1 ((ℓ - 1) / 2), (basis.representation (b k)).character (u ^ j) =
      δ * (cyclicRoot ℓ ^ (((k : ℕ) : ℤ) * j) + cyclicRoot ℓ ^ (-(((k : ℕ) : ℤ) * j)))) ∧
    ∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      θ ≠ principal → θ ≠ a → (∀ k, θ ≠ b k) →
        (basis.representation θ).character (u ^ j) = 0 := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hℓ2 : ℓ ≠ 2 := by omega
  have hu : orderOf u = ℓ := by rw [← Nat.card_zpowers, ← hPu]; exact hP
  have hδsq : (δ : ℂ) * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hδnorm : Complex.normSq (δ : ℂ) = 1 := by rcases hδ with rfl | rfl <;> simp
  have hprinB : principal ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
    coefficientBlock_self_mem _ _ _
  let α : Finset.Icc 1 ((ℓ - 1) / 2) → ℂ := fun k =>
    cyclicRoot ℓ ^ (((k : ℕ) : ℤ) * j) + cyclicRoot ℓ ^ (-(((k : ℕ) : ℤ) * j))
  have hαreal : ∀ k, (α k).im = 0 := by
    intro k
    have hconj : starRingEnd ℂ (α k) = α k := by
      simp only [α, map_add, map_zpow₀, cyclicRoot_conj, inv_zpow', neg_neg]
      ring
    exact Complex.conj_eq_iff_im.mp hconj
  have hαsum : ∑ k, α k = -1 := by
    rw [Finset.sum_coe_sort (Finset.Icc 1 ((ℓ - 1) / 2))
      (fun i : ℕ => cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j)))]
    exact sum_cyclicRoot_pair_eq_neg_one hp hℓ2 hj
  have hαsq : ∑ k, α k ^ 2 = ℓ - 2 := by
    rw [Finset.sum_coe_sort (Finset.Icc 1 ((ℓ - 1) / 2))
      (fun i : ℕ => (cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j))) ^ 2)]
    exact sum_cyclicRoot_pair_sq hp hℓ2 hj
  have hαsumR : ∑ k, (α k).re = -1 := by
    rw [← Complex.re_sum, hαsum]
    simp
  have hαsqR : ∑ k, (α k).re ^ 2 = (ℓ : ℝ) - 2 := by
    have h : ∀ k, (α k ^ 2).re = (α k).re ^ 2 := fun k => by
      rw [sq, Complex.mul_re, hαreal k]
      ring
    rw [← Finset.sum_congr rfl fun k _ => h k, ← Complex.re_sum, hαsq]
    simp
  have hTj : ∀ k, 1 + δ * (basis.representation a).character (u ^ j) -
      δ * (basis.representation (b k)).character (u ^ j) = 2 - α k := by
    intro k
    rw [← hT k, inversionProjection_zpow basis ideal ℓ hℓ2 principal hprincipal P u hPu hP hindex]
    simp only [α]
    ring
  set A := (basis.representation a).character (u ^ j) with hA
  have hBk : ∀ k, (basis.representation (b k)).character (u ^ j) =
      δ * ((δ * A - 1) + α k) := by
    intro k
    linear_combination (-(δ : ℂ)) * hTj k - (basis.representation (b k)).character (u ^ j) * hδsq
  have hAβ : A = δ * ((δ * A - 1) + 1) := by linear_combination (-A) * hδsq
  have hmemP : u ^ j ∈ (P : Subgroup G) := hPu ▸ Subgroup.zpow_mem_zpowers u j
  have hne : u ^ j ≠ 1 := fun h => hj (by rwa [← orderOf_dvd_iff_zpow_eq_one, hu] at h)
  have hcol := prime_order_sylow_principal_column_norm basis ideal ℓ principal hprincipal P hP
    (u ^ j) hmemP hne
  have hcolR : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      Complex.normSq ((basis.representation θ).character (u ^ j)) = ℓ := by
    have h : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ((Complex.normSq ((basis.representation θ).character (u ^ j)) : ℝ) : ℂ) = (ℓ : ℂ) := by
      rw [← hcol]
      refine Finset.sum_congr rfl fun θ _ => ?_
      rw [Complex.mul_conj]
    exact_mod_cast h
  let S : Finset basis.index := insert principal (insert a (Finset.univ.image b))
  have hSB : S ⊆ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | rfl | ⟨k, rfl⟩
    · exact hprinB
    · exact haB
    · exact (hb k).1
  have hpa : principal ∉ insert a (Finset.univ.image b) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists]
    exact ⟨fun h => hao h.symm, fun k hk => (hb k).2.1 hk⟩
  have ha : a ∉ Finset.univ.image b := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun k hk => (hb k).2.2 hk
  have hnormsq : ∀ w : ℂ, w.im = 0 → Complex.normSq ((δ * A - 1) + w) =
      Complex.normSq (δ * A - 1) + w.re ^ 2 + 2 * (δ * A - 1).re * w.re := by
    intro w hw
    have hw2 : Complex.normSq w = w.re ^ 2 := by
      rw [Complex.normSq_apply, hw]
      ring
    rw [Complex.normSq_add, hw2, Complex.mul_re, Complex.conj_re, Complex.conj_im, hw]
    ring
  have hsumS : ∑ θ ∈ S, Complex.normSq ((basis.representation θ).character (u ^ j)) =
      ℓ + ((((ℓ - 1) / 2 : ℕ) : ℝ) + 1) * Complex.normSq (δ * A - 1) := by
    rw [Finset.sum_insert hpa, Finset.sum_insert ha,
      Finset.sum_image (fun x _ y _ h => hbinj h)]
    rw [hprincipal, Pi.one_apply, Complex.normSq_one]
    have h1 : Complex.normSq A = Complex.normSq (δ * A - 1) + 1 + 2 * (δ * A - 1).re := by
      conv_lhs => rw [hAβ]
      rw [Complex.normSq_mul, hδnorm, one_mul, hnormsq 1 Complex.one_im, Complex.one_re]
      ring
    have h2 : ∀ k, Complex.normSq ((basis.representation (b k)).character (u ^ j)) =
        Complex.normSq (δ * A - 1) + (α k).re ^ 2 + 2 * (δ * A - 1).re * (α k).re := by
      intro k
      rw [hBk k, Complex.normSq_mul, hδnorm, one_mul, hnormsq (α k) (hαreal k)]
    rw [h1, Finset.sum_congr rfl fun k _ => h2 k, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, ← Finset.mul_sum, hαsumR, hαsqR, Finset.card_univ, Fintype.card_coe,
      Nat.card_Icc, nsmul_eq_mul]
    have hr : (ℓ - 1) / 2 + 1 - 1 = (ℓ - 1) / 2 := by omega
    rw [hr]
    ring
  have hsplit := Finset.sum_sdiff hSB (f := fun θ =>
    Complex.normSq ((basis.representation θ).character (u ^ j)))
  rw [hsumS, hcolR] at hsplit
  have hrest_nonneg : 0 ≤ ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal \ S, Complex.normSq ((basis.representation θ).character (u ^ j)) :=
    Finset.sum_nonneg fun θ _ => Complex.normSq_nonneg _
  have hβ0 : Complex.normSq (δ * A - 1) = 0 := by
    have hnn := Complex.normSq_nonneg (δ * A - 1)
    have hrpos : (0 : ℝ) < (((ℓ - 1) / 2 : ℕ) : ℝ) + 1 := by positivity
    nlinarith
  have hrest : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal \ S,
      Complex.normSq ((basis.representation θ).character (u ^ j)) = 0 := by
    rw [hβ0, mul_zero, add_zero] at hsplit
    linarith
  have hβ : δ * A - 1 = 0 := Complex.normSq_eq_zero.mp hβ0
  refine ⟨?_, fun k => ?_, fun θ hθ hθo hθa hθb => ?_⟩
  · rw [hAβ, hβ, zero_add, mul_one]
  · rw [hBk k, hβ, zero_add]
  · have hθS : θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal \ S := by
      refine Finset.mem_sdiff.mpr ⟨hθ, ?_⟩
      simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
        not_exists]
      exact ⟨hθo, hθa, fun k hk => hθb k hk.symm⟩
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun θ _ => Complex.normSq_nonneg
      ((basis.representation θ).character (u ^ j))).mp hrest θ hθS
    exact Complex.normSq_eq_zero.mp h

end Values

theorem prime_inversion_weighted_identity (f a₁ a₂ δ : ℂ) (hδ : δ = 1 ∨ δ = -1) (hf : f ≠ 0)
    (hfδ : f + δ ≠ 0) :
    1 + a₁ * a₂ * δ / f + (a₁ + δ) * (a₂ + δ) * δ / (f + δ) * (-1) =
      (f - a₁) * (f - a₂) / (f * (f + δ)) := by
  rcases hδ with rfl | rfl
  · field_simp
    ring
  · field_simp
    ring

section Main

variable [Fintype G]

theorem characterPairing_one_add_sub_left (c : ℂ) (F F' g : G → ℂ) :
    characterPairing (fun x => 1 + c * F x - c * F' x) g =
      characterPairing (fun _ => 1) g + c * characterPairing F g - c * characterPairing F' g := by
  unfold characterPairing
  have h : ∀ x : G, (1 + c * F x - c * F' x) * g x⁻¹ =
      1 * g x⁻¹ + c * (F x * g x⁻¹) - c * (F' x * g x⁻¹) := fun x => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem prime_order_sylow_inversion_normalizer_exact_principal_block_family
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ]
    (hℓ : 5 ≤ ℓ) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2) :
    ∃ (δ : ℤ) (χ : basis.index) (ψ : ℕ → basis.index),
      (δ = 1 ∨ δ = -1) ∧ χ ≠ principal ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ψ i ≠ principal ∧ ψ i ≠ χ) ∧
      Set.InjOn ψ (Finset.Icc 1 ((ℓ - 1) / 2)) ∧
      coefficientBlock basis (localizedComplexIntegerRing ideal) principal =
        insert principal (insert χ ((Finset.Icc 1 ((ℓ - 1) / 2)).image ψ)) ∧
      (∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal, ∀ g : G,
        starRingEnd ℂ ((basis.representation θ).character g) =
          (basis.representation θ).character g) ∧
      0 < (Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), (basis.representation (ψ i)).character 1 =
        (basis.representation χ).character 1 + δ) ∧
      (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ∀ x : G, ¬ ℓ ∣ orderOf x →
        (basis.representation (ψ i)).character x = (basis.representation χ).character x + δ) ∧
      (∀ j ∈ Finset.Icc 1 (ℓ - 1), ∀ y ∈ Subgroup.centralizer (P : Set G), ¬ ℓ ∣ orderOf y →
        (basis.representation χ).character (u ^ j * y) = δ ∧
        ∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
          (basis.representation (ψ i)).character (u ^ j * y) =
            δ * (Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ ((i * j : ℕ) : ℤ) +
              Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ (-((i * j : ℕ) : ℤ)))) ∧
      (∀ z : G, ℓ ∣ orderOf z → ∃ j ∈ Finset.Icc 1 (ℓ - 1),
        ∃ y ∈ Subgroup.centralizer (P : Set G), ¬ ℓ ∣ orderOf y ∧ IsConj z (u ^ j * y)) ∧
      ∀ x₁ x₂ z : G, ¬ ℓ ∣ orderOf x₁ → ¬ ℓ ∣ orderOf x₂ → ℓ ∣ orderOf z →
        ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation θ).character x₁ * (basis.representation θ).character x₂ *
            (basis.representation θ).character z / (basis.representation θ).character 1 =
          ((basis.representation χ).character 1 - (basis.representation χ).character x₁) *
            ((basis.representation χ).character 1 - (basis.representation χ).character x₂) /
              ((basis.representation χ).character 1 *
                ((basis.representation χ).character 1 + δ)) := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓpos : 0 < ℓ := hp.pos
  have hu : orderOf u = ℓ := by rw [← Nat.card_zpowers, ← hPu]; exact hP
  have hupow : u ^ ℓ = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hPset : (P : Set G) = (Subgroup.zpowers u : Set G) := by rw [← hPu]; rfl
  have hindex' : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2 := by
    rw [← hPset]
    exact hindex
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set r := (ℓ - 1) / 2 with hr
  have hprinB : principal ∈ B := coefficientBlock_self_mem _ _ _
  obtain ⟨a, b, δ, haB, hao, hbinj, hb, hδ, hbdeg, hapos, hT⟩ :=
    prime_inversion_family_decomposition basis ideal ℓ hℓ principal hprincipal P u hPu hP hindex'
  have hδsq : (δ : ℂ) * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hval := fun (j : ℤ) (hj : ¬ (ℓ : ℤ) ∣ j) =>
    prime_inversion_values_at_powers basis ideal ℓ hℓ principal hprincipal P u hPu hP hindex' a b
      δ haB hao hbinj hb hδ hT hj
  have hreg : ∀ (k : Finset.Icc 1 r) (x : G), ¬ ℓ ∣ orderOf x →
      (basis.representation (b k)).character x = (basis.representation a).character x + δ := by
    intro k x hx
    have h0 := principalCyclicProjection_eq_zero_of_regular basis ideal ℓ principal hu
      (inversionTwist u ℓ ((k : ℕ) : ℤ)) (inversionTwist_one hu _) hx
    rw [hT k x] at h0
    linear_combination (-(δ : ℂ)) * h0 +
      ((basis.representation a).character x - (basis.representation (b k)).character x) * hδsq
  have hconst : ∀ θ ∈ B, ∀ (j : ℕ), j ∈ Finset.Icc 1 (ℓ - 1) →
      ∀ y ∈ Subgroup.centralizer (P : Set G), ¬ ℓ ∣ orderOf y →
        (basis.representation θ).character (u ^ j * y) =
          (basis.representation θ).character (u ^ j) := by
    intro θ hθ j hj y hy hyreg
    have hjmem := Finset.mem_Icc.mp hj
    have hmemP : u ^ j ∈ (P : Subgroup G) := hPu ▸ Subgroup.npow_mem_zpowers u j
    have hne : u ^ j ≠ 1 := by
      intro h
      have h' := orderOf_dvd_of_pow_eq_one h
      rw [hu] at h'
      have := Nat.le_of_dvd (by omega) h'
      omega
    have hcomm : Commute u y := by
      rw [hPset] at hy
      exact (CFSG.LyonsUnitaryFour.commute_of_mem_centralizer_zpowers u ⟨y, hy⟩)
    exact prime_sylow_principal_section_constant basis ideal ℓ principal hprincipal P hP hmemP hne
      (hcomm.pow_left j) hyreg hθ
  let ψ : ℕ → basis.index := fun i => if h : i ∈ Finset.Icc 1 r then b ⟨i, h⟩ else principal
  have hψ : ∀ i (h : i ∈ Finset.Icc 1 r), ψ i = b ⟨i, h⟩ := fun i h => by
    simp only [ψ, h, ↓reduceDIte]
  have himage : (Finset.Icc 1 r).image ψ = Finset.univ.image b := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, (hψ i hi).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, hψ k k.2⟩
  have hGfactor : (Nat.card G).factorization ℓ = 1 := by
    have h := P.card_eq_multiplicity
    rw [hP] at h
    exact Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one ℓ).symm)
  have hBeq : B = insert principal (insert a (Finset.univ.image b)) := by
    apply Finset.Subset.antisymm
    · intro θ hθ
      by_contra hθS
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
        not_exists] at hθS
      obtain ⟨hθo, hθa, hθb⟩ := hθS
      have hvan : ∀ v : ℕ, 0 < v → v < ℓ → (basis.representation θ).character (u ^ v) = 0 := by
        intro v hv0 hvl
        have hvj : ¬ (ℓ : ℤ) ∣ (v : ℤ) := by
          intro h
          have h' := Int.le_of_dvd (by omega) h
          omega
        have h := (hval v hvj).2.2 θ hθ hθo hθa (fun k hk => hθb k hk.symm)
        rwa [zpow_natCast] at h
      obtain ⟨mθ, hmθ⟩ := cyclicMultiplicity_natural (basis.representation θ) u hℓpos hupow 0
      have hmult : cyclicMultiplicity (basis.representation θ).character u ℓ 0 =
          (ℓ : ℂ)⁻¹ * (basis.representation θ).character 1 := by
        unfold cyclicMultiplicity
        rw [Finset.sum_eq_single 0]
        · simp
        · intro v hv hv0
          rw [hvan v (Nat.pos_of_ne_zero hv0) (Finset.mem_range.mp hv), zero_mul]
        · intro h
          exact absurd (Finset.mem_range.mpr hℓpos) h
      rw [hmult, (label_character_one basis θ).1] at hmθ
      have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hdeg : Module.finrank ℂ (basis.representation θ).vector = ℓ * mθ := by
        have h : (Module.finrank ℂ (basis.representation θ).vector : ℂ) = ℓ * mθ := by
          field_simp at hmθ
          linear_combination hmθ
        exact_mod_cast h
      have hdvd : ℓ ^ (Nat.card G).factorization ℓ ∣
          Module.finrank ℂ (basis.representation θ).vector := by
        rw [hGfactor, pow_one, hdeg]
        exact dvd_mul_right ℓ mθ
      obtain ⟨hsingle, -⟩ :=
        full_prime_part_character_degree_singleton_block_singular_vanishing basis ideal ℓ θ hdvd
      have hblock := coefficientBlock_eq_of_mem basis (localizedComplexIntegerRing ideal) hθ
      rw [hsingle] at hblock
      have hpθ : principal ∈ ({θ} : Finset basis.index) := by
        rw [hblock]
        exact hprinB
      exact hθo (Finset.mem_singleton.mp hpθ).symm
    · intro θ hθ
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hθ
      rcases hθ with rfl | rfl | ⟨k, rfl⟩
      · exact hprinB
      · exact haB
      · exact (hb k).1
  have hclass : ∀ (θ : basis.index) (g h : G), IsConj g h →
      (basis.representation θ).character g = (basis.representation θ).character h := by
    intro θ g h hgh
    obtain ⟨c, hc⟩ := isConj_iff.mp hgh
    rw [← hc]
    simp only [FiniteComplexRepresentation.character, Representation.char_conj]
  have hFreal : ∀ (k : Finset.Icc 1 r) (g : G),
      starRingEnd ℂ (1 + δ * (basis.representation a).character g -
        δ * (basis.representation (b k)).character g) =
      1 + δ * (basis.representation a).character g -
        δ * (basis.representation (b k)).character g := by
    intro k g
    by_cases hg : ℓ ∣ orderOf g
    · obtain ⟨j, hj, y, hy, hyreg, hconj⟩ := exists_isConj_pow_mul_of_dvd_orderOf P u hPu hP hg
      have hjmem := Finset.mem_Icc.mp hj
      have hjz : ¬ (ℓ : ℤ) ∣ (j : ℤ) := by
        intro h
        have h' := Int.le_of_dvd (by omega) h
        omega
      have hv := hval j hjz
      rw [hclass a g _ hconj, hclass (b k) g _ hconj, hconst a haB j hj y hy hyreg,
        hconst (b k) (hb k).1 j hj y hy hyreg, ← zpow_natCast, hv.1, hv.2.1 k]
      simp only [map_sub, map_add, map_mul, map_one, map_intCast, map_zpow₀,
        cyclicRoot_conj, inv_zpow', neg_neg]
      ring
    · rw [← hT k g, principalCyclicProjection_eq_zero_of_regular basis ideal ℓ principal hu
        (inversionTwist u ℓ ((k : ℕ) : ℤ)) (inversionTwist_one hu _) hg, map_zero]
  have hreal : ∀ (k : Finset.Icc 1 r) (g : G),
      starRingEnd ℂ ((basis.representation a).character g) = (basis.representation a).character g ∧
      starRingEnd ℂ ((basis.representation (b k)).character g) =
        (basis.representation (b k)).character g := by
    intro k
    obtain ⟨a', ha'⟩ := exists_conj_label basis a
    obtain ⟨b', hb'⟩ := exists_conj_label basis (b k)
    have hfun : (fun g => 1 + (δ : ℂ) * (basis.representation a').character g -
        δ * (basis.representation b').character g) =
        fun g => 1 + (δ : ℂ) * (basis.representation a).character g -
          δ * (basis.representation (b k)).character g := by
      funext g
      rw [ha', hb', ← hFreal k g]
      simp only [map_sub, map_add, map_mul, map_one, map_intCast]
    have hpair := fun (θ : basis.index) => congrArg
      (fun F => characterPairing F (basis.representation θ).character) hfun
    have hδ0 : (δ : ℂ) ≠ 0 := by rcases hδ with rfl | rfl <;> norm_num
    have haa : a' = a := by
      have h := hpair a
      simp only [characterPairing_one_add_sub_left, characterPairing_label_label] at h
      have hba : b k ≠ a := (hb k).2.2
      simp only [hba, ↓reduceIte] at h
      by_contra hne
      simp only [hne, ↓reduceIte] at h
      by_cases hb'a : b' = a
      · simp only [hb'a, ↓reduceIte] at h
        apply hδ0
        linear_combination (-1 / 2 : ℂ) * h
      · simp only [hb'a, ↓reduceIte] at h
        apply hδ0
        linear_combination (-1 : ℂ) * h
    have hbb : b' = b k := by
      have h := hpair (b k)
      simp only [characterPairing_one_add_sub_left, characterPairing_label_label, haa] at h
      have hab : a ≠ b k := fun h' => (hb k).2.2 h'.symm
      simp only [hab, ↓reduceIte] at h
      by_contra hne
      simp only [hne, ↓reduceIte] at h
      apply hδ0
      linear_combination h
    refine fun g => ⟨?_, ?_⟩
    · rw [← ha' g, haa]
    · rw [← hb' g, hbb]
  have hk₀ : (1 : ℕ) ∈ Finset.Icc 1 r := Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩
  refine ⟨δ, a, ψ, hδ, hao, fun i hi => ?_, fun i hi i' hi' hii => ?_, ?_, ?_, hapos,
    fun i hi => ?_, fun i hi x hx => ?_, fun j hj y hy hyreg => ?_,
    fun z hz => exists_isConj_pow_mul_of_dvd_orderOf P u hPu hP hz,
    fun x₁ x₂ z hx₁ hx₂ hz => ?_⟩
  · rw [hψ i hi]
    exact ⟨(hb _).2.1, (hb _).2.2⟩
  · have hi' : i' ∈ Finset.Icc 1 r := hi'
    have hi'' : i ∈ Finset.Icc 1 r := hi
    have h := hbinj ((hψ i hi'').symm.trans (hii.trans (hψ i' hi')))
    exact congrArg Subtype.val h
  · rw [hBeq, himage]
  · intro θ hθ g
    rw [hBeq] at hθ
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hθ
    rcases hθ with rfl | rfl | ⟨k, rfl⟩
    · rw [hprincipal, Pi.one_apply, map_one]
    · exact (hreal ⟨1, hk₀⟩ g).1
    · exact (hreal k g).2
  · rw [hψ i hi]
    exact hreg _ 1 (by rw [orderOf_one]; exact hp.not_dvd_one)
  · rw [hψ i hi]
    exact hreg _ x hx
  · have hjmem := Finset.mem_Icc.mp hj
    have hjz : ¬ (ℓ : ℤ) ∣ (j : ℤ) := by
      intro h
      have h' := Int.le_of_dvd (by omega) h
      omega
    have hv := hval j hjz
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hconst a haB j hj y hy hyreg, ← zpow_natCast, hv.1]
    · rw [hψ i hi, hconst _ (hb _).1 j hj y hy hyreg, ← zpow_natCast, hv.2.1 ⟨i, hi⟩]
      push_cast
      rfl
  ·
    obtain ⟨j, hj, y, hy, hyreg, hconj⟩ := exists_isConj_pow_mul_of_dvd_orderOf P u hPu hP hz
    have hjmem := Finset.mem_Icc.mp hj
    have hjz : ¬ (ℓ : ℤ) ∣ (j : ℤ) := by
      intro h
      have h' := Int.le_of_dvd (by omega) h
      omega
    have hv := hval j hjz
    have hzval : ∀ θ ∈ B, (basis.representation θ).character z =
        (basis.representation θ).character (u ^ (j : ℤ)) := by
      intro θ hθ
      rw [hclass θ z _ hconj, hconst θ hθ j hj y hy hyreg, zpow_natCast]
    have hpa : principal ∉ insert a (Finset.univ.image b) := by
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
        not_exists]
      exact ⟨fun h => hao h.symm, fun k hk => (hb k).2.1 hk⟩
    have ha : a ∉ Finset.univ.image b := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun k hk => (hb k).2.2 hk
    rw [hBeq, Finset.sum_insert hpa, Finset.sum_insert ha,
      Finset.sum_image (fun x _ y _ h => hbinj h)]
    rw [hzval principal hprinB, hzval a haB, hprincipal]
    simp only [Pi.one_apply, mul_one, div_one]
    rw [hv.1]
    have hsumk : ∑ k : Finset.Icc 1 r, (basis.representation (b k)).character x₁ *
        (basis.representation (b k)).character x₂ * (basis.representation (b k)).character z /
          (basis.representation (b k)).character 1 =
        ((basis.representation a).character x₁ + δ) * ((basis.representation a).character x₂ + δ) *
          δ / ((basis.representation a).character 1 + δ) * (-1) := by
      have hαsum : ∑ k : Finset.Icc 1 r,
          (cyclicRoot ℓ ^ (((k : ℕ) : ℤ) * (j : ℤ)) +
            cyclicRoot ℓ ^ (-(((k : ℕ) : ℤ) * (j : ℤ)))) = -1 := by
        rw [Finset.sum_coe_sort (Finset.Icc 1 r)
          (fun i : ℕ => cyclicRoot ℓ ^ ((i : ℤ) * (j : ℤ)) +
            cyclicRoot ℓ ^ (-((i : ℤ) * (j : ℤ))))]
        exact sum_cyclicRoot_pair_eq_neg_one hp hℓ2 hjz
      rw [← hαsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hzval (b k) (hb k).1, hv.2.1 k, hreg k x₁ hx₁, hreg k x₂ hx₂,
        hreg k 1 (by rw [orderOf_one]; exact hp.not_dvd_one)]
      ring
    rw [hsumk]
    have hf : (basis.representation a).character 1 ≠ 0 := by
      rw [(label_character_one basis a).1]
      exact Nat.cast_ne_zero.mpr (label_character_one basis a).2.ne'
    have hfδ : (basis.representation a).character 1 + δ ≠ 0 := by
      rw [(label_character_one basis a).1]
      have h : ((Module.finrank ℂ (basis.representation a).vector : ℤ) + δ : ℤ) ≠ 0 := hapos.ne'
      exact_mod_cast h
    have hδ' : (δ : ℂ) = 1 ∨ (δ : ℂ) = -1 := by
      rcases hδ with rfl | rfl
      · left
        norm_num
      · right
        norm_num
    have hid := prime_inversion_weighted_identity ((basis.representation a).character 1)
      ((basis.representation a).character x₁) ((basis.representation a).character x₂) δ hδ' hf
      hfδ
    rw [← hid]
    ring

end Main

end CFSG.Semidihedral.Principal
