module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchStatement
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchCharacter
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchOrder
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchLemmaOne
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierGaps

public section

open scoped Classical

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.TwoRankLowerBound.Helpers
open CFSG.Semidihedral.Principal
  (actual_field_factor_one_nontrivial_fixed_core_is_regular_and_has_no_inverted_odd_factor)
open CFSG.Semidihedral.StationaryConfinement
  (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element)

theorem nat_dvd_gcd_mul_of_dvd_mul {c X Y : ℕ} (h : c ∣ X * Y) : c ∣ Nat.gcd c X * Y := by
  have h1 : c ∣ Nat.gcd (X * Y) (c * Y) := Nat.dvd_gcd h (dvd_mul_right c Y)
  rwa [Nat.gcd_mul_right, Nat.gcd_comm] at h1

theorem dvd_of_dvd_mul_of_odd_prime {c M L : ℕ} (hc : c ∣ M * L) (hM : 2 ∣ M) (hL : L ≠ 0)
    (hodd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ L → ¬ ℓ ∣ c) (h4 : ¬ 4 ∣ c) : c ∣ M := by
  have hg2 : Nat.gcd c L ∣ 2 := by
    obtain ⟨j, g', hg'odd, hg⟩ :=
      Nat.exists_eq_two_pow_mul_odd (n := Nat.gcd c L) (Nat.gcd_ne_zero_right hL)
    have hg'1 : g' = 1 := by
      by_contra hne
      obtain ⟨ℓ, hℓ, hℓg⟩ := Nat.exists_prime_and_dvd hne
      have hℓ2 : ℓ ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hg'odd) (even_iff_two_dvd.mpr hℓg)
      have hℓgcd : ℓ ∣ Nat.gcd c L := hg ▸ dvd_mul_of_dvd_right hℓg _
      exact hodd ℓ hℓ hℓ2 (hℓgcd.trans (Nat.gcd_dvd_right c L))
        (hℓgcd.trans (Nat.gcd_dvd_left c L))
    rw [hg, hg'1, mul_one]
    rcases j with _ | _ | j
    · simp
    · simp
    · exfalso
      apply h4
      have h5 : Nat.gcd c L = 2 ^ (j + 2) := by rw [hg, hg'1, mul_one]
      have h6 : 4 ∣ 2 ^ (j + 2) := by
        rw [pow_add]
        exact dvd_mul_left 4 _
      exact h6.trans (h5 ▸ Nat.gcd_dvd_left c L)
  have hc2 : c ∣ M * 2 := by
    have h1 := nat_dvd_gcd_mul_of_dvd_mul (c := c) (X := L) (Y := M) (by rw [mul_comm]; exact hc)
    exact h1.trans (by rw [mul_comm M 2]; exact Nat.mul_dvd_mul_right hg2 M)
  obtain ⟨M', rfl⟩ := hM
  have hc4 : c ∣ 4 * M' := by
    have : 2 * M' * 2 = 4 * M' := by ring
    rwa [this] at hc2
  have hg4 : Nat.gcd c 4 ∣ 2 := by
    have h1 : Nat.gcd c 4 ∣ 4 := Nat.gcd_dvd_right c 4
    have h2 : Nat.gcd c 4 ≠ 4 := fun h => h4 (h ▸ Nat.gcd_dvd_left c 4)
    have h3 : Nat.gcd c 4 ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨h1, by norm_num⟩
    have : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [this] at h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at h3
    rcases h3 with h | h | h
    · rw [h]
      exact one_dvd 2
    · rw [h]
    · exact absurd h h2
  exact (nat_dvd_gcd_mul_of_dvd_mul hc4).trans (Nat.mul_dvd_mul_right hg4 M')

theorem not_modEq_rotation {n : ℕ} (hn : 4 ≤ n) {v : ℤ} (hv : v = 1 ∨ v = 2) :
    ¬ v ≡ 0 [ZMOD modulus n] ∧ ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
  have h8 : 8 ≤ modulus n := by
    unfold modulus
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM : (modulus n : ℤ) = 2 * ((modulus n / 2 : ℕ) : ℤ) := by
    have : modulus n = 2 * (modulus n / 2) := by
      unfold modulus
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
      omega
    exact_mod_cast this
  have hv0 : 0 < v ∧ v < modulus n / 2 := by
    rcases hv with rfl | rfl <;> constructor <;> push_cast <;> omega
  constructor
  · intro h
    have := Int.emod_emod_of_dvd v (dvd_refl (modulus n : ℤ))
    rw [Int.ModEq, Int.zero_emod, Int.emod_eq_of_lt hv0.1.le (by omega)] at h
    omega
  · intro h
    rw [Int.ModEq, Int.emod_eq_of_lt hv0.1.le (by omega),
      Int.emod_eq_of_lt (by positivity) (by omega)] at h
    omega

theorem eq_of_unitary_degree_eq {ι : Type*} {deg : ι → ℤ} {a b c d : ι} {q : ℤ} (hq : 3 ≤ q)
    (ha : deg a = 1) (hb : deg b = q ^ 3) (hc : deg c = q ^ 2 - 1 * q + 1)
    (hd : deg d = q * (q ^ 2 - 1 * q + 1)) {x y : ι}
    (hx : x = a ∨ x = b ∨ x = c ∨ x = d) (hy : y = a ∨ y = b ∨ y = c ∨ y = d)
    (hxy : deg x = deg y) : x = y := by
  have h1 : (1 : ℤ) < q := by omega
  have hq2 : q < q ^ 2 := by nlinarith
  have hq3 : q ^ 2 < q ^ 3 := by nlinarith
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso; nlinarith [hxy, ha, hb, hc, hd])

theorem unitary_character_data
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq1 : p ^ f % 4 = 1)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hval : 3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) : ℤ) ≤
      padicValNat p (Nat.card G))
    {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
    (hD : UnitaryLocalData t p f F κ)
    (hG : Nat.card G = 2 * Nat.card (N t) * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1)) :
    ∃ χ₁ ψ : G → ℂ, χ₁ ∈ CFSG.BlocksIrr G ∧ χ₁ 1 = (((p ^ f) ^ 3 : ℕ) : ℂ) ∧
      ψ ∈ CFSG.BlocksIrr G ∧ ψ 1 = (((p ^ f) ^ 3 + 1 : ℕ) : ℂ) ∧
      (∀ x : G, Odd (orderOf x) → ψ x = χ₁ x + 1) ∧
      ∀ p₀ : ℕ, p₀.Prime → p₀ ≠ 2 → p₀ ∣ p ^ f - 1 → ∀ g : G, ¬ p * p₀ ∣ orderOf g := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hG2 : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  obtain ⟨-, ht2, hcentR, -, -, -⟩ := Principal.supplied_t_s_facts hn fS ht
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal, hmax, h2⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2
  obtain ⟨F', hF', hF'fin, ρ, hcard, -, -, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam,
      hdeg, hvalues⟩ :=
    Principal.actual_simple_layer_characteristic_valuation_degree_formulas hGnonab n hn S fS t ht2
      hnonab hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal fS hcentR hval
  have hq1' : Nat.card F' % 4 = 1 := by rw [hcard]; exact hq1
  have he : (if Nat.card F' % 4 = 1 then (1 : ℤ) else -1) = 1 := ite_eq_left_iff.mpr
    (fun h => absurd hq1' h)
  rw [he] at hfam hvalues
  obtain ⟨hδ₁, hδ₂, hδ₃, -, hf₁, hf₂, hf₃, -, -, hν1, -, -⟩ := hvalues
  have hq3 : 3 ≤ Nat.card F' := by
    rw [hcard]
    obtain ⟨m, hm⟩ := hpodd
    calc 3 ≤ p := by have := hp.two_le; omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hqodd : Odd (Nat.card F') := by rw [hcard]; exact hpodd.pow
  obtain ⟨hrot, -⟩ := Principal.actual_principal_rotation_values_and_congruences hG2 hn ht2 hnonab
    basis ideal principal hprincipal localBasis localPrincipal (Nat.card F') hq3 hqodd 1
    (fun _ => rfl) (fun h => by omega) _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg fS hcentR
  obtain ⟨-, -, -, -, -, hnd, -, -, -, -, -, hB, -, hodd, -, hrel⟩ := hfam
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  have hmemB : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₂B : χ₂ ∈ B := hmemB χ₂ (by simp)
  have hχ₃B : χ₃ ∈ B := hmemB χ₃ (by simp)
  have hr1 := hrot 1 (not_modEq_rotation hn (Or.inl rfl)).1 (not_modEq_rotation hn (Or.inl rfl)).2
  have hr2 := hrot 2 (not_modEq_rotation hn (Or.inr rfl)).1 (not_modEq_rotation hn (Or.inr rfl)).2
  rw [zpow_one] at hr1
  rw [show ((fS (r n) : G) ^ (2 : ℤ)) = (fS (r n) : G) ^ 2 from zpow_natCast _ 2] at hr2
  have hχ₂ : (basis.representation χ₂).character (fS (r n) : G) ≠
      (basis.representation χ₂).character ((fS (r n) : G) ^ 2) := by
    rw [hr1.2.1, hr2.2.1, hδ₂]
    norm_num
  have hδ₃' : δ₃ = -1 := by rw [hδ₃]
  have hχ₃ : (basis.representation χ₃).character (fS (r n) : G) ≠
      (basis.representation χ₃).character ((fS (r n) : G) ^ 2) := by
    rw [hr1.2.2, hr2.2.2, hδ₃']
    norm_num
  set q' := Nat.card F' with hq'
  have hdeg0 : Module.finrank ℂ (basis.representation principal).vector = 1 := by
    have h1 := (Principal.basis_character_one basis principal).1
    rw [hprincipal, Pi.one_apply] at h1
    exact_mod_cast h1.symm
  have hq'3 : (3 : ℤ) ≤ q' := by exact_mod_cast hq3
  have hdegs : ∀ c ∈ B, ∀ c' ∈ B, Odd (Module.finrank ℂ (basis.representation c).vector) →
      Module.finrank ℂ (basis.representation c).vector =
        Module.finrank ℂ (basis.representation c').vector → c = c' := by
    intro c hc c' hc' hoddc hcc'
    have hoddc' : Odd (Module.finrank ℂ (basis.representation c').vector) := hcc' ▸ hoddc
    exact eq_of_unitary_degree_eq
      (deg := fun l => (Module.finrank ℂ (basis.representation l).vector : ℤ))
      hq'3 (by simp [hdeg0]) hf₁ hf₂ hf₃ ((hodd c hc).mp hoddc) ((hodd c' hc').mp hoddc')
      (by exact_mod_cast hcc')
  have hχ₁deg : Module.finrank ℂ (basis.representation χ₁).vector = (p ^ f) ^ 3 := by
    rw [← hcard]
    exact_mod_cast hf₁
  have hL1 := not_dvd_orderOf_mul_of_dvd_sub_one hD n hn S fS ht hG basis ideal principal
    hprincipal χ₁ χ₂ χ₃ hodd hdegs hχ₂B hχ₃B hχ₁deg hχ₂ hχ₃
  have hk0 : (0 : ℕ) ∈ Finset.range (2 ^ (n - 3)) := by
    simp only [Finset.mem_range]
    positivity
  refine ⟨(basis.representation χ₁).character, (basis.representation (ν 0)).character,
    ⟨_, inferInstance, inferInstance, inferInstance, (basis.representation χ₁).representation,
      basis.irreducible χ₁, rfl⟩, ?_,
    ⟨_, inferInstance, inferInstance, inferInstance, (basis.representation (ν 0)).representation,
      basis.irreducible (ν 0), rfl⟩, ?_, ?_, hL1⟩
  · rw [(Principal.basis_character_one basis χ₁).1, hχ₁deg]
  · rw [hν1 0 hk0, hcard]
    push_cast
    ring
  · intro x hx
    rw [((hrel x hx).2.1 0 hk0), hδ₁]
    push_cast
    ring

theorem unitary_centralizer_bound {G : Type} [Group G] [Finite G] {t : G} {p f : ℕ}
    {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
    (hD : UnitaryLocalData t p f F κ) (hinv : ∀ y : G, orderOf y = 2 → IsConj y t)
    (hG : Nat.card G = 2 * Nat.card (N t) * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1))
    {χ₁ ψ : G → ℂ} (hχ₁ : χ₁ ∈ CFSG.BlocksIrr G) (hχ₁deg : χ₁ 1 = (((p ^ f) ^ 3 : ℕ) : ℂ))
    (hψ : ψ ∈ CFSG.BlocksIrr G) (hψdeg : ψ 1 = (((p ^ f) ^ 3 + 1 : ℕ) : ℂ))
    (hψχ : ∀ x : G, Odd (orderOf x) → ψ x = χ₁ x + 1)
    (hL1 : ∀ p₀ : ℕ, p₀.Prime → p₀ ≠ 2 → p₀ ∣ p ^ f - 1 → ∀ g : G, ¬ p * p₀ ∣ orderOf g)
    {u : G} (hu1 : u ≠ 1) (hup : ∃ k : ℕ, orderOf u = p ^ k) :
    Nat.card (Subgroup.centralizer {u}) ∣ Nat.card (unitaryK t) * (p ^ f) ^ 3 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hp := hD.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hup
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hu1 hk
    · omega
  have hpu : p ∣ orderOf u := by
    rw [hk]
    exact dvd_pow_self p (by omega)
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hD.ne_two
  have hoddu : Odd (orderOf u) := by
    rw [hk]
    exact hpodd.pow
  set a := Nat.card (N t)
  set q := p ^ f with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
  have hKp := (unitaryK_properties hD).2.2.1
  rw [(unitaryLocalData_card hD).1] at hKp
  have hpq : p ∣ q := dvd_pow_self p (by have := hD.one_le; omega)
  have hnot : ¬ p ∣ 2 * a * (q - 1) * (q ^ 3 + 1) := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact hKp h2
      · have h3 : p ∣ q - (q - 1) := Nat.dvd_sub hpq h2
        rw [Nat.sub_sub_self hq1] at h3
        exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    · have h4 : p ∣ q ^ 3 := dvd_pow hpq (by norm_num)
      have h5 : p ∣ q ^ 3 + 1 - q ^ 3 := Nat.dvd_sub h1 h4
      rw [Nat.add_sub_cancel_left] at h5
      exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
  have hfac : (Nat.card G).factorization p = 3 * f := by
    rw [hG, show 2 * a * q ^ 3 * (q - 1) * (q ^ 3 + 1) =
      p ^ (3 * f) * (2 * a * (q - 1) * (q ^ 3 + 1)) by rw [hqdef, ← pow_mul]; ring]
    exact factorization_prime_pow_mul hp hnot
  have hχ₁u : χ₁ u = 0 := by
    obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ₁
    have hdim : Module.finrank ℂ V = q ^ 3 := by
      rw [Representation.char_one] at hχ₁deg
      exact_mod_cast hχ₁deg
    exact CFSG.DefectZeroSylow.character_eq_zero_of_finrank_dvd ρ hirr
      (by rw [hfac, hdim, hqdef, ← pow_mul, mul_comm]) hpu
  have hψu : ψ u = 1 := by rw [hψχ u hoddu, hχ₁u, zero_add]
  have hdvd1 := card_centralizer_mul_dvd_of_character_eq_one hψ hψdeg hψu
  have hdvd2 : Nat.card (Subgroup.centralizer {u}) ∣ 2 * a * q ^ 3 * (q - 1) := by
    rw [hG, show 2 * a * q ^ 3 * (q - 1) * (q ^ 3 + 1) = (2 * a * q ^ 3 * (q - 1)) * (q ^ 3 + 1)
      by ring] at hdvd1
    exact Nat.dvd_of_mul_dvd_mul_right (by positivity) hdvd1
  have hodd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ q - 1 →
      ¬ ℓ ∣ Nat.card (Subgroup.centralizer {u}) := by
    intro ℓ hℓ hℓ2 hℓq hℓC
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer {u}) ℓ hℓC
    have hvu : Commute u (v : G) := (Subgroup.mem_centralizer_singleton_iff.mp v.2).symm
    have hvo : orderOf (v : G) = ℓ := by rw [Subgroup.orderOf_coe, hv]
    have hℓp : ℓ ≠ p := by
      rintro rfl
      have h1 : ℓ ∣ q - (q - 1) := Nat.dvd_sub hpq hℓq
      rw [Nat.sub_sub_self hq1] at h1
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h1)
    have hcop : Nat.Coprime (orderOf u) (orderOf (v : G)) := by
      rw [hk, hvo]
      exact Nat.Coprime.pow_left k ((Nat.coprime_primes hp hℓ).mpr hℓp.symm)
    apply hL1 ℓ hℓ hℓ2 hℓq (u * v)
    rw [hvu.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hvo]
    exact Nat.mul_dvd_mul_right hpu ℓ
  have h4 := not_four_dvd_card_centralizer hD hinv hu1 ⟨k, hk⟩
  rw [(unitaryLocalData_card hD).1, show 2 * a * q ^ 3 = 2 * a * q ^ 3 from rfl]
  have hq0 : q - 1 ≠ 0 := by
    have : 1 < q := Nat.one_lt_pow (by have := hD.one_le; omega) hp.one_lt
    omega
  exact dvd_of_dvd_mul_of_odd_prime hdvd2 (dvd_mul_of_dvd_left (dvd_mul_right 2 a) _) hq0 hodd h4

theorem unitary_branch_of_d_value
    (hd : DValueStatement) :
    SimpleLayerFrontier.UnitaryBranchStatement := by
  intro G _ _ _ hGnonab hrecognition n hn S fS t ht _ hnonab hcentral hnc p f hp hpodd hf hq1
    hq5 hmodel hcov hY hA₀
  classical
  have hpne : p ≠ 2 := fun h => (Nat.not_even_iff_odd.mpr hpodd) (h ▸ even_two)
  have hG2 : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  obtain ⟨hz, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  obtain ⟨-, -, -, -, -, ⟨F, hF, hFfin, κ, hD⟩, -, -, hGcard⟩ :=
    unitary_order_formulas G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd
      hf hq1 hq5 hmodel hcov hY hA₀
  obtain ⟨hval, -⟩ :=
    actual_field_factor_one_nontrivial_fixed_core_is_regular_and_has_no_inverted_odd_factor
      G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq5 hmodel hcov hY
      hA₀
  obtain ⟨χ₁, ψ, hχ₁, hχ₁deg, hψ, hψdeg, hψχ, hL1⟩ :=
    unitary_character_data G hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq1 hmodel
      hval hD hGcard
  have hdv := hd G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq1 hq5
    hmodel hcov hY hA₀
  obtain ⟨htK, hKcent, hKp, hKconf'⟩ := unitaryK_properties hD
  have hconf := (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element
    G hGnonab hrecognition n hn S fS t (fS (s n)) ht2 hs2 hsC hst.symm hnonab hcentral hnc p f hp
    hpodd hf hq5 hmodel hcov).2.1
  obtain ⟨hSC, hNS⟩ := sylow_le_and_normalizer_le_centralizer n hn S fS ht
  obtain ⟨Q₀, H, hQ₀card, hQ₀comm, hQ₀C, hQ₀syl, -, -, hHQ₀, hHcyc, hKH, hHcard⟩ :=
    exists_unitary_local_subgroups hD n hn S fS ht
  have hinv : ∀ y : G, orderOf y = 2 → IsConj y t := fun y hy =>
    hz ▸ InvolutionFusion.ambient_involution_isConj_z n hn S fS hG2 y hy
  have hKcard := (unitaryLocalData_card hD).1
  have hG' : Nat.card G =
      Nat.card (unitaryK t) * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1) := by
    rw [hGcard, hKcard]
  have hd' : Nat.card (unitaryK t) * Nat.gcd (p ^ f + 1) 3 = p ^ f + 1 := by
    rw [hKcard]
    exact hdv
  exact statedClassicalModel_psu_of_centralizer_data hGnonab p f hp hpne hf t ht2 (unitaryK t) htK
    hKcent hKp (hKconf' hconf) S hSC hNS Q₀ hQ₀card hQ₀comm hQ₀C hQ₀syl H hHQ₀ hHcyc hKH hHcard
    (fun u hu1 hup => unitary_centralizer_bound hD hinv hGcard hχ₁ hχ₁deg hψ hψdeg hψχ hL1 hu1 hup)
    hG' hχ₁ hχ₁deg hd'

end CFSG.Semidihedral.UnitaryBranch
