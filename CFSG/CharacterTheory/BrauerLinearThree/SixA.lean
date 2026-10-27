module

public import CFSG.CharacterTheory.BrauerLinearThree.SixASylow
public import CFSG.CharacterTheory.BrauerLinearThree.SixBOrder
public import CFSG.CharacterTheory.CyclicBlocks.InertialIndexTwo
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers CFSG.Open
open CFSG.Semidihedral.Principal
  (full_prime_part_character_degree_singleton_block_singular_vanishing)

theorem rotation_index_conditions {m : ℕ} (hm : 2 ≤ m) {v : ℤ} (hv1 : 1 ≤ v) (hv2 : v ≤ 2) :
    ¬ v ≡ 0 [ZMOD (CFSG.Semidihedral.modulus (m + 2) : ℕ)] ∧
      ¬ v ≡ ((CFSG.Semidihedral.modulus (m + 2) / 2 : ℕ) : ℤ)
        [ZMOD (CFSG.Semidihedral.modulus (m + 2) : ℕ)] := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 ^ m := ⟨_, rfl⟩
  have hM : CFSG.Semidihedral.modulus (m + 2) = M * 2 := by
    rw [CFSG.Semidihedral.modulus, show m + 2 - 1 = m + 1 by omega, pow_succ, hMdef]
  have h4 : 4 ≤ M := by
    rw [hMdef]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [hM, Nat.mul_div_cancel _ (by norm_num)]
  constructor
  · intro h
    rw [Int.ModEq, Int.emod_eq_of_lt (by omega) (by push_cast; omega), Int.zero_emod] at h
    omega
  · intro h
    rw [Int.ModEq, Int.emod_eq_of_lt (by omega) (by push_cast; omega),
      Int.emod_eq_of_lt (by positivity) (by push_cast; omega)] at h
    omega

theorem eq_of_degree_eq_of_three {ι : Type*} (d : ι → ℕ) {χ₁ χ₂ χ₃ c c' : ι} {q : ℕ}
    (hq : 2 ≤ q) (hf₁ : d χ₁ = q ^ 3) (hf₂ : d χ₂ = q ^ 2 + q + 1)
    (hf₃ : d χ₃ = q * (q ^ 2 + q + 1)) (hc : c = χ₁ ∨ c = χ₂ ∨ c = χ₃)
    (hc' : c' = χ₁ ∨ c' = χ₂ ∨ c' = χ₃) (hcc' : d c = d c') : c = c' := by
  have hA : q ^ 3 ≠ q ^ 2 + q + 1 := by
    intro h
    nlinarith
  have hB : q ^ 3 ≠ q * (q ^ 2 + q + 1) := by
    intro h
    nlinarith
  have hC : q ^ 2 + q + 1 ≠ q * (q ^ 2 + q + 1) := by
    intro h
    nlinarith
  rcases hc with h | h | h <;> rcases hc' with h' | h' | h' <;> rw [h, h'] at hcc' <;>
    rw [h, h'] <;>
    first
    | rfl
    | (rw [hf₁, hf₂] at hcc'; exact absurd hcc' hA)
    | (rw [hf₂, hf₁] at hcc'; exact absurd hcc'.symm hA)
    | (rw [hf₁, hf₃] at hcc'; exact absurd hcc' hB)
    | (rw [hf₃, hf₁] at hcc'; exact absurd hcc'.symm hB)
    | (rw [hf₂, hf₃] at hcc'; exact absurd hcc' hC)
    | (rw [hf₃, hf₂] at hcc'; exact absurd hcc'.symm hC)

theorem exists_constant_character_of_inertial_index_two {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2)
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) r] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow r G) (hcyc : IsCyclic (P : Subgroup G))
    (hN : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2)
    (hP3 : 3 ≤ Nat.card P) (hPodd : Odd (Nat.card P))
    (huniq : ∀ c c' : basis.index, c ≠ principal → c' ≠ principal →
      (∀ g, starRingEnd ℂ ((basis.representation c).character g) =
        (basis.representation c).character g) →
      (∀ g, starRingEnd ℂ ((basis.representation c').character g) =
        (basis.representation c').character g) →
      Odd (Module.finrank ℂ (basis.representation c).vector) →
      Module.finrank ℂ (basis.representation c).vector =
        Module.finrank ℂ (basis.representation c').vector → c = c') :
    ∃ (Ψ : basis.index) (δ' : ℤ), Ψ ≠ principal ∧
      (∀ g, starRingEnd ℂ ((basis.representation Ψ).character g) =
        (basis.representation Ψ).character g) ∧
      Odd (Module.finrank ℂ (basis.representation Ψ).vector) ∧
      (∀ g : G, r ∣ orderOf g → (basis.representation Ψ).character g = δ') ∧
      (δ' = 1 ∨ δ' = -1) := by
  obtain ⟨ψ₁, ψ, δ, hδ, hψ₁ne, hinj, hψne, hψ₁val, hψdeg, hψ₁real, hψreal, h3⟩ :=
    CFSG.CyclicBlocks.principal_block_cyclic_sylow_inertial_index_two basis ideal r hr2 principal
      hprincipal P hcyc hN
  by_cases hodd1 : Odd (Module.finrank ℂ (basis.representation ψ₁).vector)
  · exact ⟨ψ₁, δ, hψ₁ne, hψ₁real, hodd1, hψ₁val, hδ⟩
  have hoddμ : ∀ μ' ∈ Finset.Icc 1 ((Nat.card P - 1) / 2),
      Odd (Module.finrank ℂ (basis.representation (ψ μ')).vector) := by
    intro μ' hμ'
    have hd := hψdeg μ' hμ'
    obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hodd1
    rw [ht] at hd
    rcases hδ with rfl | rfl
    · exact ⟨t, by push_cast at hd; omega⟩
    · refine ⟨t - 1, ?_⟩
      push_cast at hd
      omega
  have h1mem : 1 ∈ Finset.Icc 1 ((Nat.card P - 1) / 2) := by
    rw [Finset.mem_Icc]
    omega
  by_cases hP : Nat.card P = 3
  · refine ⟨ψ 1, -δ, (hψne 1 h1mem).1, hψreal 1 h1mem, hoddμ 1 h1mem, fun g hg => ?_, ?_⟩
    · rw [h3 hP g hg]
      push_cast
      ring
    · rcases hδ with rfl | rfl <;> norm_num
  exfalso
  have h2mem : 2 ∈ Finset.Icc 1 ((Nat.card P - 1) / 2) := by
    rw [Finset.mem_Icc]
    obtain ⟨t, ht⟩ := hPodd
    omega
  have hdeq : Module.finrank ℂ (basis.representation (ψ 1)).vector =
      Module.finrank ℂ (basis.representation (ψ 2)).vector := by
    have e1 := hψdeg 1 h1mem
    have e2 := hψdeg 2 h2mem
    omega
  have h12 := huniq (ψ 1) (ψ 2) (hψne 1 h1mem).1 (hψne 2 h2mem).1 (hψreal 1 h1mem)
    (hψreal 2 h2mem) (hoddμ 1 h1mem) hdeq
  exact absurd (hinj h1mem h2mem h12) (by norm_num)

open CFSG.Semidihedral in
theorem character_rotation_eq_of_singular {G : Type} [Group G] [Fintype G] {n : ℕ}
    (hn : 4 ≤ n) {S : Sylow 2 G} (e' : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {Ψ : basis.index}
    (hΨ : Ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) {δ' : ℤ}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hΨval : ∀ g : G, r ∣ orderOf g → (basis.representation Ψ).character g = δ') {y : G}
    (hy : Commute (e' (Semidihedral.r n) : G) y) {k : ℕ} (hyord : orderOf y = r ^ k)
    (hk : 1 ≤ k) {v : ℤ} (hv0 : ¬ v ≡ 0 [ZMOD modulus n])
    (hv1 : ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    (basis.representation Ψ).character ((e' (Semidihedral.r n) : G) ^ v) = δ' := by
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hyC : y ∈ Subgroup.centralizer {(e' (Semidihedral.r n) : G) ^ v} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hy.zpow_left v).eq).symm
  have hyodd : Odd (orderOf y) := by
    rw [hyord]
    exact hrodd.pow
  rw [← (Principal.noncentral_rotation_principal_section_columns hn e' basis ideal principal
    hprincipal).1 v hv0 hv1 Ψ hΨ y hyC hyodd]
  apply hΨval
  have hcop : Nat.Coprime (orderOf ((e' (Semidihedral.r n) : G) ^ v)) (orderOf y) := by
    rw [hyord]
    exact Nat.Coprime.coprime_dvd_left
      (Principal.suppliedRotation_zpow_orderOf_dvd (by omega) e' v)
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)))
  rw [(hy.zpow_left v).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hyord]
  exact dvd_mul_of_dvd_right (dvd_pow_self r (by omega)) _

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem exists_principal_two_block_characters
    [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {S : Sylow 2 G}
    (e' : SemidihedralGroup ((Nat.card F + 1).factorization 2 + 2) ≃* (S : Subgroup G))
    (hn4 : 4 ≤ (Nat.card F + 1).factorization 2 + 2)
    (he'J : (e' (CFSG.Semidihedral.r _) : G) ^
      (CFSG.Semidihedral.modulus ((Nat.card F + 1).factorization 2 + 2) / 2) = J)
    (he's : (e' (CFSG.Semidihedral.s _) : G) = invJ₁ φ) :
    ∃ χ₁ χ₂ χ₃ : basis.index,
      (∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        Odd (Module.finrank ℂ (basis.representation c).vector) →
          c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃) ∧
      Module.finrank ℂ (basis.representation χ₁).vector = Nat.card F ^ 3 ∧
      Module.finrank ℂ (basis.representation χ₂).vector = Nat.card F ^ 2 + Nat.card F + 1 ∧
      Module.finrank ℂ (basis.representation χ₃).vector =
        Nat.card F * (Nat.card F ^ 2 + Nat.card F + 1) ∧
      (basis.representation χ₂).character ((e' (CFSG.Semidihedral.r _) : G) ^ (1 : ℤ)) ≠
        (basis.representation χ₂).character ((e' (CFSG.Semidihedral.r _) : G) ^ (2 : ℤ)) ∧
      (basis.representation χ₃).character ((e' (CFSG.Semidihedral.r _) : G) ^ (1 : ℤ)) ≠
        (basis.representation χ₃).character ((e' (CFSG.Semidihedral.r _) : G) ^ (2 : ℤ)) := by
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
  obtain ⟨localBasis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer ({J} : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    CFSG.Semidihedral.Principal.finiteIrreducibleCharacterBasis_exists_principal_label localBasis
  obtain ⟨hvc, hvd⟩ := padicValNat_centralizers φ hZ hZodd h2 p f hp hF
  have hvG : padicValNat p (Nat.card G) = 3 * f := by
    have hcop := coprime_facts hZ
    rw [ringChar_eq_of_card hp hF] at hcop
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
      hprincipal localBasis localPrincipal hlocalPrincipal e' he'J hval
  obtain ⟨-, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg, hvals⟩ := hrest
  have hq' : Nat.card F' = Nat.card F := hF'.trans hF.symm
  have he : (if Nat.card F' % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    rw [hq']
    exact ite_eq_right_iff.mpr (fun h => by omega)
  have hq3 : 3 ≤ Nat.card F' := by omega
  have hqodd : Odd (Nat.card F') := by
    rw [hq']
    exact ⟨Nat.card F / 2, by omega⟩
  obtain ⟨hrot, -, -, -⟩ :=
    CFSG.Semidihedral.Principal.actual_principal_rotation_values_and_congruences
      (CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hnonab) hn4 hJ hnab basis ideal
      principal hprincipal localBasis localPrincipal (Nat.card F') hq3 hqodd
      (if Nat.card F' % 4 = 1 then 1 else -1) (fun h => by simp [h]) (fun h => by simp [h])
      _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg e' he'J
  obtain ⟨-, hδ₂, hδ₃, -, hf₁, hf₂, hf₃, -, -, -, -, -⟩ := hvals
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hodd, -, -⟩ := hfam
  rw [he, hq'] at hf₂ hf₃
  rw [hq'] at hf₁
  rw [he] at hδ₃
  obtain ⟨h10, h11⟩ := rotation_index_conditions (m := (Nat.card F + 1).factorization 2)
    (by omega) (v := 1) le_rfl (by norm_num)
  obtain ⟨h20, h21⟩ := rotation_index_conditions (m := (Nat.card F + 1).factorization 2)
    (by omega) (v := 2) (by norm_num) le_rfl
  obtain ⟨-, hχ₂1, hχ₃1⟩ := hrot 1 h10 h11
  obtain ⟨-, hχ₂2, hχ₃2⟩ := hrot 2 h20 h21
  refine ⟨χ₁, χ₂, χ₃, fun c hc hco => (hodd c hc).mp hco, by exact_mod_cast hf₁, ?_, ?_, ?_, ?_⟩
  · have : ((Module.finrank ℂ (basis.representation χ₂).vector : ℕ) : ℤ) =
        ((Nat.card F ^ 2 + Nat.card F + 1 : ℕ) : ℤ) := by
      rw [hf₂]
      push_cast
      ring
    exact_mod_cast this
  · have : ((Module.finrank ℂ (basis.representation χ₃).vector : ℕ) : ℤ) =
        ((Nat.card F * (Nat.card F ^ 2 + Nat.card F + 1) : ℕ) : ℤ) := by
      rw [hf₃]
      push_cast
      ring
    exact_mod_cast this
  · rw [hχ₂1, hχ₂2, hδ₂]
    norm_num
  · rw [hχ₃1, hχ₃2, hδ₃]
    norm_num

include φ hZ hZodd h2 hJ in
theorem not_dvd_card_centralizer_of_dvd_add_one
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) :
    ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 → ∀ r : ℕ, r.Prime → r ∣ Nat.card F + 1 → Odd r →
      ¬ r ∣ Nat.card (Subgroup.centralizer ({Q} : Set G)) := by
  classical
  intro Q hQ1 hQp r hr hrq hrodd hdvd
  have : Fintype G := Fintype.ofFinite G
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hrodd) even_two
  have hpc : ringChar F = p := ringChar_eq_of_card hp hF
  obtain ⟨K, _, _, μ, hμ⟩ := exists_nonsplit_torus hq
  obtain ⟨ζ, hζ, hζ2, -⟩ := exists_two_part hμ hq
  obtain ⟨hn4, S, e', he'r, he'J, he's⟩ := exists_semidihedral_sylow_of_element φ hZ hZodd h2 hJ
    hq (μ ζ) (by rw [orderOf_injective μ hμ.injective, hζ]) hζ2
    ((hμ.frob ζ).trans (map_pow μ ζ _))
  obtain ⟨η, P, hPη, hyord, hrel⟩ :=
    exists_torus_sylow_relIndex_eq_two φ hZ hZodd h2 hJ hμ hq hcard hr2 hrq
  have ha1 : 1 ≤ (Nat.card F + 1).factorization r :=
    Nat.Prime.factorization_pos_of_dvd hr (by omega) hrq
  have hcyc : IsCyclic (P : Subgroup G) := by
    rw [hPη]
    infer_instance
  have hPcard : Nat.card P = r ^ (Nat.card F + 1).factorization r := by
    rw [hPη, Nat.card_zpowers, hyord]
  have huy : Commute (e' (CFSG.Semidihedral.r _) : G) (linearCentralizerHom φ (μ η)) := by
    rw [he'r]
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm ζ η]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({Q} : Set G)) r
    hdvd
  have hxord : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
  have hxQ : Commute (x : G) Q := Subgroup.mem_centralizer_singleton_iff.mp x.2
  have hQord : orderOf Q = p := by
    rw [hpc] at hQp
    exact orderOf_eq_prime hQp hQ1
  have hrp : r ≠ p := by
    rintro rfl
    have hdq : r ∣ Nat.card F := by rw [hF]; exact dvd_pow_self r (by omega)
    have h1 := Nat.dvd_sub hrq hdq
    rw [Nat.add_sub_cancel_left] at h1
    exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
  have hxQord : orderOf ((x : G) * Q) = r * p := by
    rw [hxQ.orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [hxord, hQord]; exact (Nat.coprime_primes hr hp).mpr hrp), hxord, hQord]
  obtain ⟨basis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ :=
    CFSG.Semidihedral.Principal.finiteIrreducibleCharacterBasis_exists_principal_label basis
  obtain ⟨⟨id2, hmax2, h2mem⟩, hchar2⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : id2.IsMaximal := hmax2
  have : CharP (ComplexAlgebraicIntegers ⧸ id2) 2 := hchar2 id2 hmax2 h2mem
  obtain ⟨χ₁, χ₂, χ₃, hodd, hf₁, hf₂, hf₃, hχ₂, hχ₃⟩ :=
    exists_principal_two_block_characters φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hcard basis
      principal hprincipal id2 e' hn4 he'J he's
  have hreal : ∀ c : basis.index,
      (∀ g, starRingEnd ℂ ((basis.representation c).character g) =
        (basis.representation c).character g) →
      Odd (Module.finrank ℂ (basis.representation c).vector) → c ≠ principal →
      c ∈ coefficientBlock basis (localizedComplexIntegerRing id2) principal ∧
        (c = χ₁ ∨ c = χ₂ ∨ c = χ₃) := by
    intro c hcr hco hcp
    have hB :=
      CFSG.Semidihedral.Principal.real_valued_odd_degree_irreducible_mem_principal_two_block
        basis id2 principal hprincipal c hcr hco
    refine ⟨hB, ?_⟩
    rcases hodd c hB hco with h | h
    · exact absurd h hcp
    · exact h
  obtain ⟨⟨idr, hmaxr, hrmem⟩, hcharr⟩ := CFSG.BlockBasics.residue_prime_existence r hr
  have : idr.IsMaximal := hmaxr
  have : CharP (ComplexAlgebraicIntegers ⧸ idr) r := hcharr idr hmaxr hrmem
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hP3 : 3 ≤ Nat.card P := by
    rw [hPcard]
    exact hr3.trans (Nat.le_self_pow (by omega) r)
  have hPodd : Odd (Nat.card P) := by
    rw [hPcard]
    exact hrodd.pow
  obtain ⟨Ψ, δ', hΨne, hΨreal, hΨodd, hΨval, hδ'⟩ :=
    exists_constant_character_of_inertial_index_two basis idr r hr2 principal hprincipal P hcyc
      hrel hP3 hPodd
      (fun c c' hc hc' hcr hc'r hco hcc' => eq_of_degree_eq_of_three
        (fun c => Module.finrank ℂ (basis.representation c).vector) (by omega) hf₁ hf₂ hf₃
        (hreal c hcr hco hc).2 (hreal c' hc'r (hcc' ▸ hco) hc').2 hcc')
  obtain ⟨hΨB, hΨ⟩ := hreal Ψ hΨreal hΨodd hΨne
  obtain ⟨h10, h11⟩ := rotation_index_conditions (m := (Nat.card F + 1).factorization 2)
    (by omega) (v := 1) le_rfl (by norm_num)
  obtain ⟨h20, h21⟩ := rotation_index_conditions (m := (Nat.card F + 1).factorization 2)
    (by omega) (v := 2) (by norm_num) le_rfl
  have hΨ1 := character_rotation_eq_of_singular hn4 e' basis id2 principal hprincipal hΨB hr hr2
    hΨval huy hyord ha1 h10 h11
  have hΨ2 := character_rotation_eq_of_singular hn4 e' basis id2 principal hprincipal hΨB hr hr2
    hΨval huy hyord ha1 h20 h21
  rcases hΨ with h | h | h
  ·
    rw [h] at hΨval
    obtain ⟨⟨idp, hmaxp, hpmem⟩, hcharp⟩ := CFSG.BlockBasics.residue_prime_existence p hp
    have : idp.IsMaximal := hmaxp
    have : CharP (ComplexAlgebraicIntegers ⧸ idp) p := hcharp idp hmaxp hpmem
    have hvGp : (Nat.card G).factorization p = 3 * f := by
      have hcop := coprime_facts hZ
      rw [hpc] at hcop
      have hq1 : 1 < Nat.card F := by omega
      have hne : (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) ≠ 0 := by
        have h3' : 1 < Nat.card F ^ 3 := Nat.one_lt_pow (by norm_num) hq1
        have h2' : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) hq1
        exact Nat.mul_ne_zero (by omega) (by omega)
      have h1 : (Nat.card G * Nat.card Z).factorization p = (Nat.card G).factorization p := by
        rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop.1),
          add_zero]
      rw [← h1, hcard, mul_assoc, Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop.2.2),
        add_zero, hF, ← pow_mul, hp.factorization_pow, Finsupp.single_eq_same]
      ring
    have hdegp : p ^ (Nat.card G).factorization p ∣
        Module.finrank ℂ (basis.representation χ₁).vector := by
      rw [hvGp, hf₁, hF, ← pow_mul, mul_comm]
    obtain ⟨-, hvan⟩ :=
      full_prime_part_character_degree_singleton_block_singular_vanishing basis idp p χ₁ hdegp
    have h0 := hvan ((x : G) * Q) (by rw [hxQord]; exact dvd_mul_left p r)
    have hδ'0 := hΨval ((x : G) * Q) (by rw [hxQord]; exact dvd_mul_right r p)
    rw [h0] at hδ'0
    rcases hδ' with rfl | rfl <;> norm_num at hδ'0
  · rw [h] at hΨ1 hΨ2
    exact hχ₂ (hΨ1.trans hΨ2.symm)
  · rw [h] at hΨ1 hΨ2
    exact hχ₃ (hΨ1.trans hΨ2.symm)

end CFSG.BrauerLinearThree
