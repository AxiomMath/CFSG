module

public import CFSG.CharacterTheory.BrauerLinearThree.SixBChar
public import CFSG.CharacterTheory.BrauerLinearThree.FourGOrder
public import CFSG.CharacterTheory.BrauerLinearThree.SixBLocal

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Field F] [Finite F] in
theorem ringChar_eq_of_card [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ f) : ringChar F = p := by
  have hrc : (ringChar F).Prime := CharP.char_is_prime F _
  obtain ⟨f', hf', hq'⟩ := exists_card_eq_ringChar_pow F
  have hdvd : ringChar F ∣ p ^ f := by
    rw [← hF, hq']
    exact dvd_pow_self _ hf'.ne'
  exact (Nat.prime_dvd_prime_iff_eq hrc hp).mp (hrc.dvd_of_dvd_pow hdvd)

include φ hZ hZodd h2 hJ in
theorem exists_six_B_character
    [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    (basis : FiniteIrreducibleCharacterBasis G) :
    ∃ ν₀ : basis.index, Module.finrank ℂ (basis.representation ν₀).vector = Nat.card F ^ 3 - 1 ∧
      ∀ x : G, Odd (orderOf x) → p ∣ orderOf x → (basis.representation ν₀).character x = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨χ₁, ν₀, hχ₁, hν₀, hrel⟩ :=
    exists_principal_characters φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hcard basis
  obtain ⟨⟨ideal, hmax, hpmem⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence p hp
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) p := hchar ideal hmax hpmem
  have hvG : (Nat.card G).factorization p = 3 * f := by
    have hcop := coprime_facts hZ
    rw [ringChar_eq_of_card hp hF] at hcop
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
  have hdeg : p ^ (Nat.card G).factorization p ∣
      Module.finrank ℂ (basis.representation χ₁).vector := by
    rw [hvG, hχ₁, hF, ← pow_mul, mul_comm]
  obtain ⟨-, hvan⟩ :=
    CFSG.Semidihedral.Principal.full_prime_part_character_degree_singleton_block_singular_vanishing
      basis ideal p χ₁ hdeg
  refine ⟨ν₀, hν₀, fun x hx hpx => ?_⟩
  rw [hrel x hx, hvan x hpx, zero_sub]

include φ hZ hZodd h2 hJ in
theorem card_centralizer_mul_card_Z_dvd
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    {Q : G} (hQ1 : Q ≠ 1) (hQp : Q ^ ringChar F = 1) :
    Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
      Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) := by
  let : Fintype G := Fintype.ofFinite G
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨basis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨ν₀, hν₀, hval⟩ :=
    exists_six_B_character φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hcard basis
  rw [ringChar_eq_of_card hp hF] at hQp
  have hord : orderOf Q = p := orderOf_eq_prime hQp hQ1
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have hqodd := odd_card_F h2
      rw [hF, h] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
    · exact h
  have hQν := hval Q (by rw [hord]; exact hpodd) (by rw [hord])
  have hdvd := card_centralizer_mul_dvd_of_character_eq_neg_one basis ν₀ Q hQν
  rw [hν₀] at hdvd
  have hq3 : 0 < Nat.card F ^ 3 - 1 := by
    have : 1 < Nat.card F ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h1 : Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z * (Nat.card F ^ 3 - 1) ∣
      Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
    calc Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z * (Nat.card F ^ 3 - 1) =
        Nat.card (Subgroup.centralizer ({Q} : Set G)) * (Nat.card F ^ 3 - 1) * Nat.card Z := by
          ring
      _ ∣ Nat.card G * Nat.card Z := Nat.mul_dvd_mul_right hdvd _
      _ = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by rw [hcard]; ring
  exact Nat.dvd_of_mul_dvd_mul_right hq3 h1

omit [Field F] [Finite F] in
theorem mul_dvd_of_coprime_conditions {c l q : ℕ} (hq : q % 4 = 3)
    (h : c * l ∣ q ^ 3 * (q - 1) * (q + 1)) (hl : l ∣ q - 1) (hlodd : Odd l) (h4 : ¬ 4 ∣ c)
    (hodd : ∀ r : ℕ, r.Prime → r ∣ q + 1 → Odd r → ¬ r ∣ c) (hc : 0 < c) :
    c * l ∣ q ^ 3 * (q - 1) := by
  have hq0 : 0 < q := by omega
  have hl0 : 0 < l := hlodd.pos
  have hX : 0 < q ^ 3 * (q - 1) := Nat.mul_pos (by positivity) (by omega)
  rw [← Nat.factorization_le_iff_dvd (by positivity) hX.ne']
  have hle := (Nat.factorization_le_iff_dvd (by positivity) (by positivity)).mpr h
  intro r
  by_cases hr : r.Prime
  · have hr' := hle r
    rw [Nat.factorization_mul hX.ne' (by omega), Finsupp.add_apply] at hr'
    by_cases hr2 : r = 2
    · subst hr2
      have hcl : (c * l).factorization 2 ≤ 1 := by
        rw [Nat.factorization_mul hc.ne' hl0.ne', Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hlodd)
            (even_iff_two_dvd.mpr h2)), add_zero]
        by_contra hcon
        push Not at hcon
        apply h4
        have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hc.ne').mpr
          (show 2 ≤ c.factorization 2 by omega)
        simpa using this
      have hX2 : 1 ≤ (q ^ 3 * (q - 1)).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX.ne').mp
          (by rw [pow_one]; exact Dvd.dvd.mul_left (by omega) _)
      omega
    · by_cases hrq : r ∣ q + 1
      ·
        have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
        have hrc : ¬ r ∣ c := hodd r hr hrq hrodd
        have hrl : ¬ r ∣ l := by
          intro hrl
          have h1 : r ∣ q - 1 := hrl.trans hl
          have h2' : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub hrq h1
          rw [show q + 1 - (q - 1) = 2 by omega] at h2'
          exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2')
        have : (c * l).factorization r = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun h => (hr.dvd_mul.mp h).elim hrc hrl)
        omega
      · rw [Nat.factorization_eq_zero_of_not_dvd hrq, add_zero] at hr'
        exact hr'
  · simp [Nat.factorization_eq_zero_of_not_prime _ hr]

include φ hZ hZodd h2 hJ in
theorem card_centralizer_mul_card_Z_dvd_of_six_A
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    (h6A : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 → ∀ r : ℕ, r.Prime → r ∣ Nat.card F + 1 →
      Odd r → ¬ r ∣ Nat.card (Subgroup.centralizer ({Q} : Set G)))
    {Q : G} (hQ1 : Q ≠ 1) (hQp : Q ^ ringChar F = 1) :
    Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
      Nat.card F ^ 3 * (Nat.card F - 1) := by
  have ha := card_centralizer_mul_card_Z_dvd φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hcard
    hQ1 hQp
  have e : Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) =
      Nat.card F ^ 3 * (Nat.card F - 1) * (Nat.card F + 1) := by
    have hq1 : 1 ≤ Nat.card F := by omega
    have : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      zify [hq1, Nat.one_le_pow 2 _ hq1]
      ring
    rw [this]
    ring
  rw [e] at ha
  exact mul_dvd_of_coprime_conditions hq ha (card_Z_dvd hZ) hZodd
    (not_four_dvd_card_centralizer φ hZ hZodd h2 hJ hnonab hq hQ1 hQp)
    (fun r hr hrq hrodd => h6A Q hQ1 hQp r hr hrq hrodd) Nat.card_pos

include φ hZ hZodd h2 hJ in
theorem false_of_prime_dvd_odd_card_centralizer
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    (h6A : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 → ∀ r : ℕ, r.Prime → r ∣ Nat.card F + 1 →
      Odd r → ¬ r ∣ Nat.card (Subgroup.centralizer ({Q} : Set G)))
    {Q : G} (hQ1 : Q ≠ 1) (hQp : Q ^ ringChar F = 1)
    (hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({Q} : Set G)))
    {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (hrq : ¬ r ∣ Nat.card F + 1)
    (hrc : r ∣ Nat.card (Subgroup.centralizer ({Q} : Set G))) : False := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have hpc := ringChar_eq_of_card hp hF
  have hq1 : 1 < Nat.card F := by omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hodd hrc
  obtain ⟨basis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨ν₀, hν₀, hval⟩ :=
    exists_six_B_character φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hcard basis
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have hqodd := odd_card_F h2
      rw [hF, h] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
    · exact h
  obtain ⟨P, hP⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({Q} : Set G)) r hrc
  have hPr : orderOf (P : G) = r := by rw [Subgroup.orderOf_coe, hP]
  have hPQ : Commute (P : G) Q := Subgroup.mem_centralizer_singleton_iff.mp P.2
  have hQord : orderOf Q = p := by
    rw [hpc] at hQp
    exact orderOf_eq_prime hQp hQ1
  have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).mpr hrp
  have hPQord : orderOf ((P : G) * Q) = r * p := by
    rw [hPQ.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hPr, hQord]; exact hcop), hPr, hQord]
  have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have hνPQ : (basis.representation ν₀).character ((P : G) * Q) = -1 :=
    hval _ (by rw [hPQord]; exact hrodd.mul hpodd) (by rw [hPQord]; exact dvd_mul_left p r)
  obtain ⟨⟨ideal, hmax, hrmem⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence r hr
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) r := hchar ideal hmax hrmem
  obtain ⟨D, hD⟩ := coefficientBlockDefect_exists basis ideal r ν₀
  set Q₀ := rootUp φ 1 with hQ₀
  have hQ₀1 : Q₀ ≠ 1 := rootUp_one_ne_one φ hZ
  have hQ₀p : Q₀ ^ ringChar F = 1 := rootUp_pow_ringChar φ 1
  have hQ₀ord : orderOf Q₀ = p := by
    rw [hpc] at hQ₀p
    exact orderOf_eq_prime hQ₀p hQ₀1
  have hνQ₀ : (basis.representation ν₀).character Q₀ = -1 :=
    hval Q₀ (by rw [hQ₀ord]; exact hpodd) (by rw [hQ₀ord])
  have hZC : centerSub φ ≤ Subgroup.centralizer ({Q₀} : Set G) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_mem_centerSub φ hx (linearCentralizerHom_commute φ (upperGL 1)))
  have hcZ : Nat.card (centerSub φ) * Nat.card Z = Nat.card F - 1 := card_scalarImage φ hZ
  obtain ⟨R⟩ : Nonempty (Sylow r (centerSub φ)) := inferInstance
  set P₀ : Subgroup G := (R : Subgroup (centerSub φ)).map (centerSub φ).subtype with hP₀
  have hP₀Z : P₀ ≤ centerSub φ := Subgroup.map_subtype_le _
  have hP₀C : P₀ ≤ Subgroup.centralizer ({Q₀} : Set G) := hP₀Z.trans hZC
  have hcardP₀ : Nat.card P₀ = r ^ (Nat.card (centerSub φ)).factorization r := by
    rw [hP₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Sylow.card_eq_multiplicity]
  have hcQ₀ := card_centralizer_mul_card_Z_dvd_of_six_A φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF
    hcard h6A hQ₀1 hQ₀p
  have hvQ₀ : (Nat.card (Subgroup.centralizer ({Q₀} : Set G))).factorization r =
      (Nat.card (centerSub φ)).factorization r := by
    apply le_antisymm
    ·
      have h1 : Nat.card (Subgroup.centralizer ({Q₀} : Set G)) ∣
          Nat.card F ^ 3 * Nat.card (centerSub φ) := by
        rw [← hcZ, ← mul_assoc] at hcQ₀
        exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hcQ₀
      have hq3ne : Nat.card F ^ 3 ≠ 0 := (pow_pos Nat.card_pos 3).ne'
      have h2' := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (Nat.mul_ne_zero hq3ne Nat.card_pos.ne')).mpr h1 r
      rwa [Nat.factorization_mul hq3ne Nat.card_pos.ne', Finsupp.add_apply, hF,
        ← pow_mul, hp.factorization_pow, Finsupp.single_eq_of_ne hrp, zero_add] at h2'
    · have h1 := Subgroup.card_dvd_of_le hP₀C
      rw [hcardP₀] at h1
      exact (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
  have hsyl : Nat.card (P₀.subgroupOf (Subgroup.centralizer ({Q₀} : Set G))) =
      r ^ (Nat.card (Subgroup.centralizer ({Q₀} : Set G))).factorization r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀C).toEquiv, hcardP₀, hvQ₀]
  set Syl := Sylow.ofCard _ hsyl
  have hclass : classDefect r (ConjClasses.mk Q₀) P₀ := by
    refine ⟨Q₀, rfl, Syl, ?_⟩
    change P₀ = (P₀.subgroupOf (Subgroup.centralizer ({Q₀} : Set G))).map
      (Subgroup.centralizer ({Q₀} : Set G)).subtype
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hP₀C]
  have hdvdQ₀ := card_centralizer_mul_dvd_of_character_eq_neg_one basis ν₀ Q₀ hνQ₀
  rw [hν₀] at hdvdQ₀
  set c₀ := Nat.card (Subgroup.centralizer ({Q₀} : Set G))
  set m := (Subgroup.centralizer ({Q₀} : Set G)).index with hm
  have hindex : m * c₀ = Nat.card G := Subgroup.index_mul_card _
  obtain ⟨m', hm'⟩ : (Nat.card F ^ 3 - 1) ∣ m := by
    have h := hdvdQ₀
    rw [← hindex, mul_comm m] at h
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h
  have hq3 : 0 < Nat.card F ^ 3 - 1 := by
    have : 1 < Nat.card F ^ 3 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have hm'eq : m' * c₀ * Nat.card Z = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hq3
    calc (Nat.card F ^ 3 - 1) * (m' * c₀ * Nat.card Z) = m * c₀ * Nat.card Z := by
          rw [hm']; ring
      _ = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by rw [hindex, hcard]
      _ = (Nat.card F ^ 3 - 1) * (Nat.card F ^ 3 * (Nat.card F ^ 2 - 1)) := by ring
  have hm'r : ¬ r ∣ m' := by
    intro hdvd
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_mul] at hm'eq
      have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) hq1
      have : 0 < Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
      omega
    have hv := congrArg (fun n => n.factorization r) hm'eq
    have hq21 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      zify [hq1.le, Nat.one_le_pow 2 _ hq1.le]
      ring
    have hq3ne : Nat.card F ^ 3 ≠ 0 := (pow_pos Nat.card_pos 3).ne'
    have e1 : (m' * c₀ * Nat.card Z).factorization r = m'.factorization r +
        c₀.factorization r + (Nat.card Z).factorization r := by
      rw [Nat.factorization_mul (Nat.mul_ne_zero hm'0 Nat.card_pos.ne') Nat.card_pos.ne',
        Nat.factorization_mul hm'0 Nat.card_pos.ne', Finsupp.add_apply, Finsupp.add_apply]
    have e2 : (Nat.card F ^ 3 * (Nat.card F ^ 2 - 1)).factorization r =
        (Nat.card (centerSub φ)).factorization r + (Nat.card Z).factorization r := by
      rw [hq21, Nat.factorization_mul hq3ne (Nat.mul_ne_zero (by omega) (by omega)),
        Finsupp.add_apply, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hrq, add_zero, ← hcZ,
        Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hF,
        ← pow_mul, hp.factorization_pow, Finsupp.single_eq_of_ne hrp, zero_add]
    simp only [e1, e2, hvQ₀] at hv
    have h1 : 1 ≤ m'.factorization r := (hr.dvd_iff_one_le_factorization hm'0).mp hdvd
    omega
  have hres : centralCharacterResidueHom basis ideal ν₀
      (centralConjugacyClassSum _ (ConjClasses.mk Q₀)) ≠ 0 := by
    have hscalar : (localCentralCharacterHom basis ideal ν₀
        (centralConjugacyClassSum _ (ConjClasses.mk Q₀)) : ℂ) = ((-(m' : ℤ) : ℤ) : ℂ) := by
      rw [localCentralCharacterHom_coe]
      change centralCharacterScalar basis (conjugacyClassSum (ConjClasses.mk Q₀)) ν₀ = _
      rw [CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk, hνQ₀,
        show (basis.representation ν₀).character 1 = (Module.finrank ℂ
          (basis.representation ν₀).vector : ℂ) from Representation.char_one _, hν₀]
      change (m : ℂ) * -1 / ((Nat.card F ^ 3 - 1 : ℕ) : ℂ) = _
      have hq3' : ((Nat.card F ^ 3 - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq3.ne'
      rw [hm']
      push_cast
      field_simp
    have helt : localCentralCharacterHom basis ideal ν₀
        (centralConjugacyClassSum _ (ConjClasses.mk Q₀)) =
          ((-(m' : ℤ) : ℤ) : localizedComplexIntegerRing ideal) := by
      apply Subtype.ext
      rw [hscalar]
      push_cast
      rfl
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal ν₀
      (centralConjugacyClassSum _ (ConjClasses.mk Q₀))) ≠ 0
    rw [helt, map_intCast]
    intro h0
    rw [CharP.intCast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) r, Int.dvd_neg] at h0
    exact hm'r (by exact_mod_cast h0)
  have hDP₀ := hD.2 (ConjClasses.mk Q₀) P₀ hclass hres
  obtain ⟨-, hsub⟩ :=
    CFSG.Semidihedral.Principal.block_characters_vanish_outside_defect_primary basis ideal r ν₀ D
      hD ((P : G) * Q) P Q rfl hPQ ⟨1, by rw [hPr, pow_one]⟩ (by rw [hQord]; exact hcop)
  have hPD := hsub ⟨ν₀, coefficientBlock_self_mem basis _ ν₀, by rw [hνPQ]; norm_num⟩
  obtain ⟨g, hg⟩ := subgroupSubconjugate_trans hPD hDP₀
  have hgP : g * (P : G) * g⁻¹ ∈ centerSub φ :=
    hP₀Z (hg ⟨P, Subgroup.mem_zpowers _, rfl⟩)
  have hgP1 : g * (P : G) * g⁻¹ ≠ 1 := by
    intro h
    have : (P : G) = 1 := by
      calc (P : G) = g⁻¹ * (g * P * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hPr
    exact hr.one_lt.ne' hPr.symm
  have h4G := centralizer_le_of_mem_centerSub φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hgP hgP1
  have hgQ : g * Q * g⁻¹ ∈ Subgroup.centralizer ({g * (P : G) * g⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * Q * g⁻¹ * (g * ↑P * g⁻¹) = g * (Q * ↑P) * g⁻¹ := by group
      _ = g * (↑P * Q) * g⁻¹ := by rw [hPQ.eq]
      _ = g * ↑P * g⁻¹ * (g * Q * g⁻¹) := by group
  have hgQJ := Subgroup.mem_centralizer_singleton_iff.mp (h4G hgQ)
  apply hodd
  have hJQ : g⁻¹ * J * g ∈ Subgroup.centralizer ({Q} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * J * g * Q = g⁻¹ * (J * (g * Q * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * Q * g⁻¹) * J) * g := by rw [hgQJ]
      _ = Q * (g⁻¹ * J * g) := by group
  have hord : orderOf (⟨g⁻¹ * J * g, hJQ⟩ : Subgroup.centralizer ({Q} : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    have h : orderOf (g⁻¹ * J * g) = orderOf J := by
      simpa using orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective J
    rw [h, hJ]
  rw [← hord]
  exact orderOf_dvd_natCard _

include φ hZ hZodd h2 hJ in
theorem card_centralizer_of_six_A
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    (h6A : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 → ∀ r : ℕ, r.Prime → r ∣ Nat.card F + 1 →
      Odd r → ¬ r ∣ Nat.card (Subgroup.centralizer ({Q} : Set G))) :
    ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
      Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
          Nat.card F ^ 3 * (Nat.card F - 1) ∧
        ((∀ g : G, g * Q * g⁻¹ ∉ rootX₁ φ) →
          Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card F ^ 3) := by
  intro Q hQ1 hQp
  have hfirst := card_centralizer_mul_card_Z_dvd_of_six_A φ hZ hZodd h2 hJ hnonab hq hq7 p f hp
    hf hF hcard h6A hQ1 hQp
  refine ⟨hfirst, fun hnot => ?_⟩
  have hpc := ringChar_eq_of_card hp hF
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({Q} : Set G)) := by
    intro hev
    obtain ⟨g, hg⟩ := exists_conj_mem_rootX₁_of_even φ hZ hZodd h2 hJ hnonab hQp hev
    exact hnot g hg
  have hpow : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.centralizer ({Q} : Set G)) → r = p := by
    intro r hr hrc
    by_contra hrp
    have hr2 : r ≠ 2 := fun h => hodd (h ▸ hrc)
    have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
    have hrq : ¬ r ∣ Nat.card F + 1 := fun h => h6A Q hQ1 hQp r hr h hrodd hrc
    exact false_of_prime_dvd_odd_card_centralizer φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF
      hcard h6A hQ1 hQp hodd hr hrp hrq hrc
  have hcop : Nat.Coprime (Nat.card (Subgroup.centralizer ({Q} : Set G))) (Nat.card F - 1) := by
    apply Nat.Coprime.symm
    apply Nat.coprime_of_dvd
    intro r hr hr1 hr2
    have := hpow r hr hr2
    subst this
    have h := coprime_ringChar_card_sub_one F
    rw [hpc] at h
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp h hr1
  have h1 : Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card F ^ 3 * (Nat.card F - 1) :=
    (Nat.dvd_mul_right _ _).trans hfirst
  exact hcop.dvd_of_dvd_mul_right h1

end CFSG.BrauerLinearThree
