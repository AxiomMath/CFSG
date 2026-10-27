module

public import CFSG.CharacterTheory.BrauerLinearThree.QOneCentralizer
public import CFSG.CharacterTheory.BrauerLinearThree.QOneFourG

public section

namespace CFSG.BrauerLinearThree.QOne

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0)
  (hcard : Nat.card G * Nat.card Z =
    Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
  [Fintype G] (basis : FiniteIrreducibleCharacterBasis G) {χ₁ χ₄ : basis.index}
  (hχ₁ : (basis.representation χ₁).character 1 = (Nat.card F : ℂ) ^ 3)
  (hχ₄ : (basis.representation χ₄).character 1 = (Nat.card F : ℂ) ^ 3 - 1)
  (hrel : ∀ g : G, Odd (orderOf g) →
    -1 + (basis.representation χ₁).character g = (basis.representation χ₄).character g)

omit [Z.Normal] in
include hZ hcard hχ₁ hrel in
theorem character_four_eq_neg_one {g : G} (hgodd : Odd (orderOf g))
    (hg : ringChar F ∣ orderOf g) : (basis.representation χ₄).character g = -1 := by
  rw [← hrel g hgodd, character_eq_zero_of_ringChar_dvd hZ hcard basis hχ₁ hg, add_zero]

omit [Z.Normal] in
include h2 hZ hcard hχ₁ hrel in
theorem character_four_eq_neg_one_of_pow {Q : G} (hQ1 : Q ≠ 1) (hQp : Q ^ ringChar F = 1) :
    (basis.representation χ₄).character Q = -1 := by
  have hp₀ : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp₀⟩
  have hQord : orderOf Q = ringChar F := orderOf_eq_prime hQp hQ1
  exact character_four_eq_neg_one hZ hcard basis hχ₁ hrel
    (by rw [hQord]; exact hp₀.odd_of_ne_two (ringChar_ne_two h2)) (by rw [hQord])

include φ hZ h2 hcard hχ₁ hχ₄ hrel in
theorem exists_conj_mem_centerSub_of_character_ne_zero
    (hcA : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
      Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
        Nat.card F ^ 3 * (Nat.card F - 1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1) {g u v : G}
    (hg : g = u * v) (huv : Commute u v) (hu : ∃ k : ℕ, orderOf u = p ^ k)
    (hv : Nat.Coprime p (orderOf v)) (hne : (basis.representation χ₄).character g ≠ 0) :
    ∃ x : G, x * u * x⁻¹ ∈ centerSub φ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ hp).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) p :=
    (CFSG.BlockBasics.residue_prime_existence _ hp).2 ideal hmax hmem
  set q := Nat.card F with hqdef
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hq3 : 0 < q ^ 3 - 1 := by
    have : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
    omega
  have hpq0 : ¬ p ∣ q := by
    intro h
    have : p ∣ q - (q - 1) := Nat.dvd_sub h hpq
    rw [show q - (q - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hpq1 : ¬ p ∣ q + 1 := by
    intro h
    have : p ∣ q + 1 - (q - 1) := Nat.dvd_sub h hpq
    rw [show q + 1 - (q - 1) = 2 by omega] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  set Q₀ := rootUp φ 1 with hQ₀def
  have hQ₀1 : Q₀ ≠ 1 := rootUp_one_ne_one φ hZ
  have hQ₀p : Q₀ ^ ringChar F = 1 := rootUp_pow_ringChar φ 1
  have hQ₀4 := character_four_eq_neg_one_of_pow hZ h2 hcard basis hχ₁ hrel hQ₀1 hQ₀p
  set C₀ := Subgroup.centralizer ({Q₀} : Set G) with hC₀def
  have hca := hcA Q₀ hQ₀1 hQ₀p
  set U := centerSub φ with hUdef
  have hUC : U ≤ C₀ := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_mem_centerSub φ hx (linearCentralizerHom_commute φ _))
  have hUcard : Nat.card U * Nat.card Z = q - 1 := card_scalarImage φ hZ
  obtain ⟨PU⟩ : Nonempty (Sylow p U) := inferInstance
  set P : Subgroup G := (PU : Subgroup U).map U.subtype with hPdef
  have hPcard : Nat.card P = p ^ (Nat.card U).factorization p := by
    rw [hPdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective U),
      Sylow.card_eq_multiplicity]
  have hPU : P ≤ U := Subgroup.map_subtype_le _
  have hPC : P ≤ C₀ := hPU.trans hUC
  have hfac : (Nat.card C₀).factorization p = (Nat.card U).factorization p := by
    apply le_antisymm
    · have h1 : Nat.card C₀ ∣ q ^ 3 * Nat.card U := by
        have : Nat.card C₀ * Nat.card Z ∣ q ^ 3 * Nat.card U * Nat.card Z := by
          rw [mul_assoc, hUcard]
          exact hca
        exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos this
      have hcop : Nat.Coprime p (q ^ 3) :=
        Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq0)
      have h2' : p ^ (Nat.card C₀).factorization p ∣ Nat.card U :=
        (Nat.Coprime.pow_left _ hcop).dvd_of_dvd_mul_left ((Nat.ordProj_dvd _ _).trans h1)
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp h2'
    · have h1 : p ^ (Nat.card U).factorization p ∣ Nat.card C₀ := by
        rw [← hPcard]
        exact Subgroup.card_dvd_of_le hPC
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp h1
  have hPsyl : Nat.card (P.subgroupOf C₀) = p ^ (Nat.card C₀).factorization p := by
    rw [card_subgroupOf_of_le hPC, hPcard, hfac]
  have hclass : classDefect p (ConjClasses.mk Q₀) P := by
    refine ⟨Q₀, rfl, Sylow.ofCard (P.subgroupOf C₀) hPsyl, ?_⟩
    rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPC]
  obtain ⟨N, hN⟩ := cube_sub_one_dvd_index_centralizer basis hχ₄ hQ₀4
  rw [← hqdef] at hN
  have hNc : N * (Nat.card C₀ * Nat.card Z) = q ^ 3 * (q ^ 2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hq3
    calc (q ^ 3 - 1) * (N * (Nat.card C₀ * Nat.card Z)) =
          C₀.index * Nat.card C₀ * Nat.card Z := by rw [hN]; ring
      _ = Nat.card G * Nat.card Z := by rw [Subgroup.index_mul_card]
      _ = (q ^ 3 - 1) * (q ^ 3 * (q ^ 2 - 1)) := by rw [hcard]; ring
  have hpN : ¬ p ∣ N := by
    intro hpN
    have hv' : p ^ (q - 1).factorization p ∣ Nat.card C₀ * Nat.card Z := by
      have e : (q - 1).factorization p = (Nat.card C₀ * Nat.card Z).factorization p := by
        rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hfac,
          ← hUcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
      rw [e]
      exact Nat.ordProj_dvd _ _
    have h1 : p ^ ((q - 1).factorization p + 1) ∣ q ^ 3 * (q + 1) * (q - 1) := by
      have h' := Nat.mul_dvd_mul hpN hv'
      rw [hNc] at h'
      rw [pow_succ, mul_comm]
      convert h' using 1
      have h1' : 1 ≤ q := by omega
      have h2' : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1', h2']
      ring
    have hcop : Nat.Coprime p (q ^ 3 * (q + 1)) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq0))
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq1)
    exact Nat.pow_succ_factorization_not_dvd (by omega) hp
      ((Nat.Coprime.pow_left _ hcop).dvd_of_dvd_mul_left h1)
  have hval : (localCentralCharacterHom basis ideal χ₄
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk Q₀)) : ℂ) =
      (((-(N : ℤ)) : ℤ) : ℂ) := by
    have h : (localCentralCharacterHom basis ideal χ₄ (centralConjugacyClassSum
        (localizedComplexIntegerRing ideal) (ConjClasses.mk Q₀)) : ℂ) =
        (C₀.index : ℂ) * (basis.representation χ₄).character Q₀ /
          (basis.representation χ₄).character 1 :=
      CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis Q₀ χ₄
    rw [h, hQ₀4, hχ₄, hN]
    have hne' : (q : ℂ) ^ 3 - 1 ≠ 0 := by
      have : ((q ^ 3 - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq3.ne'
      push_cast [Nat.cast_sub h3] at this
      exact this
    push_cast [Nat.cast_sub h3]
    field_simp
  have heq : localCentralCharacterHom basis ideal χ₄
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk Q₀)) =
      (((-(N : ℤ)) : ℤ) : localizedComplexIntegerRing ideal) :=
    Subtype.ext (by rw [hval]; push_cast; rfl)
  have hunit : IsUnit (((-(N : ℤ)) : ℤ) : localizedComplexIntegerRing ideal) := by
    rw [localizedComplexInteger_integer_unit_iff ideal p]
    rw [dvd_neg]
    exact fun h => hpN (Int.natCast_dvd_natCast.mp h)
  have hres : centralCharacterResidueHom basis ideal χ₄
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk Q₀)) ≠ 0 := by
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ₄ _) ≠ 0
    rw [heq]
    exact (localizedComplexIntegerResidue_isUnit_iff ideal _).mp hunit
  obtain ⟨D, hD⟩ := coefficientBlockDefect_exists basis ideal p χ₄
  have hDP := hD.2 (ConjClasses.mk Q₀) P hclass hres
  have huD := (CFSG.Semidihedral.Principal.block_characters_vanish_outside_defect_primary basis
    ideal p χ₄ D hD g u v hg huv hu hv).2 ⟨χ₄, coefficientBlock_self_mem basis _ χ₄, hne⟩
  obtain ⟨x, hx⟩ := subgroupSubconjugate_trans huD hDP
  exact ⟨x, hPU (hx (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers u)))⟩

include φ hZ h2 hcard hχ₁ hχ₄ hrel in
theorem card_centralizer_dvd_cube_of_odd (hJ : orderOf J = 2)
    (h4G : ∀ z ∈ centerSub φ, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer ({J} : Set G))
    (hcA : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
      Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
        Nat.card F ^ 3 * (Nat.card F - 1))
    {Q : G} (hQ1 : Q ≠ 1) (hQp : Q ^ ringChar F = 1)
    (hodd : Odd (Nat.card (Subgroup.centralizer ({Q} : Set G)))) :
    Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card F ^ 3 := by
  set C := Subgroup.centralizer ({Q} : Set G) with hCdef
  have hp₀ : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp₀⟩
  have hp₀odd : Odd (ringChar F) := hp₀.odd_of_ne_two (ringChar_ne_two h2)
  have hQord : orderOf Q = ringChar F := orderOf_eq_prime hQp hQ1
  have hcq : Nat.card C ∣ Nat.card F ^ 3 * (Nat.card F - 1) :=
    (Dvd.intro _ rfl).trans (hcA Q hQ1 hQp)
  by_contra hndvd
  have hncop : ¬ Nat.Coprime (Nat.card C) (Nat.card F - 1) :=
    fun hcop => hndvd (hcop.dvd_of_dvd_mul_right hcq)
  obtain ⟨p, hp, hpC, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hncop
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpC)
  have : Fact p.Prime := ⟨hp⟩
  have hpp₀ : p ≠ ringChar F := by
    rintro rfl
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (coprime_ringChar_card_sub_one (F := F)) hpq
  have hcopp : Nat.Coprime p (ringChar F) := (Nat.coprime_primes hp hp₀).mpr hpp₀
  obtain ⟨P, hP⟩ := exists_prime_orderOf_dvd_card' p hpC
  have hPQ : Commute (P : G) Q := Subgroup.mem_centralizer_singleton_iff.mp P.2
  have hPord : orderOf (P : G) = p := by rw [Subgroup.orderOf_coe, hP]
  have hord : orderOf ((P : G) * Q) = p * ringChar F := by
    rw [hPQ.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hPord, hQord]; exact hcopp), hPord,
      hQord]
  have h4 : (basis.representation χ₄).character ((P : G) * Q) = -1 :=
    character_four_eq_neg_one hZ hcard basis hχ₁ hrel
      (by rw [hord]; exact (hp.odd_of_ne_two hp2).mul hp₀odd) (by rw [hord]; exact dvd_mul_left _ _)
  obtain ⟨x, hx⟩ := exists_conj_mem_centerSub_of_character_ne_zero φ hZ h2 hcard basis hχ₁ hχ₄
    hrel hcA hp hp2 hpq rfl hPQ ⟨1, by rw [pow_one, hPord]⟩ (by rw [hQord]; exact hcopp)
    (by rw [h4]; norm_num)
  have hx1 : x * (P : G) * x⁻¹ ≠ 1 := by
    intro h
    have hP1 : (P : G) = 1 := by
      calc (P : G) = x⁻¹ * (x * P * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    rw [hP1, orderOf_one] at hPord
    exact hp.one_lt.ne' hPord.symm
  have hxQ : x * Q * x⁻¹ ∈ Subgroup.centralizer ({x * (P : G) * x⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * Q * x⁻¹ * (x * P * x⁻¹) = x * (Q * P) * x⁻¹ := by group
      _ = x * (P * Q) * x⁻¹ := by rw [hPQ.eq]
      _ = x * P * x⁻¹ * (x * Q * x⁻¹) := by group
  rw [h4G _ hx hx1] at hxQ
  have hJmem : J ∈ Subgroup.centralizer ({x * Q * x⁻¹} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hxQ).symm
  have h2dvd : 2 ∣ Nat.card (Subgroup.centralizer ({x * Q * x⁻¹} : Set G)) := by
    have := orderOf_dvd_natCard (⟨J, hJmem⟩ : Subgroup.centralizer ({x * Q * x⁻¹} : Set G))
    rwa [Subgroup.orderOf_mk, hJ] at this
  rw [card_centralizer_conj] at h2dvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)

include φ hZ hZodd h2 hcard hχ₁ hχ₄ hrel in
theorem card_centralizer_conditions (hq : Nat.card F % 4 = 1) (hJ : orderOf J = 2)
    (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hL1 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card F + 1 → ∀ g : G, orderOf g ≠ p * ringChar F)
    (h4G : ∀ z ∈ centerSub φ, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer ({J} : Set G)) :
    ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
      Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
          Nat.card F ^ 3 * (Nat.card F - 1) ∧
        ((∀ g : G, g * Q * g⁻¹ ∉ rootX₁ φ) →
          Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card F ^ 3) := by
  have hcA : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
      Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
        Nat.card F ^ 3 * (Nat.card F - 1) := fun Q hQ1 hQp =>
    card_centralizer_mul_card_Z_dvd φ hZ hZodd h2 basis hχ₄ hq hcard hinv hJ hL1 hQ1 hQp
      (character_four_eq_neg_one_of_pow hZ h2 hcard basis hχ₁ hrel hQ1 hQp)
  intro Q hQ1 hQp
  refine ⟨hcA Q hQ1 hQp, fun hnot => ?_⟩
  have hodd : Odd (Nat.card (Subgroup.centralizer ({Q} : Set G))) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h
    obtain ⟨g, hg⟩ := (two_part_card_centralizer φ hZ hZodd h2 hinv hJ hQ1 hQp).2 h
    exact hnot g hg
  exact card_centralizer_dvd_cube_of_odd φ hZ h2 hcard basis hχ₁ hχ₄ hrel hJ h4G hcA hQ1 hQp hodd

end CFSG.BrauerLinearThree.QOne
