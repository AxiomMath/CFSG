module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.Restriction
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NoninvertingSection

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G]

section Inversion

@[expose] def dihedralSubgroup (t y : G) (hy : y * y = 1) (hyt : y * t * y⁻¹ = t⁻¹) :
    Subgroup G where
  carrier := {g | ∃ i : ℤ, g = t ^ i ∨ g = t ^ i * y}
  one_mem' := ⟨0, Or.inl (by simp)⟩
  mul_mem' := by
    have hconj : ∀ j : ℤ, y * t ^ j * y⁻¹ = t ^ (-j) := by
      intro j
      rw [← conj_zpow, hyt, inv_zpow']
    rintro a b ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
    · exact ⟨i + j, Or.inl (by rw [zpow_add])⟩
    · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · refine ⟨i - j, Or.inr ?_⟩
      calc t ^ i * y * t ^ j = t ^ i * (y * t ^ j * y⁻¹) * y := by group
        _ = t ^ (i - j) * y := by rw [hconj, ← zpow_add]; ring_nf
    · refine ⟨i - j, Or.inl ?_⟩
      calc t ^ i * y * (t ^ j * y) = t ^ i * (y * t ^ j * y⁻¹) * (y * y) := by group
        _ = t ^ (i - j) := by rw [hconj, hy, mul_one, ← zpow_add]; ring_nf
  inv_mem' := by
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy
    have hconj : ∀ j : ℤ, y * t ^ j * y⁻¹ = t ^ (-j) := by
      intro j
      rw [← conj_zpow, hyt, inv_zpow']
    rintro a ⟨i, rfl | rfl⟩
    · exact ⟨-i, Or.inl (by rw [zpow_neg])⟩
    · refine ⟨i, Or.inr ?_⟩
      calc (t ^ i * y)⁻¹ = y⁻¹ * t ^ (-i) := by rw [mul_inv_rev, zpow_neg]
        _ = y * t ^ (-i) := by rw [hyinv]
        _ = y * t ^ (-i) * y⁻¹ * y := by group
        _ = t ^ i * y := by rw [hconj, neg_neg]

theorem not_inverts_of_orderOf_eq_four {T : Type} [Group T] [Finite G]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) {t : G}
    (ht : orderOf t = 4) (y : G) (hy : y * y = 1) : y * t * y⁻¹ ≠ t⁻¹ := by
  intro hyt
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  set M := dihedralSubgroup t y hy hyt
  have htM : t ∈ M := ⟨1, Or.inl (by simp)⟩
  have hyM : y ∈ M := ⟨0, Or.inr (by simp)⟩
  have ht4 : t ^ 4 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hMp : IsPGroup 2 M := by
    rintro ⟨g, i, hg | hg⟩
    · refine ⟨2, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one, hg]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      norm_num [ht4]
    · refine ⟨2, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one, hg]
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy
      have hsq : (t ^ i * y) ^ 2 = 1 := by
        have h1 : y * t ^ i * y⁻¹ = t ^ (-i) := by
          rw [← conj_zpow, hyt, inv_zpow']
        calc (t ^ i * y) ^ 2 = t ^ i * (y * t ^ i * y⁻¹) * (y * y) := by
              rw [pow_two]; group
          _ = 1 := by rw [h1, hy, mul_one, ← zpow_add, add_neg_cancel, zpow_zero]
      rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, hsq, one_pow]
  obtain ⟨P, hP⟩ := hMp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hmem : ∀ x ∈ M, g⁻¹ * x * g ∈ (S : Subgroup G) := by
    intro x hx
    have hxP : x ∈ (P : Subgroup G) := hP hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hxP
  set y' : (S : Subgroup G) := ⟨g⁻¹ * y * g, hmem y hyM⟩
  set t' : (S : Subgroup G) := ⟨g⁻¹ * t * g, hmem t htM⟩
  have hy'2 : y' ^ 2 = 1 := by
    apply Subtype.ext
    simp only [y', Subgroup.coe_pow, Subgroup.coe_one]
    calc (g⁻¹ * y * g) ^ 2 = g⁻¹ * (y * y) * g := by rw [pow_two]; group
      _ = 1 := by rw [hy]; group
  have hy'Z := (hshape.sq_eq_one_iff y').mp hy'2
  have hcomm : t' * y' = y' * t' := (Subgroup.mem_center_iff.mp hy'Z t')
  have hcommG : t * y = y * t := by
    have h := congrArg Subtype.val hcomm
    simp only [t', y', Subgroup.coe_mul] at h
    have h' : g * (g⁻¹ * t * g * (g⁻¹ * y * g)) * g⁻¹ = g * (g⁻¹ * y * g * (g⁻¹ * t * g)) * g⁻¹ :=
      by rw [h]
    simpa [mul_assoc] using h'
  have htt : t = t⁻¹ := by
    rw [← hyt]
    calc t = y * t * y⁻¹ * (y * y) := by
          rw [hy, mul_one, ← hcommG]
          group
      _ = y * t * y⁻¹ := by rw [hy, mul_one]
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [htt]
    exact mul_inv_cancel t
  have hdvd := orderOf_dvd_of_pow_eq_one ht2
  rw [ht] at hdvd
  norm_num at hdvd

end Inversion

section Column

theorem lyons_order_four_principal_column [Fintype G] {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {t : G} (htS : t ∈ (S : Subgroup G)) (ht : orderOf t = 4) :
    (∃ s ∈ (S : Subgroup G), s * t * s⁻¹ = t⁻¹) ∧
    (∀ y : G, y * y = 1 → y * t * y⁻¹ ≠ t⁻¹) ∧
    (∀ label, ∃ n : ℤ, (basis.representation label).character t = n) ∧
    (∀ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ r ∈ Subgroup.centralizer ({t} : Set G), Odd (orderOf r) →
        (basis.representation label).character (t * r) =
          (basis.representation label).character t) ∧
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation label).character t ^ 2 = 16 ∧
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation label).character 1 * (basis.representation label).character t = 0 ∧
    ∀ z : G, z * z = 1 →
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character z * (basis.representation label).character t = 0 ∧
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character z ^ 2 * (basis.representation label).character t /
          (basis.representation label).character 1 = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have ht4 : orderOf t ∣ 2 ^ 2 := by rw [ht]; norm_num
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  have hconjS : ∃ s ∈ (S : Subgroup G), s * t * s⁻¹ = t⁻¹ := by
    set t' : (S : Subgroup G) := ⟨t, htS⟩
    have hnot : t' ∉ Subgroup.center (S : Subgroup G) := by
      intro hZ
      have h2 := congrArg Subtype.val ((hshape.sq_eq_one_iff t').mpr hZ)
      rw [Subgroup.coe_pow] at h2
      have hdvd := orderOf_dvd_of_pow_eq_one h2
      rw [ht] at hdvd
      norm_num at hdvd
    have hconj : IsConj t' t'⁻¹ := (hshape.isConj_iff_mul_center t' hnot t'⁻¹).mpr
      ⟨(t' ^ 2)⁻¹, Subgroup.inv_mem _ (hshape.sq_mem_center t'), by group⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    exact ⟨c, c.property, congrArg Subtype.val hc⟩
  have hnoinv := not_inverts_of_orderOf_eq_four hT S U hSU ht
  have hint : ∀ label, ∃ n : ℤ, (basis.representation label).character t = n :=
    fun label => sylow_character_integer hT S U hSU (basis.representation label).representation
      htS
  obtain ⟨-, -, -, hKnormal, hKodd, hKidx, -⟩ :=
    unitary_four_order_four_centralizer_odd_complement hT S U hSU htS ht
  have hcomp : ∃ (K : Subgroup (Subgroup.centralizer ({t} : Set G))) (_ : K.Normal),
      Nat.Coprime 2 (Nat.card K) ∧ IsPGroup 2 (Subgroup.centralizer ({t} : Set G) ⧸ K) ∧
      Nat.card (Subgroup.centralizer ({t} : Set G) ⧸ K) = 16 :=
    ⟨CFSG.oddCore _, hKnormal, Nat.coprime_two_left.mpr hKodd,
      IsPGroup.of_card (n := 4) (by rw [← Subgroup.index_eq_card, hKidx]; norm_num),
      by rw [← Subgroup.index_eq_card, hKidx]⟩
  have hcomp' := hcomp
  rw [centralizer_singleton_eq_zpowers] at hcomp
  obtain ⟨K, hKn, hKcop, hKp, hKcard⟩ := hcomp
  rw [centralizer_singleton_eq_zpowers, ← centralizer_zpowers_inv] at hcomp'
  obtain ⟨K', hK'n, hK'cop, hK'p, -⟩ := hcomp'
  have hconst : ∀ label ∈ B, ∀ r ∈ Subgroup.centralizer ({t} : Set G), Odd (orderOf r) →
      (basis.representation label).character (t * r) =
        (basis.representation label).character t := by
    intro label hlabel r hr hrodd
    have hrcop : Nat.Coprime 2 (orderOf r) := Nat.coprime_two_left.mpr hrodd
    have htr : Commute t r := (Subgroup.mem_centralizer_singleton_iff.mp hr).symm
    have hrC : r⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers t⁻¹ : Set G) :=
      mem_centralizer_zpowers_of_commute htr.inv_inv
    have h := principal_character_section_inv_eq basis ideal 2 principal hprincipal t⁻¹ 2
      (by rwa [orderOf_inv]) K' hK'cop hK'p label hlabel ⟨r⁻¹, hrC⟩
      (by rw [Subgroup.orderOf_mk, orderOf_inv]; exact hrcop)
    have heq : ((centralizerSelf t⁻¹ * ⟨r⁻¹, hrC⟩ : _) : G)⁻¹ = t * r := by
      change (t⁻¹ * r⁻¹)⁻¹ = t * r
      rw [mul_inv_rev, inv_inv, inv_inv, htr.eq]
    rw [heq, inv_inv] at h
    exact h
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers t : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨h1, h2, -⟩ := principal_primary_column_centralizer_norm_of_normal_complement basis
    ideal 2 principal hprincipal t 2 ht4 localBasis localPrincipal hlocalPrincipal K hKcop hKp
  have hnorm : ∑ label ∈ B, (basis.representation label).character t ^ 2 = 16 := by
    have h := h1.trans h2
    rw [hKcard] at h
    calc ∑ label ∈ B, (basis.representation label).character t ^ 2 =
        ∑ label ∈ B, (basis.representation label).character t *
          starRingEnd ℂ ((basis.representation label).character t) := by
          apply Finset.sum_congr rfl
          intro label _
          obtain ⟨n, hn⟩ := hint label
          rw [hn, map_intCast, pow_two]
      _ = 16 := by rw [h]; norm_num
  have horth : ∀ y : G, ¬ IsConj t y → ∀ ey : ℕ, orderOf y ∣ 2 ^ ey →
      ∑ label ∈ B, (basis.representation label).character t *
        (basis.representation label).character y⁻¹ = 0 := by
    intro y hty ey hy
    have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal t y 1 1 2 ey
      ht4 hy (by simp) (by simp) (Commute.one_right t) (Commute.one_right y) hty
    simpa only [mul_one] using h
  have hdeg : ∑ label ∈ B, (basis.representation label).character 1 *
      (basis.representation label).character t = 0 := by
    have h := horth 1 (fun h => ht1 (isConj_one_left.mp h)) 0 (by simp)
    rw [← h]
    apply Finset.sum_congr rfl
    intro label _
    rw [inv_one, mul_comm]
  refine ⟨hconjS, hnoinv, hint, hconst, hnorm, hdeg, fun z hz => ⟨?_, ?_⟩⟩
  · have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz
    have hz2 : orderOf z ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two, hz])
    have hnot : ¬ IsConj t z := by
      intro h
      obtain ⟨c, hc⟩ := isConj_iff.mp h
      have hord : orderOf z = orderOf t := by
        rw [← hc]
        exact (MulAut.conj c).orderOf_eq t
      rw [hord, ht] at hz2
      norm_num at hz2
    have h := horth z hnot 1 hz2
    rw [← h]
    apply Finset.sum_congr rfl
    intro label _
    rw [hzinv, mul_comm]
  · have hnoinv' : ∀ s : G, IsConj z s → s * t * s⁻¹ ≠ t⁻¹ := by
      intro s hs
      obtain ⟨c, rfl⟩ := isConj_iff.mp hs
      apply hnoinv
      calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [hz]; group
    have h := (brauer_noninverting_block_section_vanishing basis ideal 2 principal z z t hz hz 2
      ht4 hnoinv').1 1 (Subgroup.one_mem _) (by simp)
    rw [← h]
    apply Finset.sum_congr rfl
    intro label _
    rw [mul_one, pow_two]

end Column

end CFSG.LyonsUnitaryFour
