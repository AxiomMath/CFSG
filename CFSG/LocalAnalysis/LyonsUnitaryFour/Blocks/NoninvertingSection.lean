module

public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ProductCharacterFormula

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem inverts_zpow {G : Type*} [Group G] {t y : G} (h : t * y * t⁻¹ = y⁻¹) (m : ℤ) :
    t * y ^ m * t⁻¹ = (y ^ m)⁻¹ := by
  rw [← conj_zpow, h, inv_zpow]

theorem primary_part_product_not_conj {G : Type*} [Group G] {a b u : G} (ha : a * a = 1)
    (hb : b * b = 1) (hnoinv : ∀ t : G, IsConj a t → t * u * t⁻¹ ≠ u⁻¹) {a' b' : G}
    (ha' : IsConj a a') (hb' : IsConj b b') (primary : G)
    (hprimary : primary ∈ Subgroup.zpowers (a' * b')) : ¬ IsConj primary u⁻¹ := by
  intro hconj
  have hsq : ∀ c d : G, c * c = 1 → IsConj c d → d * d = 1 := by
    intro c d hc hcd
    obtain ⟨g, rfl⟩ := isConj_iff.mp hcd
    calc g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ := by group
      _ = 1 := by rw [hc]; group
  have ha'2 := hsq a a' ha ha'
  have hb'2 := hsq b b' hb hb'
  have ha'inv : a'⁻¹ = a' := inv_eq_of_mul_eq_one_left ha'2
  have hb'inv : b'⁻¹ = b' := inv_eq_of_mul_eq_one_left hb'2
  have hinvert : a' * (a' * b') * a'⁻¹ = (a' * b')⁻¹ := by
    rw [mul_inv_rev, ha'inv, hb'inv, ← mul_assoc, ha'2, one_mul]
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hprimary
  have hpow := inverts_zpow hinvert m
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  apply hnoinv (c * a' * c⁻¹) (ha'.trans (isConj_iff.mpr ⟨c, rfl⟩))
  have hu : u = (c * (a' * b') ^ m * c⁻¹)⁻¹ := by rw [hc, inv_inv]
  rw [hu]
  calc c * a' * c⁻¹ * (c * (a' * b') ^ m * c⁻¹)⁻¹ * (c * a' * c⁻¹)⁻¹ =
      (c * (a' * (a' * b') ^ m * a'⁻¹) * c⁻¹)⁻¹ := by group
    _ = (c * (a' * b') ^ m * c⁻¹)⁻¹⁻¹ := by rw [hpow]; group

theorem brauer_noninverting_block_section_vanishing {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (blockLabel : basis.index) (a b u : G) (ha : a * a = 1) (hb : b * b = 1) (e : ℕ)
    (hu : orderOf u ∣ p ^ e) (hnoinv : ∀ t : G, IsConj a t → t * u * t⁻¹ ≠ u⁻¹) :
    (∀ r : G, r ∈ Subgroup.centralizer {u} → Nat.Coprime p (orderOf r) →
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
        (basis.representation label).character a * (basis.representation label).character b *
          (basis.representation label).character (u * r) /
            (basis.representation label).character 1 = 0) ∧
    (∀ ℓ : ({r : G // r ∈ Subgroup.centralizer {u} ∧ Nat.Coprime p (orderOf r)} → ℂ) →ₗ[ℂ] ℂ,
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
        (basis.representation label).character a * (basis.representation label).character b *
          ℓ (fun r => (basis.representation label).character (u * r.val)) /
            (basis.representation label).character 1 = 0) := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel
  set A := conjClassFinset a
  set C := conjClassFinset b
  have hAne : (A.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl a⟩))
  have hCne : (C.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl b⟩))
  have hpair : ∀ label, (basis.representation label).character a *
      (basis.representation label).character b / (basis.representation label).character 1 =
      ((A.card : ℂ) * C.card)⁻¹ * ∑ a' ∈ A, ∑ b' ∈ C,
        (basis.representation label).character (a' * b') := by
    intro label
    have hdeg := irreducible_character_degree_ne_zero (basis.representation label)
      (basis.irreducible label)
    have h := irreducible_character_product_sum (basis.representation label)
      (basis.irreducible label) A C (conjClassFinset_invariant a) (conjClassFinset_invariant b) 1
    simp only [mul_one] at h
    rw [h, character_conjClassFinset_sum, character_conjClassFinset_sum]
    field_simp
    rfl
  have hvanish : ∀ r : G, r ∈ Subgroup.centralizer {u} → Nat.Coprime p (orderOf r) →
      ∑ label ∈ B, (basis.representation label).character a *
        (basis.representation label).character b *
          (basis.representation label).character (u * r) /
            (basis.representation label).character 1 = 0 := by
    intro r hr hrp
    have hcomm : Commute u r := (Subgroup.mem_centralizer_singleton_iff.mp hr).symm
    have hterm : ∀ a' ∈ A, ∀ b' ∈ C, ∑ label ∈ B,
        (basis.representation label).character (a' * b') *
          (basis.representation label).character (u * r) = 0 := by
      intro a' ha' b' hb'
      have ha'c : IsConj a a' := (Finset.mem_filter.mp ha').2
      have hb'c : IsConj b b' := (Finset.mem_filter.mp hb').2
      obtain ⟨primary, regular, exponent, hprimaryMem, _, hpc, hprod, hprimary, hregular⟩ :=
        finite_prime_primary_factorization (a' * b') p Fact.out
      have hnot := primary_part_product_not_conj ha hb hnoinv ha'c hb'c primary hprimaryMem
      have horth := coefficientBlock_section_column_orthogonality basis ideal p blockLabel
        primary u⁻¹ regular r⁻¹ exponent e hprimary (by rwa [orderOf_inv])
        hregular (by rwa [orderOf_inv]) hpc (hcomm.inv_inv) hnot
      rw [hprod] at horth
      have huinv : (u⁻¹ * r⁻¹)⁻¹ = u * r := by rw [mul_inv_rev, inv_inv, inv_inv, hcomm.eq]
      rw [huinv] at horth
      exact horth
    calc ∑ label ∈ B, (basis.representation label).character a *
          (basis.representation label).character b *
            (basis.representation label).character (u * r) /
              (basis.representation label).character 1 =
        ∑ label ∈ B, ((A.card : ℂ) * C.card)⁻¹ * ∑ a' ∈ A, ∑ b' ∈ C,
          (basis.representation label).character (a' * b') *
            (basis.representation label).character (u * r) := by
          apply Finset.sum_congr rfl
          intro label _
          rw [mul_div_right_comm, hpair label, mul_assoc, Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro a' _
          rw [Finset.sum_mul]
      _ = ((A.card : ℂ) * C.card)⁻¹ * ∑ a' ∈ A, ∑ b' ∈ C, ∑ label ∈ B,
          (basis.representation label).character (a' * b') *
            (basis.representation label).character (u * r) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a' _
          rw [Finset.sum_comm]
      _ = 0 := by
          rw [Finset.sum_eq_zero (fun a' ha' => Finset.sum_eq_zero (fun b' hb' =>
            hterm a' ha' b' hb')), mul_zero]
  refine ⟨hvanish, ?_⟩
  intro ℓ
  have hzero : (∑ label ∈ B, ((basis.representation label).character a *
      (basis.representation label).character b / (basis.representation label).character 1) •
        (fun r : {r : G // r ∈ Subgroup.centralizer {u} ∧ Nat.Coprime p (orderOf r)} =>
          (basis.representation label).character (u * r.val))) = 0 := by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hvanish r.val r.property.1 r.property.2]
    apply Finset.sum_congr rfl
    intro label _
    ring
  have h := congrArg ℓ hzero
  rw [map_sum, map_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro label _
  rw [map_smul, smul_eq_mul]
  ring

theorem central_involutions_no_inversion {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hP : ∀ x ∈ (P : Subgroup G), x * x = 1 → ∀ y ∈ (P : Subgroup G), x * y = y * x)
    {x : G} (hx : x ∈ (P : Subgroup G)) (hx2 : x * x ≠ 1) {t : G} (ht : t * t = 1) :
    t * x * t⁻¹ ≠ x⁻¹ := by
  intro hinv
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have htp : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two, ht])
  have hconj : ∀ k : ℤ, t * x ^ k * t⁻¹ = (x ^ k)⁻¹ := inverts_zpow hinv
  have htN : t ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hconj]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers x k)
    · intro hy
      have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
        rw [htinv]
        calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
          _ = y := by rw [ht]; group
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← h2, ← hk, hconj]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers x k)
  have hsup := IsPGroup.to_sup_of_normal_right' htp hxp (Subgroup.zpowers_le.mpr htN)
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hsup
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hmemQ : ∀ y : G, y ∈ (Q : Subgroup G) → g⁻¹ * y * g ∈ (P : Subgroup G) := by
    intro y hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa [MulAut.smul_def, MulAut.conj_apply] using hy
  have htQ : t ∈ (Q : Subgroup G) := hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hxQ : x ∈ (Q : Subgroup G) := hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have ht' : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht]; group
  have hcomm : t * x = x * t := by
    have h := hP _ (hmemQ t htQ) ht' _ (hmemQ x hxQ)
    calc t * x = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [h]
      _ = x * t := by group
  apply hx2
  have h' : t * x * t⁻¹ = x := by rw [hcomm, mul_inv_cancel_right]
  rw [h'] at hinv
  calc x * x = x * x⁻¹ := by rw [← hinv]
    _ = 1 := mul_inv_cancel x

theorem central_sylow_involutions_weighted_block_zero {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (blockLabel : basis.index)
    (P : Sylow 2 G)
    (hP : ∀ x ∈ (P : Subgroup G), x * x = 1 → ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (v : G) (hv : v * v = 1) (μ : ↥(P : Subgroup G) → ℂ)
    (hμ : ∀ x : (P : Subgroup G), (x : G) * x = 1 → μ x = 0) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
      ((Nat.card P : ℂ)⁻¹ * ∑ x : (P : Subgroup G),
          μ x * starRingEnd ℂ ((basis.representation label).character x)) *
        (Complex.normSq ((basis.representation label).character v) : ℂ) /
          (basis.representation label).character 1 = 0 := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv
  have hnorm : ∀ label, (Complex.normSq ((basis.representation label).character v) : ℂ) =
      (basis.representation label).character v * (basis.representation label).character v := by
    intro label
    rw [← Complex.mul_conj, finite_character_conjugate_inverse, hvinv]
  have hzero : ∀ x : (P : Subgroup G), (x : G) * x ≠ 1 →
      ∑ label ∈ B, (basis.representation label).character v *
        (basis.representation label).character v *
          (basis.representation label).character (x : G)⁻¹ /
            (basis.representation label).character 1 = 0 := by
    intro x hx
    have hxinv : (x : G)⁻¹ ∈ (P : Subgroup G) := Subgroup.inv_mem _ x.property
    have hxinv2 : (x : G)⁻¹ * (x : G)⁻¹ ≠ 1 := by
      intro h
      apply hx
      rw [← mul_inv_rev] at h
      exact inv_eq_one.mp h
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨(x : G)⁻¹, hxinv⟩
    have hord : orderOf (x : G)⁻¹ ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have hnoinv : ∀ t : G, IsConj v t → t * (x : G)⁻¹ * t⁻¹ ≠ ((x : G)⁻¹)⁻¹ := by
      intro t ht
      have htt : t * t = 1 := by
        obtain ⟨c, rfl⟩ := isConj_iff.mp ht
        calc c * v * c⁻¹ * (c * v * c⁻¹) = c * (v * v) * c⁻¹ := by group
          _ = 1 := by rw [hv]; group
      exact central_involutions_no_inversion P hP hxinv hxinv2 htt
    have h := (brauer_noninverting_block_section_vanishing basis ideal 2 blockLabel v v
      (x : G)⁻¹ hv hv k hord hnoinv).1 1 (Subgroup.one_mem _) (by simp)
    simpa using h
  have hexpand : ∀ label, ((Nat.card P : ℂ)⁻¹ * ∑ x : (P : Subgroup G),
      μ x * starRingEnd ℂ ((basis.representation label).character x)) *
        (Complex.normSq ((basis.representation label).character v) : ℂ) /
          (basis.representation label).character 1 =
      (Nat.card P : ℂ)⁻¹ * ∑ x : (P : Subgroup G), μ x *
        ((basis.representation label).character v * (basis.representation label).character v *
          (basis.representation label).character (x : G)⁻¹ /
            (basis.representation label).character 1) := by
    intro label
    rw [hnorm, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [finite_character_conjugate_inverse]
    ring
  rw [Finset.sum_congr rfl (fun label _ => hexpand label), ← Finset.mul_sum, Finset.sum_comm]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x _
  rw [← Finset.mul_sum]
  by_cases hx : (x : G) * x = 1
  · rw [hμ x hx, zero_mul]
  · rw [hzero x hx, mul_zero]

end CFSG.LyonsUnitaryFour
