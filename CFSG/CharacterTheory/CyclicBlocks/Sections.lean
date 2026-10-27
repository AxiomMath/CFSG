module

public import CFSG.CharacterTheory.CyclicBlocks.Fusion
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientRegular
public import CFSG.CharacterTheory.Semidihedral.Principal.FourierSupport

public section

open scoped BigOperators Classical

namespace CFSG.CyclicBlocks

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Semidihedral.Principal

variable {G : Type*} [Group G]

theorem mem_of_coprime_orderOf_of_isPGroup_quotient {H : Type*} [Group H] {p : ℕ}
    (R : Subgroup H) [R.Normal] (hquot : IsPGroup p (H ⧸ R)) {y : H}
    (hy : Nat.Coprime p (orderOf y)) : y ∈ R := by
  rw [← QuotientGroup.eq_one_iff]
  obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk y)
  have h1 := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (QuotientGroup.mk (s := R) y) ∣ orderOf y :=
    orderOf_map_dvd (QuotientGroup.mk' R) y
  have hcop : Nat.Coprime (p ^ k) (orderOf y) := hy.pow_left k
  exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)

theorem exists_isConj_mul_of_dvd_orderOf [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {u : G} (hPu : (P : Subgroup G) = Subgroup.zpowers u) {g : G} (hg : p ∣ orderOf g) :
    ∃ x ∈ Subgroup.zpowers u, x ≠ 1 ∧
      ∃ y : G, Commute x y ∧ ¬ p ∣ orderOf y ∧ IsConj g (x * y) := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, b, e, -, -, hab, habz, ha, hb⟩ := finite_prime_primary_factorization g p hp
  have hane : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at habz
    rw [← habz] at hg
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hb hg
  obtain ⟨k₀, -, hk₀⟩ := (Nat.dvd_prime_pow hp).mp ha
  have hpa : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := k₀) (by rw [Nat.card_zpowers, hk₀])
  obtain ⟨Q, hQ⟩ := hpa.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q P
  have hmem : c * a * c⁻¹ ∈ (P : Subgroup G) := by
    have h := Subgroup.smul_mem_pointwise_smul a (MulAut.conj c) (Q : Subgroup G)
      (hQ (Subgroup.mem_zpowers a))
    rw [MulAut.smul_def, MulAut.conj_apply] at h
    rw [← hc, Sylow.coe_subgroup_smul]
    exact h
  rw [hPu] at hmem
  refine ⟨c * a * c⁻¹, hmem, ?_, c * b * c⁻¹, hab.map (MulAut.conj c).toMonoidHom, ?_, ?_⟩
  · intro h
    apply hane
    calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · rw [orderOf_conj_eq]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hb
  · refine isConj_iff.mpr ⟨c, ?_⟩
    rw [← habz]
    group

variable [Fintype G]

theorem principalCyclicProjection_isConj (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (u : G) (h : Subgroup.zpowers u → ℂ) {g g' : G}
    (hgg' : IsConj g g') :
    principalCyclicProjection basis B u h g = principalCyclicProjection basis B u h g' := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hgg'
  unfold principalCyclicProjection
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [← hc]
  simp only [FiniteComplexRepresentation.character, Representation.char_conj]

section Sections

variable (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]

theorem principal_section_constant (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) {u : G}
    (hPu : (P : Subgroup G) = Subgroup.zpowers u)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {x : G} (hx : x ∈ Subgroup.zpowers u) (hx1 : x ≠ 1) {y : G} (hxy : Commute x y)
    (hy : ¬ p ∣ orderOf y) {θ : basis.index}
    (hθ : θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    (basis.representation θ).character (x * y) = (basis.representation θ).character x := by
  have hp : p.Prime := Fact.out
  have hxord : orderOf x ∣ p ^ (Nat.card G).factorization p :=
    (orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_sylow_eq_zpowers P hPu)
  obtain ⟨R, hR, hcop, hquot⟩ := exists_normal_complement_centralizer hp2 P hPu hindex hx hx1
  have hyC : y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    CFSG.LyonsUnitaryFour.mem_centralizer_zpowers_of_commute hxy
  have hyR : (⟨y, hyC⟩ : Subgroup.centralizer (Subgroup.zpowers x : Set G)) ∈ R := by
    apply mem_of_coprime_orderOf_of_isPGroup_quotient R hquot
    rw [Subgroup.orderOf_mk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hy
  exact principal_character_section_constant_of_normal_complement basis ideal p principal
    hprincipal hxord R hcop hquot hθ hyR

theorem principal_column_norm (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) {u : G}
    (hPu : (P : Subgroup G) = Subgroup.zpowers u)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {x : G} (hx : x ∈ Subgroup.zpowers u) (hx1 : x ≠ 1) :
    ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation θ).character x *
          starRingEnd ℂ ((basis.representation θ).character x) = Nat.card P := by
  have hxord : orderOf x ∣ p ^ (Nat.card G).factorization p :=
    (orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_sylow_eq_zpowers P hPu)
  obtain ⟨R, hR, hcop, hquot⟩ := exists_normal_complement_centralizer hp2 P hPu hindex hx hx1
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers x : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨hcolumn, hdegrees, hsylow⟩ :=
    principal_primary_column_centralizer_norm_of_normal_complement basis ideal p principal
      hprincipal x _ hxord localBasis localPrincipal hlocalPrincipal R hcop hquot
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    hPu ▸ zpowers_le_centralizer_zpowers hx
  rw [hcolumn, hdegrees, hsylow (P.subtype hle), Sylow.coe_subtype,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem principalCyclicProjection_eq_zero_of_coprime (label : basis.index) {u : G} {e : ℕ}
    (hu : orderOf u ∣ p ^ e) (h : Subgroup.zpowers u → ℂ) (h1 : h 1 = 0) {g : G}
    (hg : ¬ p ∣ orderOf g) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
      label) u h g = 0 := by
  have hp : p.Prime := Fact.out
  rw [principalCyclicProjection_eq_sum]
  apply mul_eq_zero_of_right
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x = 1
  · rw [hx, inv_one, h1, zero_mul]
  · apply mul_eq_zero_of_right
    have hxne : (x : G) ≠ 1 := fun h' => hx (Subtype.ext h')
    have hxord : orderOf (x : G) ∣ p ^ e := (orderOf_dvd_of_mem_zpowers x.2).trans hu
    have horth := coefficientBlock_section_column_orthogonality basis ideal p label
      (x : G) 1 1 g⁻¹ e 0 hxord (by simp) (by simp)
      (by rw [orderOf_inv]; exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hg)
      (Commute.one_right _) (Commute.one_left _) (fun hc => hxne (isConj_one_left.mp hc))
    simpa using horth

theorem principalCyclicProjection_section (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) {u : G}
    (hPu : (P : Subgroup G) = Subgroup.zpowers u)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    (h : Subgroup.zpowers u → ℂ) (z : Subgroup.zpowers u) (hz : z ≠ 1) {y : G}
    (hzy : Commute (z : G) y) (hy : ¬ p ∣ orderOf y) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal) u h ((z : G) * y) = h z + h z⁻¹ := by
  have hp : p.Prime := Fact.out
  have hu := orderOf_dvd_of_sylow_eq_zpowers P hPu
  have hx : (z : G) ∈ Subgroup.zpowers u := z.2
  have hx1 : (z : G) ≠ 1 := fun h' => hz (Subtype.ext h')
  have hxord : orderOf (z : G) ∣ p ^ (Nat.card G).factorization p :=
    (orderOf_dvd_of_mem_zpowers hx).trans hu
  have hxodd : Odd (orderOf (z : G)) := odd_orderOf_of_dvd_prime_pow hp hp2 hxord
  have hyreg : Nat.Coprime p (orderOf y) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hy
  have hconst : ∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation θ).character ((z : G) * y) =
        (basis.representation θ).character (z : G) := fun θ hθ =>
    principal_section_constant basis ideal p hp2 principal hprincipal P hPu hindex hx hx1 hzy hy
      hθ
  obtain ⟨n, -, -, hn⟩ := exists_mem_normalizer_conj_eq_inv_of_dvd_prime_pow hp hp2 hu hindex
  have hθinv : ∀ θ : basis.index, (basis.representation θ).character (z : G)⁻¹ =
      (basis.representation θ).character (z : G) := by
    intro θ
    rw [← conj_mem_zpowers_eq_inv hx hn]
    simp only [FiniteComplexRepresentation.character, Representation.char_conj]
  have hθconj : ∀ θ : basis.index, (basis.representation θ).character (z : G)⁻¹ =
      starRingEnd ℂ ((basis.representation θ).character (z : G)) := fun θ =>
    (finite_character_conjugate_inverse _ _).symm
  have hnorm := principal_column_norm basis ideal p hp2 principal hprincipal P hPu hindex hx hx1
  have hzz : z⁻¹ ≠ z := by
    intro heq
    exact hx1 (eq_one_of_inv_eq_self_of_odd hxodd (congrArg Subtype.val heq))
  have hS₁ : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation θ).character ((z⁻¹ : Subgroup.zpowers u) : G) *
        (basis.representation θ).character ((z : G) * y) = Nat.card P := by
    rw [← hnorm]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [Subgroup.coe_inv, hconst θ hθ, hθconj, mul_comm]
  have hS₂ : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation θ).character (z : G) *
        (basis.representation θ).character ((z : G) * y) = Nat.card P := by
    rw [← hnorm]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [hconst θ hθ, ← hθconj, hθinv]
  have hcard : (Nat.card (Subgroup.zpowers u) : ℂ) = Nat.card P := by
    rw [← hPu]
  rw [principalCyclicProjection_eq_sum, Fintype.sum_eq_add z⁻¹ z hzz, inv_inv, hS₁, hS₂, hcard]
  · have hP0 : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp
  · rintro w ⟨hw1, hw2⟩
    apply mul_eq_zero_of_right
    have hnot : ¬ IsConj (w : G) (z : G)⁻¹ := by
      intro hc
      rcases eq_or_eq_inv_of_isConj hp2 P hPu hindex w.2 (Subgroup.inv_mem _ hx) hc with h' | h'
      · exact hw1 (Subtype.ext h'.symm)
      · exact hw2 (Subtype.ext (inv_injective h').symm)
    have hword : orderOf (w : G) ∣ p ^ (Nat.card G).factorization p :=
      (orderOf_dvd_of_mem_zpowers w.2).trans hu
    have hxinvord : orderOf (z : G)⁻¹ ∣ p ^ (Nat.card G).factorization p := by
      rw [orderOf_inv]
      exact hxord
    have horth := coefficientBlock_section_column_orthogonality basis ideal p principal
      (w : G) (z : G)⁻¹ 1 y⁻¹ _ _ hword hxinvord (by simp)
      (by rw [orderOf_inv]; exact hyreg) (Commute.one_right _) hzy.inv_inv hnot
    have hrw : ((z : G)⁻¹ * y⁻¹)⁻¹ = (z : G) * y := by
      rw [mul_inv_rev, inv_inv, inv_inv]
      exact hzy.eq.symm
    rw [hrw, mul_one] at horth
    exact horth

end Sections

end CFSG.CyclicBlocks
