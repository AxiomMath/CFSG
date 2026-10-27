module

public import CFSG.CharacterTheory.Semidihedral.Principal.OddFourierFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.Principal

variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}

@[expose] def RotationColumns (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) (B : Finset basis.index) : Prop :=
  (∀ i j : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
    ¬ j ≡ 0 [ZMOD modulus n] → ¬ j ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
    ∑ χ ∈ B, (basis.representation χ).character ((e (r n) : G) ^ i) *
        starRingEnd ℂ ((basis.representation χ).character ((e (r n) : G) ^ j)) =
      if j ≡ i [ZMOD modulus n] ∨ j ≡ (((modulus n / 2 : ℕ) : ℤ) - 1) * i [ZMOD modulus n]
      then (modulus n : ℂ) else 0) ∧
  (∀ i : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
    ∀ x : G, (∀ a c : G, a * c = x → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
        Odd (orderOf c) → ¬ IsConj a ((e (r n) : G) ^ i)) →
      ∑ χ ∈ B, (basis.representation χ).character ((e (r n) : G) ^ i) *
        starRingEnd ℂ ((basis.representation χ).character x) = 0)

variable (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
  (B : Finset basis.index)

theorem rotation_column_pair_of (hn : 4 ≤ n) (hcols : RotationColumns e basis B) {v w : ℤ}
    (hv0 : ¬ v ≡ 0 [ZMOD modulus n]) (hv1 : ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n])
    (hw0 : ¬ w ≡ 0 [ZMOD modulus n]) (hw1 : ¬ w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∑ χ ∈ B, (basis.representation χ).character ((e (r n) : G) ^ w) *
          (basis.representation χ).character ((e (r n) : G) ^ v) =
      if (e (r n) : G) ^ w = (e (r n) : G) ^ (-v) ∨
          (e (r n) : G) ^ w = (e (r n) : G) ^ (-((((modulus n / 2 : ℕ) : ℤ) - 1) * v))
      then (modulus n : ℂ) else 0 := by
  obtain ⟨hnv0, hnv1⟩ := noncentral_neg hn hv0 hv1
  have hgram := hcols.1 w (-v) hw0 hw1 hnv0 hnv1
  have hval : ∀ χ : basis.index, (basis.representation χ).character ((e (r n) : G) ^ v) =
      starRingEnd ℂ ((basis.representation χ).character ((e (r n) : G) ^ (-v))) := by
    intro χ
    rw [finite_character_conjugate_inverse, zpow_neg, inv_inv]
  simp only [hval]
  rw [hgram]
  have hsq := twist_sq_modEq hn
  congr 1
  apply propext
  rw [suppliedRotation_zpow_eq_iff (by omega) e, suppliedRotation_zpow_eq_iff (by omega) e,
    twist_modEq_iff hsq]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h

theorem cyclicProjection_noncentral_value_of (hn : 4 ≤ n) (hcols : RotationColumns e basis B)
    {f : Subgroup.zpowers (e (r n) : G) → ℂ} (h1 : f 1 = 0)
    (ht : f ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0) {v : ℤ}
    (hv0 : ¬ v ≡ 0 [ZMOD modulus n]) (hv1 : ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    principalCyclicProjection basis B (e (r n) : G) f ((e (r n) : G) ^ v) =
      f ⟨(e (r n) : G) ^ v, Subgroup.zpow_mem_zpowers _ _⟩ +
        f ⟨(e (r n) : G) ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * v),
          Subgroup.zpow_mem_zpowers _ _⟩ := by
  have hnc := rotationFusion_twist_noncentral hn v hv0 hv1
  obtain ⟨hnv0, hnv1⟩ := noncentral_neg hn hv0 hv1
  obtain ⟨hnav0, hnav1⟩ := noncentral_neg hn hnc.1 hnc.2.1
  let p₁ : Subgroup.zpowers (e (r n) : G) :=
    ⟨(e (r n) : G) ^ (-v), Subgroup.zpow_mem_zpowers _ _⟩
  let p₂ : Subgroup.zpowers (e (r n) : G) :=
    ⟨(e (r n) : G) ^ (-((((modulus n / 2 : ℕ) : ℤ) - 1) * v)), Subgroup.zpow_mem_zpowers _ _⟩
  have hp₁ : ∀ w : ℤ, (⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ :
      Subgroup.zpowers (e (r n) : G)) = p₁ ↔ w ≡ -v [ZMOD modulus n] := fun w => by
    rw [Subtype.mk.injEq, suppliedRotation_zpow_eq_iff (by omega) e]
  have hp₂ : ∀ w : ℤ, (⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ :
      Subgroup.zpowers (e (r n) : G)) = p₂ ↔
        w ≡ -((((modulus n / 2 : ℕ) : ℤ) - 1) * v) [ZMOD modulus n] := fun w => by
    rw [Subtype.mk.injEq, suppliedRotation_zpow_eq_iff (by omega) e]
  have hne : p₁ ≠ p₂ := by
    intro heq
    have hv' := (hp₂ (-v)).mp heq
    apply hnc.2.2
    have hv'' := hv'.neg
    rw [neg_neg, neg_neg] at hv''
    exact hv''.symm
  rw [principalCyclicProjection_eq_sum]
  have hterm : ∀ x : Subgroup.zpowers (e (r n) : G), f x⁻¹ *
      ∑ χ ∈ B, (basis.representation χ).character x *
        (basis.representation χ).character ((e (r n) : G) ^ v) =
      if x = p₁ ∨ x = p₂ then (modulus n : ℂ) * f x⁻¹ else 0 := by
    intro x
    obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.mp x.2
    have hxw : x = ⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ := Subtype.ext hw.symm
    subst hxw
    simp only [hp₁, hp₂]
    by_cases hw0 : w ≡ 0 [ZMOD modulus n]
    · have hx1 : (⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ :
          Subgroup.zpowers (e (r n) : G)) = 1 := by
        apply Subtype.ext
        show (e (r n) : G) ^ w = 1
        rw [← zpow_zero (e (r n) : G), suppliedRotation_zpow_eq_iff (by omega) e]
        exact hw0
      have hnot : ¬ (w ≡ -v [ZMOD modulus n] ∨
          w ≡ -((((modulus n / 2 : ℕ) : ℤ) - 1) * v) [ZMOD modulus n]) := by
        rintro (hh | hh)
        · exact hnv0 (hh.symm.trans hw0)
        · exact hnav0 (hh.symm.trans hw0)
      rw [ite_eq_right hnot, hx1, inv_one, h1, zero_mul]
    by_cases hw1 : w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]
    · have hxt : (⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ :
          Subgroup.zpowers (e (r n) : G)) =
          ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ := by
        apply Subtype.ext
        show (e (r n) : G) ^ w = (e (r n) : G) ^ (modulus n / 2)
        rw [← zpow_natCast, suppliedRotation_zpow_eq_iff (by omega) e]
        exact hw1
      have hxinv : (⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ :
          Subgroup.zpowers (e (r n) : G))⁻¹ =
          ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_inv, inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul,
          show 2 * (modulus n / 2) = modulus n by
            unfold modulus; rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; omega,
          ← suppliedRotation_orderOf (by omega) e, pow_orderOf_eq_one]
      have hnot : ¬ (w ≡ -v [ZMOD modulus n] ∨
          w ≡ -((((modulus n / 2 : ℕ) : ℤ) - 1) * v) [ZMOD modulus n]) := by
        rintro (hh | hh)
        · exact hnv1 (hh.symm.trans hw1)
        · exact hnav1 (hh.symm.trans hw1)
      rw [ite_eq_right hnot, hxt, hxinv, ht, zero_mul]
    · show f _ * ∑ χ ∈ B, (basis.representation χ).character ((e (r n) : G) ^ w) *
          (basis.representation χ).character ((e (r n) : G) ^ v) = _
      rw [rotation_column_pair_of e basis B hn hcols hv0 hv1 hw0 hw1]
      have hcond : ((e (r n) : G) ^ w = (e (r n) : G) ^ (-v) ∨
          (e (r n) : G) ^ w = (e (r n) : G) ^ (-((((modulus n / 2 : ℕ) : ℤ) - 1) * v))) ↔
          (w ≡ -v [ZMOD modulus n] ∨
            w ≡ -((((modulus n / 2 : ℕ) : ℤ) - 1) * v) [ZMOD modulus n]) := by
        rw [suppliedRotation_zpow_eq_iff (by omega) e, suppliedRotation_zpow_eq_iff (by omega) e]
      by_cases hc' : w ≡ -v [ZMOD modulus n] ∨
          w ≡ -((((modulus n / 2 : ℕ) : ℤ) - 1) * v) [ZMOD modulus n]
      · rw [ite_eq_left hc', ite_eq_left (hcond.mpr hc')]
        ring
      · rw [ite_eq_right hc', ite_eq_right (fun hh => hc' (hcond.mp hh)), mul_zero]
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : Finset.univ.filter (fun x : Subgroup.zpowers (e (r n) : G) =>
      x = p₁ ∨ x = p₂) = {p₁, p₂} := by
    ext x; simp
  rw [hfilter, Finset.sum_pair hne]
  have hinv₁ : p₁⁻¹ = ⟨(e (r n) : G) ^ v, Subgroup.zpow_mem_zpowers _ _⟩ := by
    apply Subtype.ext
    show ((e (r n) : G) ^ (-v))⁻¹ = (e (r n) : G) ^ v
    rw [zpow_neg, inv_inv]
  have hinv₂ : p₂⁻¹ = ⟨(e (r n) : G) ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * v),
      Subgroup.zpow_mem_zpowers _ _⟩ := by
    apply Subtype.ext
    show ((e (r n) : G) ^ (-((((modulus n / 2 : ℕ) : ℤ) - 1) * v)))⁻¹ =
      (e (r n) : G) ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * v)
    rw [zpow_neg, inv_inv]
  rw [hinv₁, hinv₂, Nat.card_zpowers, suppliedRotation_orderOf (by omega) e]
  have hM : (modulus n : ℂ) ≠ 0 := by
    have : 0 < modulus n := by unfold modulus; positivity
    exact_mod_cast this.ne'
  field_simp

omit [Fintype G] in
theorem sq_eq_one_of_primary_part {a c : G} (hcomm : Commute a c)
    (ha : ∃ k : ℕ, orderOf a = 2 ^ k) (hc : Odd (orderOf c)) (hx : (a * c) ^ 2 = 1) :
    a ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := ha
  have h2 : a ^ 2 = (c ^ 2)⁻¹ := by
    rw [hcomm.mul_pow] at hx
    exact eq_inv_of_mul_eq_one_left hx
  have hd1 : orderOf (a ^ 2) ∣ 2 ^ k := hk ▸ orderOf_pow_dvd 2
  have hd2 : orderOf (a ^ 2) ∣ orderOf c := by
    rw [h2, orderOf_inv]
    exact orderOf_pow_dvd 2
  have hcop : Nat.Coprime (2 ^ k) (orderOf c) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hc)
  have h1 : orderOf (a ^ 2) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact orderOf_eq_one_iff.mp h1

omit [Fintype G] in
theorem not_isConj_rotation_of_sq_eq_one (hn : 4 ≤ n) {x : G} (hx : x ^ 2 = 1) {w : ℤ}
    (hw0 : ¬ w ≡ 0 [ZMOD modulus n]) (hw1 : ¬ w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∀ a c : G, a * c = x → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
      Odd (orderOf c) → ¬ IsConj a ((e (r n) : G) ^ w) := by
  intro a c hac hcomm ha hc hconj
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_primary_part hcomm ha hc (by rw [hac]; exact hx)
  have h := hconj.pow 2
  rw [ha2, isConj_one_right] at h
  exact noncentralRotation_sq_ne_one (by omega) e w hw0 hw1 h

theorem cyclicProjection_rotation_value_of (hn : 4 ≤ n) (hcols : RotationColumns e basis B)
    {f : Subgroup.zpowers (e (r n) : G) → ℂ} (h1 : f 1 = 0)
    (ht : f ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0) (v : ℤ) :
    principalCyclicProjection basis B (e (r n) : G) f ((e (r n) : G) ^ v) =
      f ⟨(e (r n) : G) ^ v, Subgroup.zpow_mem_zpowers _ _⟩ +
        f ⟨(e (r n) : G) ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * v),
          Subgroup.zpow_mem_zpowers _ _⟩ := by
  by_cases hv0 : v ≡ 0 [ZMOD modulus n]
  · have hav : (((modulus n / 2 : ℕ) : ℤ) - 1) * v ≡ 0 [ZMOD modulus n] := by
      simpa using hv0.mul_left ((((modulus n / 2 : ℕ) : ℤ) - 1))
    have hx : ∀ w : ℤ, w ≡ 0 [ZMOD modulus n] →
        (⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ : Subgroup.zpowers (e (r n) : G)) =
          1 := fun w hw => Subtype.ext (by
      show (e (r n) : G) ^ w = 1
      rw [← zpow_zero (e (r n) : G), suppliedRotation_zpow_eq_iff (by omega) e]
      exact hw)
    rw [hx v hv0, hx _ hav, h1, add_zero]
    have hg : (e (r n) : G) ^ v = 1 := congrArg Subtype.val (hx v hv0)
    rw [hg]
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ h1 ht fun w hw0 hw1 => ?_
    rw [inv_one]
    exact hcols.2 w hw0 hw1 1 (not_isConj_rotation_of_sq_eq_one e hn (one_pow 2) hw0 hw1)
  by_cases hv1 : v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]
  · have hav : (((modulus n / 2 : ℕ) : ℤ) - 1) * v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
      have h := hv1.mul_left ((((modulus n / 2 : ℕ) : ℤ) - 1))
      refine h.trans ?_
      rw [Int.modEq_iff_dvd]
      obtain ⟨K, -, hK2, -⟩ := modulus_eq_four_mul hn
      refine ⟨1 - ((modulus n / 4 : ℕ) : ℤ), ?_⟩
      have h4 : (modulus n : ℤ) = 4 * ((modulus n / 4 : ℕ) : ℤ) := by
        have : 4 ∣ modulus n := ⟨2 ^ (n - 3), K⟩
        omega
      have h2' : ((modulus n / 2 : ℕ) : ℤ) = 2 * ((modulus n / 4 : ℕ) : ℤ) := by omega
      rw [h2', h4]
      ring
    have hx : ∀ w : ℤ, w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
        (⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ : Subgroup.zpowers (e (r n) : G)) =
          ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ :=
      fun w hw => Subtype.ext (by
        show (e (r n) : G) ^ w = (e (r n) : G) ^ (modulus n / 2)
        rw [← zpow_natCast, suppliedRotation_zpow_eq_iff (by omega) e]
        exact hw)
    rw [hx v hv1, hx _ hav, ht, add_zero]
    have hg : (e (r n) : G) ^ v = (e (r n) : G) ^ (modulus n / 2) :=
      congrArg Subtype.val (hx v hv1)
    rw [hg]
    have hord := suppliedRotation_half_orderOf hn e
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ h1 ht fun w hw0 hw1 => ?_
    have hsq : ((e (r n) : G) ^ (modulus n / 2))⁻¹ ^ 2 = 1 := by
      rw [inv_pow, orderOf_dvd_iff_pow_eq_one.mp (show orderOf _ ∣ 2 by rw [hord]), inv_one]
    exact hcols.2 w hw0 hw1 _ (not_isConj_rotation_of_sq_eq_one e hn hsq hw0 hw1)
  · exact cyclicProjection_noncentral_value_of e basis B hn hcols h1 ht hv0 hv1

theorem cyclicProjection_gram_sum_of (hn : 4 ≤ n) (hcols : RotationColumns e basis B)
    {f : Subgroup.zpowers (e (r n) : G) → ℂ} (h1 : f 1 = 0)
    (ht : f ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0)
    (f' : Subgroup.zpowers (e (r n) : G) → ℂ) :
    ∑ χ ∈ B, characterPairing (fun x : Subgroup.zpowers (e (r n) : G) =>
          (basis.representation χ).character x) f *
        characterPairing (fun x : Subgroup.zpowers (e (r n) : G) =>
          (basis.representation χ).character x) f' =
      (modulus n : ℂ)⁻¹ * ∑ v ∈ Finset.range (modulus n),
        (f ⟨(e (r n) : G) ^ (v : ℤ), Subgroup.zpow_mem_zpowers _ _⟩ +
          f ⟨(e (r n) : G) ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * (v : ℤ)),
            Subgroup.zpow_mem_zpowers _ _⟩) *
        f' ⟨(e (r n) : G) ^ (-(v : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩ := by
  rw [principalCyclicProjection_coefficient_gram,
    characterPairing_zpowers_eq_sum_range (suppliedRotation_orderOf (by omega) e)]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [cyclicProjection_rotation_value_of e basis B hn hcols h1 ht]

theorem multiplicityColumn_difference_gram_of (hn : 4 ≤ n) (hcols : RotationColumns e basis B)
    (p q p' q' : ℤ) (hpq : Even (p - q)) :
    ∑ χ ∈ B,
        (multiplicityColumn basis (e (r n) : G) (modulus n) p χ -
          multiplicityColumn basis (e (r n) : G) (modulus n) q χ) *
        (multiplicityColumn basis (e (r n) : G) (modulus n) p' χ -
          multiplicityColumn basis (e (r n) : G) (modulus n) q' χ) =
      residueIndicator (modulus n) p p' - residueIndicator (modulus n) p q' -
        residueIndicator (modulus n) q p' + residueIndicator (modulus n) q q' +
        residueIndicator (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * p) p' -
        residueIndicator (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * p) q' -
        residueIndicator (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * q) p' +
        residueIndicator (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * q) q' := by
  have hord := suppliedRotation_orderOf (by omega) e
  have hM : 0 < modulus n := by unfold modulus; positivity
  set a : ℤ := ((modulus n / 2 : ℕ) : ℤ) - 1 with ha
  set ζ := cyclicRoot (modulus n) with hζ
  have hlam : ∀ j k : ℤ, cyclicLinearCharacter (e (r n) : G) (modulus n) j
      ⟨(e (r n) : G) ^ k, Subgroup.zpow_mem_zpowers _ _⟩ = ζ ^ (j * k) := fun j k =>
    cyclicLinearCharacter_zpow hord j k
  have h1 : (fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p x -
      cyclicLinearCharacter (e (r n) : G) (modulus n) q x) (1 : Subgroup.zpowers (e (r n) : G)) =
      0 := by
    simp only [cyclicLinearCharacter_one hord, sub_self]
  have ht : (fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p x -
      cyclicLinearCharacter (e (r n) : G) (modulus n) q x)
      ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := by
    simp only [cyclicLinearCharacter_half hn e]
    obtain ⟨k, hk⟩ := hpq
    rw [show p = q + (k + k) by omega, zpow_add₀ (by norm_num), ← two_mul, zpow_mul]
    norm_num
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_add]
  have hgram := cyclicProjection_gram_sum_of e basis B hn hcols
    (f := fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p x -
      cyclicLinearCharacter (e (r n) : G) (modulus n) q x) h1 ht
    (fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p' x -
      cyclicLinearCharacter (e (r n) : G) (modulus n) q' x)
  simp only [characterPairing_linear_difference hn e basis, Int.cast_sub] at hgram
  rw [hgram]
  simp only [hlam]
  have hexp : ∀ v : ℕ, (ζ ^ (p * (v : ℤ)) - ζ ^ (q * (v : ℤ)) +
      (ζ ^ (p * (a * (v : ℤ))) - ζ ^ (q * (a * (v : ℤ))))) *
      (ζ ^ (p' * -(v : ℤ)) - ζ ^ (q' * -(v : ℤ))) =
      ζ ^ ((p - p') * (v : ℤ)) - ζ ^ ((p - q') * (v : ℤ)) - ζ ^ ((q - p') * (v : ℤ)) +
        ζ ^ ((q - q') * (v : ℤ)) + ζ ^ ((a * p - p') * (v : ℤ)) -
        ζ ^ ((a * p - q') * (v : ℤ)) - ζ ^ ((a * q - p') * (v : ℤ)) +
        ζ ^ ((a * q - q') * (v : ℤ)) := by
    intro v
    rw [show p * (a * (v : ℤ)) = (a * p) * v by ring, show q * (a * (v : ℤ)) = (a * q) * v by ring]
    simp only [add_mul, sub_mul, mul_sub, hζ, cyclicRoot_zpow_mul_neg]
    ring
  rw [Finset.sum_congr rfl fun v _ => hexp v]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub, hζ,
    cyclicRoot_average _ hM, residueIndicator]
  simp only [apply_ite (Int.cast : ℤ → ℂ), Int.cast_one, Int.cast_zero]

theorem even_family_coefficient_gram_of (hn : 4 ≤ n) (hcols : RotationColumns e basis B) :
    let L := multiplicityColumn basis (e (r n) : G) (modulus n)
    let θ : basis.index → ℤ := fun c => L 0 c - L ((modulus n / 2 : ℕ) : ℤ) c
    let η : ℕ → basis.index → ℤ := fun l c => L 0 c - L (2 * l) c
    ∑ c ∈ B, θ c * θ c = 4 ∧
    (∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 → ∑ c ∈ B, θ c * η l c = 2) ∧
    (∀ j l : ℕ, 1 ≤ j → j ≤ modulus n / 4 - 1 → 1 ≤ l → l ≤ modulus n / 4 - 1 →
      ∑ c ∈ B, η j c * η l c = 2 + if j = l then 1 else 0) := by
  intro L θ η
  obtain ⟨hM, -, hK2, -⟩ := modulus_eq_four_mul hn
  set K : ℕ := 2 ^ (n - 3) with hK
  set h : ℤ := ((modulus n / 2 : ℕ) : ℤ) with hh
  have hhK : h = 2 * (K : ℤ) := by rw [hh]; omega
  have hMK : (modulus n : ℤ) = 4 * (K : ℤ) := by rw [hM]; push_cast; ring
  have hquarter : modulus n / 4 = K := by omega
  have hgram := multiplicityColumn_difference_gram_of e basis B hn hcols
  have e00 : residueIndicator (modulus n) 0 0 = 1 := residueIndicator_self _ _
  have e0h : residueIndicator (modulus n) 0 h = 0 :=
    residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega)
  have eh0 : residueIndicator (modulus n) h 0 = 0 :=
    residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega)
  have ehh : residueIndicator (modulus n) h h = 1 := residueIndicator_self _ _
  have eah : ∀ y, residueIndicator (modulus n) ((h - 1) * h) y =
      residueIndicator (modulus n) h y :=
    fun y => residueIndicator_congr_left y (by
      rw [Int.modEq_iff_dvd, hMK, hhK]
      exact ⟨1 - (K : ℤ), by ring⟩)
  have e2l : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      residueIndicator (modulus n) 0 (2 * l) = 0 ∧ residueIndicator (modulus n) (2 * l) 0 = 0 ∧
      residueIndicator (modulus n) h (2 * l) = 0 ∧
      (∀ y, residueIndicator (modulus n) ((h - 1) * (2 * l)) y =
        residueIndicator (modulus n) (-(2 * l)) y) ∧
      residueIndicator (modulus n) (-(2 * l)) 0 = 0 := by
    intro l hl1 hl2
    refine ⟨residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega),
      residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega),
      residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega),
      fun y => residueIndicator_congr_left y ?_,
      residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega)⟩
    rw [Int.modEq_iff_dvd, hMK, hhK]
    exact ⟨-(l : ℤ), by ring⟩
  have ejl : ∀ j l : ℕ, 1 ≤ j → j ≤ modulus n / 4 - 1 → 1 ≤ l → l ≤ modulus n / 4 - 1 →
      residueIndicator (modulus n) (2 * j) (2 * l) = (if j = l then 1 else 0) ∧
      residueIndicator (modulus n) (-(2 * j)) (2 * l) = 0 := by
    intro j l hj1 hj2 hl1 hl2
    refine ⟨?_, residueIndicator_eq_zero_of_abs_lt (by omega)
      (by rw [abs_lt]; constructor <;> omega)⟩
    by_cases hjl : j = l
    · rw [ite_eq_left hjl, hjl]
      exact residueIndicator_self _ _
    · rw [ite_eq_right hjl]
      exact residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega)
  refine ⟨?_, fun l hl1 hl2 => ?_, fun j l hj1 hj2 hl1 hl2 => ?_⟩
  · rw [hgram 0 h 0 h ⟨-(K : ℤ), by omega⟩, mul_zero, e00, e0h, eh0, ehh, eah, eah, eh0, ehh]
    norm_num
  · obtain ⟨a0l, al0, ahl, -, -⟩ := e2l l hl1 hl2
    rw [hgram 0 h 0 (2 * l) ⟨-(K : ℤ), by omega⟩, mul_zero, e00, a0l, eh0, ahl, eah, eah, eh0,
      ahl]
    norm_num
  · obtain ⟨a0l, -, -, -, -⟩ := e2l l hl1 hl2
    obtain ⟨-, aj0, -, ajt, ajn0⟩ := e2l j hj1 hj2
    obtain ⟨hjl, hnjl⟩ := ejl j l hj1 hj2 hl1 hl2
    rw [hgram 0 (2 * j) 0 (2 * l) ⟨-(j : ℤ), by omega⟩, mul_zero, e00, a0l, aj0, hjl, ajt, ajt,
      ajn0, hnjl]
    split_ifs <;> norm_num

theorem odd_family_coefficient_gram_of (hn : 4 ≤ n) (hcols : RotationColumns e basis B)
    {I : Finset (ZMod (modulus n))}
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I) :
    let L := multiplicityColumn basis (e (r n) : G) (modulus n)
    let φ : ZMod (modulus n) → basis.index → ℤ := fun j c => L j.val c - L 1 c
    let θ : basis.index → ℤ := fun c => L 0 c - L ((modulus n / 2 : ℕ) : ℤ) c
    let η : ℕ → basis.index → ℤ := fun l c => L 0 c - L (2 * l) c
    (∀ j ∈ I, ∀ k ∈ I, j ≠ 1 → k ≠ 1 →
      ∑ c ∈ B, φ j c * φ k c = 1 + if j = k then 1 else 0) ∧
    (∀ j ∈ I, ∑ c ∈ B, φ j c * θ c = 0) ∧ (∀ j ∈ I, ∀ l : ℕ, ∑ c ∈ B, φ j c * η l c = 0) := by
  intro L φ θ η
  obtain ⟨hM4, hKeven, hK2, -⟩ := modulus_eq_four_mul hn
  have hgram := multiplicityColumn_difference_gram_of e basis B hn hcols
  have hMeven : Even (modulus n) := ⟨2 * 2 ^ (n - 3), by omega⟩
  have haodd : Odd (((modulus n / 2 : ℕ) : ℤ) - 1) := ⟨((2 ^ (n - 3) : ℕ) : ℤ) - 1, by omega⟩
  have hhalfeven : Even ((modulus n / 2 : ℕ) : ℤ) := ⟨((2 ^ (n - 3) : ℕ) : ℤ), by omega⟩
  have hjodd : ∀ j ∈ I, Odd ((j.val : ℕ) : ℤ) := fun j hj => by exact_mod_cast hI.odd j hj
  have hone : (1 : ZMod (modulus n)) ∈ I := hI.one_mem
  have hnotI : ∀ j ∈ I, (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j ∉ I := fun j hj =>
    twist_mul_not_mem_of_isOddResidueTransversal hn hI hj
  have hz : ∀ x y : ℤ, Odd x → Even y → residueIndicator (modulus n) x y = 0 := fun x y hx hy =>
    residueIndicator_eq_zero_of_odd_sub hMeven (hx.sub_even hy)
  refine ⟨fun j hj k hk hj1 hk1 => ?_, fun j hj => ?_, fun j hj l => ?_⟩
  · have hev : Even (((j.val : ℕ) : ℤ) - 1) := (hjodd j hj).sub_odd odd_one
    rw [hgram _ 1 _ 1 hev]
    simp only [residueIndicator_eq_zmod, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      Int.cast_one, ZMod.natCast_zmod_val, mul_one]
    have h3 : ¬ (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j = k := fun h =>
      hnotI j hj (by rw [h]; exact hk)
    have h4 : ¬ (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j = 1 := fun h =>
      hnotI j hj (by rw [h]; exact hone)
    have ha1 := hnotI 1 hone
    rw [mul_one] at ha1
    have h5 : ¬ ((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1 = k := fun h =>
      ha1 (by rw [h]; exact hk)
    have h6 : ¬ ((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1 = 1 := fun h =>
      ha1 (by rw [h]; exact hone)
    have h2 : ¬ (1 : ZMod (modulus n)) = k := fun h => hk1 h.symm
    simp only [hj1, h2, h3, h4, h5, h6, ite_false, ite_true]
    split_ifs <;> norm_num
  · have hev : Even (((j.val : ℕ) : ℤ) - 1) := (hjodd j hj).sub_odd odd_one
    rw [hgram _ 1 0 _ hev, hz _ _ (hjodd j hj) Even.zero, hz _ _ (hjodd j hj) hhalfeven,
      hz _ _ odd_one Even.zero, hz _ _ odd_one hhalfeven, hz _ _ (haodd.mul (hjodd j hj)) Even.zero,
      hz _ _ (haodd.mul (hjodd j hj)) hhalfeven, hz _ _ (haodd.mul odd_one) Even.zero,
      hz _ _ (haodd.mul odd_one) hhalfeven]
    norm_num
  · have hev : Even (((j.val : ℕ) : ℤ) - 1) := (hjodd j hj).sub_odd odd_one
    have h2l : Even (2 * (l : ℤ)) := even_two_mul _
    rw [hgram _ 1 0 _ hev, hz _ _ (hjodd j hj) Even.zero, hz _ _ (hjodd j hj) h2l,
      hz _ _ odd_one Even.zero, hz _ _ odd_one h2l, hz _ _ (haodd.mul (hjodd j hj)) Even.zero,
      hz _ _ (haodd.mul (hjodd j hj)) h2l, hz _ _ (haodd.mul odd_one) Even.zero,
      hz _ _ (haodd.mul odd_one) h2l]
    norm_num

end CFSG.Semidihedral.FieldFactorOne
