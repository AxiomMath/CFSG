module

public import CFSG.CharacterTheory.Semidihedral.Principal.RotationSectionColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicMultiplicity

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Open

variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}

@[expose] noncomputable def principalCyclicProjection (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (r : G) (h : Subgroup.zpowers r → ℂ) (g : G) : ℂ :=
  ∑ χ ∈ B, characterPairing (fun x : Subgroup.zpowers r => (basis.representation χ).character x)
    h * (basis.representation χ).character g

theorem principalCyclicProjection_eq_sum (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (r : G) (h : Subgroup.zpowers r → ℂ) (g : G) :
    principalCyclicProjection basis B r h g =
      (Nat.card (Subgroup.zpowers r) : ℂ)⁻¹ * ∑ x : Subgroup.zpowers r, h x⁻¹ *
        ∑ χ ∈ B, (basis.representation χ).character x * (basis.representation χ).character g := by
  unfold principalCyclicProjection characterPairing
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun χ _ => ?_
  ring

theorem twist_sq_modEq (hn : 4 ≤ n) :
    (((modulus n / 2 : ℕ) : ℤ) - 1) * (((modulus n / 2 : ℕ) : ℤ) - 1) ≡ 1 [ZMOD modulus n] := by
  have hM : modulus n = 4 * 2 ^ (n - 3) := by
    unfold modulus
    rw [show n - 1 = 2 + (n - 3) by omega, pow_add]
    norm_num
  rw [hM, Int.modEq_iff_dvd]
  have h2 : (4 * 2 ^ (n - 3)) / 2 = 2 * 2 ^ (n - 3) := by omega
  rw [h2]
  push_cast
  refine ⟨1 - 2 ^ (n - 3), by ring⟩

theorem principal_value_of_section (hn : 4 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {v : ℤ}
    (hv0 : ¬ v ≡ 0 [ZMOD modulus n]) (hv1 : ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n])
    {g a c : G} (hacg : a * c = g) (hac : Commute a c) (hc : Odd (orderOf c))
    (hconj : IsConj a ((e (r n) : G) ^ v)) {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    (basis.representation χ).character g =
      (basis.representation χ).character ((e (r n) : G) ^ v) := by
  obtain ⟨k, hk⟩ := isConj_iff.mp hconj
  have hconst := (noncentral_rotation_principal_section_columns hn e basis ideal principal
    hprincipal).1 v hv0 hv1 χ hχ (k * c * k⁻¹) (by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
      calc k * c * k⁻¹ * (k * a * k⁻¹) = k * (c * a) * k⁻¹ := by group
        _ = k * (a * c) * k⁻¹ := by rw [hac.eq]
        _ = k * a * k⁻¹ * (k * c * k⁻¹) := by group) (by
      have hord : orderOf (k * c * k⁻¹) = orderOf c :=
        orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective c
      rw [hord]; exact hc)
  rw [← hconst, ← hk, ← hacg]
  rw [show k * a * k⁻¹ * (k * c * k⁻¹) = k * (a * c) * k⁻¹ by group]
  exact (Representation.char_conj _ _ _).symm

theorem noncentral_neg {n : ℕ} (hn : 4 ≤ n) {v : ℤ} (hv0 : ¬ v ≡ 0 [ZMOD modulus n])
    (hv1 : ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ¬ -v ≡ 0 [ZMOD modulus n] ∧ ¬ -v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
  have hM : (modulus n : ℤ) = 2 * ((modulus n / 2 : ℕ) : ℤ) := by
    have : 2 ∣ modulus n := by
      unfold modulus
      exact dvd_pow_self 2 (by omega)
    omega
  refine ⟨fun h => hv0 ?_, fun h => hv1 ?_⟩
  · have := h.neg; simpa using this
  · rw [Int.modEq_iff_dvd] at h ⊢
    obtain ⟨k, hk⟩ := h
    exact ⟨-k + 1, by rw [hM] at hk ⊢; linarith⟩

theorem twist_modEq_iff {M a v w : ℤ} (hsq : a * a ≡ 1 [ZMOD M]) :
    -v ≡ a * w [ZMOD M] ↔ w ≡ -(a * v) [ZMOD M] := by
  constructor
  · intro h
    have h1 := h.mul_left a
    have h2 : a * (a * w) ≡ w [ZMOD M] := by
      have := hsq.mul_right w
      rwa [one_mul, mul_assoc] at this
    have h3 : w ≡ a * -v [ZMOD M] := (h1.trans h2).symm
    rwa [show a * -v = -(a * v) by ring] at h3
  · intro h
    have h1 := h.mul_left a
    have h2 : a * -(a * v) ≡ -v [ZMOD M] := by
      have := (hsq.mul_right v).neg
      rw [show a * -(a * v) = -(a * a * v) by ring]
      simpa using this
    exact (h1.trans h2).symm

theorem principal_rotation_column_pair (hn : 4 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {v w : ℤ}
    (hv0 : ¬ v ≡ 0 [ZMOD modulus n]) (hv1 : ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n])
    (hw0 : ¬ w ≡ 0 [ZMOD modulus n]) (hw1 : ¬ w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character ((e (r n) : G) ^ w) *
          (basis.representation χ).character ((e (r n) : G) ^ v) =
      if (e (r n) : G) ^ w = (e (r n) : G) ^ (-v) ∨
          (e (r n) : G) ^ w = (e (r n) : G) ^ (-((((modulus n / 2 : ℕ) : ℤ) - 1) * v))
      then (modulus n : ℂ) else 0 := by
  obtain ⟨hnv0, hnv1⟩ := noncentral_neg hn hv0 hv1
  have hgram := (noncentral_rotation_principal_section_columns hn e basis ideal principal
    hprincipal).2.1 w (-v) hw0 hw1 hnv0 hnv1
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

theorem principalCyclicProjection_eq_zero_of_columns (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) {h : Subgroup.zpowers (e (r n) : G) → ℂ} (h1 : h 1 = 0)
    (ht : h ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0) {g : G}
    (hcol : ∀ w : ℤ, ¬ w ≡ 0 [ZMOD modulus n] → ¬ w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∑ χ ∈ B, (basis.representation χ).character ((e (r n) : G) ^ w) *
        (basis.representation χ).character g = 0) :
    principalCyclicProjection basis B (e (r n) : G) h g = 0 := by
  rw [principalCyclicProjection_eq_sum]
  apply mul_eq_zero_of_right
  refine Finset.sum_eq_zero fun x _ => ?_
  obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.mp x.2
  by_cases hw0 : w ≡ 0 [ZMOD modulus n]
  · have hx : x = 1 := by
      apply Subtype.ext
      rw [← hw, Subgroup.coe_one, ← zpow_zero (e (r n) : G),
        suppliedRotation_zpow_eq_iff (by omega) e]
      exact hw0
    rw [hx, inv_one, h1, zero_mul]
  by_cases hw1 : w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]
  · have hx : x = ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ := by
      apply Subtype.ext
      show (x : G) = (e (r n) : G) ^ (modulus n / 2)
      rw [← hw, ← zpow_natCast, suppliedRotation_zpow_eq_iff (by omega) e]
      exact hw1
    have hxinv : x⁻¹ = x := by
      rw [hx]
      apply Subtype.ext
      rw [Subgroup.coe_inv, inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul,
        show 2 * (modulus n / 2) = modulus n by
          unfold modulus; rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; omega,
        ← suppliedRotation_orderOf (by omega) e, pow_orderOf_eq_one]
    rw [hxinv, hx, ht, zero_mul]
  · rw [← hw]
    rw [hcol w hw0 hw1, mul_zero]

theorem principalCyclicProjection_section_value (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    {f : Subgroup.zpowers (e (r n) : G) → ℂ} (h1 : f 1 = 0)
    (ht : f ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0) {v : ℤ}
    (hv0 : ¬ v ≡ 0 [ZMOD modulus n]) (hv1 : ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n])
    {g a c : G} (hacg : a * c = g) (hac : Commute a c) (hc : Odd (orderOf c))
    (hconj : IsConj a ((e (r n) : G) ^ v)) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        principal) (e (r n) : G) f g =
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
  have hval : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character g =
        (basis.representation χ).character ((e (r n) : G) ^ v) :=
    fun χ hχ => principal_value_of_section hn e basis ideal principal hprincipal hv0 hv1 hacg hac
      hc hconj hχ
  have hterm : ∀ x : Subgroup.zpowers (e (r n) : G), f x⁻¹ *
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character x * (basis.representation χ).character g =
      if x = p₁ ∨ x = p₂ then (modulus n : ℂ) * f x⁻¹ else 0 := by
    intro x
    rw [Finset.sum_congr rfl fun χ hχ => by rw [hval χ hχ]]
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
    · show f _ * ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character ((e (r n) : G) ^ w) *
            (basis.representation χ).character ((e (r n) : G) ^ v) = _
      rw [principal_rotation_column_pair hn e basis ideal principal hprincipal hv0 hv1 hw0 hw1]
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

theorem characterPairing_linear_combination {H : Type*} [Group H] [Fintype H] (F : H → ℂ)
    (s : Finset ℤ) (c : ℤ → ℂ) (lam : ℤ → H → ℂ) :
    characterPairing F (fun x => ∑ j ∈ s, c j * lam j x) =
      ∑ j ∈ s, c j * characterPairing F (lam j) := by
  unfold characterPairing
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem principalCyclicProjection_eq_zero_of_inv_columns (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) {f : Subgroup.zpowers (e (r n) : G) → ℂ} (h1 : f 1 = 0)
    (ht : f ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0) {g : G}
    (hcol : ∀ w : ℤ, ¬ w ≡ 0 [ZMOD modulus n] → ¬ w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∑ χ ∈ B, (basis.representation χ).character ((e (r n) : G) ^ w) *
        starRingEnd ℂ ((basis.representation χ).character g⁻¹) = 0) :
    principalCyclicProjection basis B (e (r n) : G) f g = 0 := by
  refine principalCyclicProjection_eq_zero_of_columns hn e basis B h1 ht fun w hw0 hw1 => ?_
  rw [← hcol w hw0 hw1]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [finite_character_conjugate_inverse, inv_inv]

theorem cyclic_principal_Fourier_exact_section_support (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (c : ℤ → ℤ)
    (f : Subgroup.zpowers (e (r n) : G) → ℂ)
    (hf : ∀ x, f x = ∑ j ∈ Finset.Ico (0 : ℤ) (modulus n),
      (c j : ℂ) * cyclicLinearCharacter (e (r n) : G) (modulus n) j x)
    (h1 : f 1 = 0)
    (ht : f ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0) :
    (∃ k : basis.index → ℤ, ∀ χ, characterPairing
        (fun x : Subgroup.zpowers (e (r n) : G) => (basis.representation χ).character x) f =
          k χ) ∧
    (∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] → ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∀ g a c' : G, a * c' = g → Commute a c' → (∃ k : ℕ, orderOf a = 2 ^ k) →
        Odd (orderOf c') → IsConj a ((e (r n) : G) ^ v) →
        principalCyclicProjection basis (coefficientBlock basis
            (localizedComplexIntegerRing ideal) principal) (e (r n) : G) f g =
          f ⟨(e (r n) : G) ^ v, Subgroup.zpow_mem_zpowers _ _⟩ +
            f ⟨(e (r n) : G) ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * v),
              Subgroup.zpow_mem_zpowers _ _⟩) ∧
    (∀ g : G, (∀ a c' : G, a * c' = g → Commute a c' → (∃ k : ℕ, orderOf a = 2 ^ k) →
        Odd (orderOf c') → ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] →
          ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] → ¬ IsConj a ((e (r n) : G) ^ v)) →
      principalCyclicProjection basis (coefficientBlock basis
          (localizedComplexIntegerRing ideal) principal) (e (r n) : G) f g = 0) ∧
    (∀ g : G, Odd (orderOf g) →
      principalCyclicProjection basis (coefficientBlock basis
          (localizedComplexIntegerRing ideal) principal) (e (r n) : G) f g = 0) ∧
    (∀ g a c' : G, a * c' = g → Commute a c' → orderOf a = 2 → Odd (orderOf c') →
      principalCyclicProjection basis (coefficientBlock basis
          (localizedComplexIntegerRing ideal) principal) (e (r n) : G) f g = 0) := by
  have hcols := noncentral_rotation_principal_section_columns hn e basis ideal principal hprincipal
  have hord := suppliedRotation_orderOf (by omega) e
  have hM : 0 < modulus n := by unfold modulus; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    have hpair : ∀ χ j, ∃ m : ℕ, characterPairing
        (fun x : Subgroup.zpowers (e (r n) : G) => (basis.representation χ).character x)
        (cyclicLinearCharacter (e (r n) : G) (modulus n) j) = m := by
      intro χ j
      rw [characterPairing_zpowers_cyclicLinearCharacter _ hord j]
      exact cyclicMultiplicity_natural (basis.representation χ) _ hM
        (by rw [← hord]; exact pow_orderOf_eq_one _) j
    choose m hm using hpair
    refine ⟨fun χ => ∑ j ∈ Finset.Ico (0 : ℤ) (modulus n), c j * m χ j, fun χ => ?_⟩
    have hfun : f = fun x => ∑ j ∈ Finset.Ico (0 : ℤ) (modulus n),
        (c j : ℂ) * cyclicLinearCharacter (e (r n) : G) (modulus n) j x := funext hf
    rw [hfun, characterPairing_linear_combination]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [hm χ j]
  ·
    intro v hv0 hv1 g a c' hacg hac _ hc hconj
    exact principalCyclicProjection_section_value hn e basis ideal principal hprincipal h1 ht hv0
      hv1 hacg hac hc hconj
  ·
    intro g hg
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ h1 ht fun w hw0 hw1 => ?_
    refine hcols.2.2.1 w hw0 hw1 g⁻¹ fun a c' hacg hac ha hc hconj => ?_
    obtain ⟨hnw0, hnw1⟩ := noncentral_neg hn hw0 hw1
    refine hg a⁻¹ c'⁻¹ ?_ hac.inv_inv ?_ (by rw [orderOf_inv]; exact hc) (-w) hnw0 hnw1 ?_
    · rw [← mul_inv_rev, ← hac.eq, hacg, inv_inv]
    · rw [orderOf_inv]; exact ha
    · obtain ⟨k, hk⟩ := isConj_iff.mp hconj
      refine isConj_iff.mpr ⟨k, ?_⟩
      rw [zpow_neg, ← hk]
      group
  ·
    intro g hg
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ h1 ht fun w hw0 hw1 => ?_
    exact hcols.2.2.2.1 w hw0 hw1 g⁻¹ (by rw [orderOf_inv]; exact hg)
  ·
    intro g a c' hacg hac ha hc
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ h1 ht fun w hw0 hw1 => ?_
    refine hcols.2.2.2.2 w hw0 hw1 g⁻¹ a⁻¹ c'⁻¹ ?_ hac.inv_inv (by rw [orderOf_inv]; exact ha)
      (by rw [orderOf_inv]; exact hc)
    rw [← mul_inv_rev, ← hac.eq, hacg]

theorem cyclicRoot_zpow_half (hn : 4 ≤ n) :
    cyclicRoot (modulus n) ^ (((modulus n / 2 : ℕ) : ℤ)) = -1 := by
  have hM : 0 < modulus n := by unfold modulus; positivity
  have hev : Even (modulus n) := by
    unfold modulus
    exact (Nat.even_pow' (by omega)).mpr even_two
  rw [zpow_natCast]
  exact cyclicRoot_pow_half hM hev

theorem cyclicLinearCharacter_one {G : Type*} [Group G] {g : G} {M : ℕ} (hg : orderOf g = M)
    (j : ℤ) : cyclicLinearCharacter g M j 1 = 1 := by
  have h := cyclicLinearCharacter_zpow hg j 0
  have h1 : (⟨g ^ (0 : ℤ), Subgroup.zpow_mem_zpowers g 0⟩ : Subgroup.zpowers g) = 1 :=
    Subtype.ext (zpow_zero g)
  rw [h1, mul_zero, zpow_zero] at h
  exact h

theorem cyclic_principal_Fourier_projection_values (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := (e (r n) : G)
    let M : ℕ := modulus n
    let a : ℤ := ((M / 2 : ℕ) : ℤ) - 1
    let ζ : ℂ := cyclicRoot M
    let Θ := principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
    let E := fun l : ℕ => principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
    let F := fun j : ℤ => principalCyclicProjection basis B ρ
      (fun x => cyclicLinearCharacter ρ M j x - cyclicLinearCharacter ρ M 1 x)
    (∀ v : ℤ, ¬ v ≡ 0 [ZMOD M] → ¬ v ≡ (M / 2 : ℕ) [ZMOD M] →
      ∀ y ∈ Subgroup.centralizer {ρ ^ v}, Odd (orderOf y) →
        Θ (ρ ^ v * y) = 2 - 2 * (-1 : ℂ) ^ v ∧
        (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
          E l (ρ ^ v * y) = 2 - ζ ^ (2 * (l : ℤ) * v) - ζ ^ (-(2 * (l : ℤ) * v))) ∧
        (∀ j : ℤ, Odd j → F j (ρ ^ v * y) = ζ ^ (j * v) + ζ ^ (a * j * v) - ζ ^ v - ζ ^ (a * v))) ∧
    (∀ g : G, Odd (orderOf g) →
      Θ g = 0 ∧ (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l g = 0) ∧ (∀ j : ℤ, Odd j → F j g = 0)) ∧
    (∀ g x c : G, x * c = g → Commute x c → orderOf x = 2 → Odd (orderOf c) →
      Θ g = 0 ∧ (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l g = 0) ∧
        (∀ j : ℤ, Odd j → F j g = 0)) := by
  intro B ρ M a ζ Θ E F
  have hord : orderOf ρ = M := suppliedRotation_orderOf (by omega) e
  have hM : 0 < M := by unfold M modulus; positivity
  have hM4 : (M : ℤ) = 4 * ((M / 4 : ℕ) : ℤ) := by
    have h4 : 4 ∣ M := by
      have := Nat.pow_dvd_pow 2 (show 2 ≤ n - 1 by omega)
      simpa [M, modulus] using this
    omega
  have hM2 : (M : ℤ) = 2 * ((M / 2 : ℕ) : ℤ) := by omega
  have hhalf : ζ ^ (((M / 2 : ℕ) : ℤ)) = -1 := cyclicRoot_zpow_half hn
  have hlam : ∀ j k : ℤ, cyclicLinearCharacter ρ M j ⟨ρ ^ k, Subgroup.zpow_mem_zpowers _ _⟩ =
      ζ ^ (j * k) := fun j k => cyclicLinearCharacter_zpow hord j k
  have hlam1 : ∀ j : ℤ, cyclicLinearCharacter ρ M j 1 = 1 := fun j =>
    cyclicLinearCharacter_one hord j
  have hlamt : ∀ j : ℤ, cyclicLinearCharacter ρ M j
      ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = (-1 : ℂ) ^ j := by
    intro j
    have h := hlam j ((M / 2 : ℕ) : ℤ)
    rw [show (⟨ρ ^ (((M / 2 : ℕ) : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩ :
        Subgroup.zpowers ρ) = ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ from
        Subtype.ext (zpow_natCast _ _)] at h
    rw [h, mul_comm, zpow_mul, hhalf]
  have hΘ1 : (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
      (1 : Subgroup.zpowers ρ) = 0 := by simp only [hlam1, sub_self]
  have hΘt : (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
      ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := by
    simp only [hlamt]
    rw [show (((M / 2 : ℕ) : ℤ)) = 2 * ((M / 4 : ℕ) : ℤ) by omega, zpow_mul]
    norm_num
  have hE1 : ∀ l : ℕ, (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
      (1 : Subgroup.zpowers ρ) = 0 := fun l => by simp only [hlam1, sub_self]
  have hEt : ∀ l : ℕ, (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
      ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := fun l => by
    simp only [hlamt]
    rw [zpow_mul]
    norm_num
  have hF1 : ∀ j : ℤ, (fun x => cyclicLinearCharacter ρ M j x - cyclicLinearCharacter ρ M 1 x)
      (1 : Subgroup.zpowers ρ) = 0 := fun j => by simp only [hlam1, sub_self]
  have hFt : ∀ j : ℤ, Odd j → (fun x => cyclicLinearCharacter ρ M j x -
      cyclicLinearCharacter ρ M 1 x) ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := by
    intro j hj
    simp only [hlamt]
    rw [hj.neg_one_zpow]
    norm_num
  have hvalue : ∀ (f : Subgroup.zpowers ρ → ℂ), f 1 = 0 →
      f ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 →
      ∀ v : ℤ, ¬ v ≡ 0 [ZMOD M] → ¬ v ≡ (M / 2 : ℕ) [ZMOD M] →
      ∀ y ∈ Subgroup.centralizer {ρ ^ v}, Odd (orderOf y) →
        principalCyclicProjection basis B ρ f (ρ ^ v * y) =
          f ⟨ρ ^ v, Subgroup.zpow_mem_zpowers _ _⟩ +
            f ⟨ρ ^ (a * v), Subgroup.zpow_mem_zpowers _ _⟩ := by
    intro f hf1 hft v hv0 hv1 y hy hyodd
    exact principalCyclicProjection_section_value hn e basis ideal principal hprincipal hf1 hft
      hv0 hv1 rfl (Subgroup.mem_centralizer_singleton_iff.mp hy).symm hyodd (IsConj.refl _)
  have hsupp := fun (f : Subgroup.zpowers ρ → ℂ) (c : ℤ → ℤ) hf hf1 hft =>
    cyclic_principal_Fourier_exact_section_support hn e basis ideal principal hprincipal c f hf
      hf1 hft
  have hodd : ∀ (f : Subgroup.zpowers ρ → ℂ), f 1 = 0 →
      f ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 → ∀ g : G, Odd (orderOf g) →
        principalCyclicProjection basis B ρ f g = 0 := by
    intro f hf1 hft g hg
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ hf1 hft
      fun w hw0 hw1 => ?_
    exact (noncentral_rotation_principal_section_columns hn e basis ideal principal
      hprincipal).2.2.2.1 w hw0 hw1 g⁻¹ (by rw [orderOf_inv]; exact hg)
  have hinvol : ∀ (f : Subgroup.zpowers ρ → ℂ), f 1 = 0 →
      f ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 →
      ∀ g x c : G, x * c = g → Commute x c → orderOf x = 2 → Odd (orderOf c) →
        principalCyclicProjection basis B ρ f g = 0 := by
    intro f hf1 hft g x c hxcg hxc hx hc
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ hf1 hft
      fun w hw0 hw1 => ?_
    refine (noncentral_rotation_principal_section_columns hn e basis ideal principal
      hprincipal).2.2.2.2 w hw0 hw1 g⁻¹ x⁻¹ c⁻¹ ?_ hxc.inv_inv (by rw [orderOf_inv]; exact hx)
      (by rw [orderOf_inv]; exact hc)
    rw [← mul_inv_rev, ← hxc.eq, hxcg]
  clear hsupp
  refine ⟨fun v hv0 hv1 y hy hyodd => ⟨?_, fun l _ _ => ?_, fun j hj => ?_⟩,
    fun g hg => ⟨hodd _ hΘ1 hΘt g hg, fun l _ _ => hodd _ (hE1 l) (hEt l) g hg,
      fun j hj => hodd _ (hF1 j) (hFt j hj) g hg⟩,
    fun g x c hxcg hxc hx hc => ⟨hinvol _ hΘ1 hΘt g x c hxcg hxc hx hc,
      fun l _ _ => hinvol _ (hE1 l) (hEt l) g x c hxcg hxc hx hc,
      fun j hj => hinvol _ (hF1 j) (hFt j hj) g x c hxcg hxc hx hc⟩⟩
  ·
    show principalCyclicProjection basis B ρ _ _ = _
    rw [hvalue _ hΘ1 hΘt v hv0 hv1 y hy hyodd]
    simp only [hlam]
    have ha_odd : Odd a := by
      refine ⟨((M / 4 : ℕ) : ℤ) - 1, ?_⟩
      unfold a; omega
    rw [zpow_mul, hhalf, zpow_mul ζ, hhalf, zpow_mul (-1 : ℂ) a v, ha_odd.neg_one_zpow]
    ring
  ·
    show principalCyclicProjection basis B ρ _ _ = _
    rw [hvalue _ (hE1 l) (hEt l) v hv0 hv1 y hy hyodd]
    simp only [hlam]
    have hcong : 2 * (l : ℤ) * (a * v) ≡ -(2 * (l : ℤ) * v) [ZMOD M] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-(l : ℤ) * v, by unfold a; rw [hM2]; ring⟩
    rw [cyclicRoot_zpow_congr hcong]
    ring
  ·
    show principalCyclicProjection basis B ρ _ _ = _
    rw [hvalue _ (hF1 j) (hFt j hj) v hv0 hv1 y hy hyodd]
    simp only [hlam]
    rw [show j * (a * v) = a * j * v by ring, show (1 : ℤ) * v = v by ring,
      show (1 : ℤ) * (a * v) = a * v by ring]
    ring

end CFSG.Semidihedral.Principal
