module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneColumns
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneRotationColumns
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneFourier
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerExhaustionSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes
open CFSG.Semidihedral.Principal

structure TypeStarTableHyp {L : Type*} (k : ℕ) (B : Finset L) (deg : L → ℤ)
    (Θ : L → ℤ) (E F : ℕ → L → ℤ) (U V : L → ℤ) : Prop where
  hdeg : ∀ x ∈ B, 0 < deg x
  hΘΘ : ∑ x ∈ B, Θ x * Θ x = 4
  hΘE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, Θ x * E l x = 2
  hEE : ∀ l ∈ Finset.Icc 1 (k - 1), ∀ l' ∈ Finset.Icc 1 (k - 1),
    ∑ x ∈ B, E l x * E l' x = 2 + if l = l' then 1 else 0
  hΘF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, Θ x * F j x = 0
  hEF : ∀ l ∈ Finset.Icc 1 (k - 1), ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, E l x * F j x = 0
  hFF : ∀ j ∈ Finset.Icc 1 (k - 1), ∀ j' ∈ Finset.Icc 1 (k - 1),
    ∑ x ∈ B, F j x * F j' x = 1 + if j = j' then 1 else 0
  hUU : ∑ x ∈ B, U x * U x = 8
  hUV : ∑ x ∈ B, U x * V x = -4
  hVV : ∑ x ∈ B, V x * V x = 2 * k + 2
  hUΘ : ∑ x ∈ B, U x * Θ x = 0
  hVΘ : ∑ x ∈ B, V x * Θ x = 0
  hUE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, U x * E l x = 0
  hVE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, V x * E l x = 0
  hUF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, U x * F j x = 0
  hVF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, V x * F j x = 0
  hdegΘ : ∑ x ∈ B, deg x * Θ x = 0
  hdegE : ∀ l ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, deg x * E l x = 0
  hdegF : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ x ∈ B, deg x * F j x = 0
  hdegU : ∑ x ∈ B, deg x * U x = 0
  hdegV : ∑ x ∈ B, deg x * V x = 0
  hcong : ∀ x ∈ B, (2 * k : ℤ) ∣ U x + 2 * V x + Θ x +
    2 * ∑ l ∈ Finset.Icc 1 (k - 1), E l x + 2 * ∑ j ∈ Finset.Icc 1 (k - 1), F j x

variable {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}
  (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

omit [Fintype G] in
theorem odd_factor_eq_one_of_two_element {g a c : G} (hg : ∃ m : ℕ, orderOf g = 2 ^ m)
    (hac : a * c = g) (hcomm : Commute a c) (ha : ∃ k : ℕ, orderOf a = 2 ^ k)
    (hc : Odd (orderOf c)) : c = 1 := by
  obtain ⟨m, hm⟩ := hg
  obtain ⟨k, hk⟩ := ha
  have hcg : c = a⁻¹ * g := by rw [← hac]; group
  have hag : Commute a⁻¹ g := by
    rw [← hac]
    exact (Commute.refl a).inv_left.mul_right hcomm.inv_left
  have hdvd : orderOf c ∣ 2 ^ (k + m) := by
    rw [hcg]
    refine hag.orderOf_mul_dvd_mul_orderOf.trans ?_
    rw [orderOf_inv, hk, hm, pow_add]
  have hcop : Nat.Coprime (orderOf c) (2 ^ (k + m)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hc)
  have h1 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  exact orderOf_eq_one_iff.mp h1

omit [Fintype G] in
theorem rotation_two_part_not_conj_t (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    {v : ℤ} (hv0 : ¬ v ≡ 0 [ZMOD modulus n]) (hv1 : ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∀ a c : G, a * c = (fS (r n) : G) ^ v → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
      ¬ 2 ∣ orderOf c → ¬ IsConj a t := by
  intro a c hac hcomm ha hc hconj
  have hg : ∃ m : ℕ, orderOf ((fS (r n) : G) ^ v) = 2 ^ m := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (suppliedRotation_zpow_orderOf_dvd (by omega) fS v)
    exact ⟨m, hm⟩
  have hc1 := odd_factor_eq_one_of_two_element hg hac hcomm ha
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hc))
  rw [hc1, mul_one] at hac
  rw [hac] at hconj
  have h2 : orderOf ((fS (r n) : G) ^ v) = 2 := by
    rw [conjugate_orderOf_eq hconj, orderOf_t fS hn ht]
  apply noncentralRotation_sq_ne_one (by omega) fS v hv0 hv1
  have h3 := pow_orderOf_eq_one ((fS (r n) : G) ^ v)
  rwa [h2] at h3

omit [Fintype G] in
theorem one_two_part_not_conj_t (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    ∀ a c : G, a * c = 1 → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
      ¬ 2 ∣ orderOf c → ¬ IsConj a t := by
  intro a c hac hcomm ha hc hconj
  have hc1 := odd_factor_eq_one_of_two_element ⟨0, by rw [orderOf_one, pow_zero]⟩ hac hcomm ha
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hc))
  rw [hc1, mul_one] at hac
  rw [hac, isConj_one_right] at hconj
  have := orderOf_t fS hn ht
  rw [hconj, orderOf_one] at this
  exact absurd this (by norm_num)

theorem sum_mul_multiplicity_diff_eq_zero (hn : 4 ≤ n)
    (basis : FiniteIrreducibleCharacterBasis G) (B : Finset basis.index) (W : basis.index → ℂ)
    (hW : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] → ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∑ χ ∈ B, W χ * (basis.representation χ).character ((fS (r n) : G) ^ v) = 0)
    (p q : ℤ) (hpq : Even (p - q)) :
    ∑ χ ∈ B, W χ * ((multiplicityColumn basis (fS (r n) : G) (modulus n) p χ -
      multiplicityColumn basis (fS (r n) : G) (modulus n) q χ : ℤ) : ℂ) = 0 := by
  have hM : 0 < modulus n := by unfold modulus; positivity
  have hord := suppliedRotation_orderOf (by omega) fS
  have hr : (fS (r n) : G) ^ modulus n = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  set ζ := cyclicRoot (modulus n) with hζ
  have hexp : ∀ χ, ((multiplicityColumn basis (fS (r n) : G) (modulus n) p χ -
      multiplicityColumn basis (fS (r n) : G) (modulus n) q χ : ℤ) : ℂ) =
      (modulus n : ℂ)⁻¹ * ∑ v ∈ Finset.range (modulus n),
        (basis.representation χ).character ((fS (r n) : G) ^ v) *
          (ζ ^ (-(p * v)) - ζ ^ (-(q * v))) := by
    intro χ
    rw [Int.cast_sub, multiplicityColumn_cast basis hM hr, multiplicityColumn_cast basis hM hr,
      cyclicMultiplicity, cyclicMultiplicity, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun v hv => ?_
  by_cases hv0 : (v : ℤ) ≡ 0 [ZMOD modulus n]
  · have hz : ∀ j : ℤ, ζ ^ (-(j * (v : ℤ))) = 1 := fun j => by
      obtain ⟨m, hm⟩ := (Int.modEq_zero_iff_dvd.mp hv0)
      rw [hm, show -(j * ((modulus n : ℤ) * m)) = (modulus n : ℤ) * (-(j * m)) by ring, zpow_mul,
        zpow_natCast, hζ, cyclicRoot_pow_self, one_zpow]
    refine Finset.sum_eq_zero fun χ _ => ?_
    rw [hz, hz, sub_self, mul_zero, mul_zero, mul_zero]
  by_cases hv1 : (v : ℤ) ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]
  · have hz : ζ ^ (-(p * (v : ℤ))) = ζ ^ (-(q * (v : ℤ))) := by
      obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hv1.symm
      have hv' : (v : ℤ) = ((modulus n / 2 : ℕ) : ℤ) + (modulus n : ℤ) * m := by linarith
      obtain ⟨c, hc⟩ := hpq
      have hp' : p = q + 2 * c := by linarith
      rw [hp', hv']
      have hhalf : (ζ ^ (((modulus n / 2 : ℕ) : ℤ))) = -1 := by
        rw [zpow_natCast, hζ, cyclicRoot_pow_half hM (by
          unfold modulus; exact (Nat.even_pow' (by omega)).mpr even_two)]
      have hfull : ζ ^ ((modulus n : ℤ)) = 1 := by rw [zpow_natCast, hζ, cyclicRoot_pow_self]
      have hz0 : ζ ≠ 0 := cyclicRoot_ne_zero _
      have key : ζ ^ (-((q + 2 * c) * (((modulus n / 2 : ℕ) : ℤ) + (modulus n : ℤ) * m))) =
          ζ ^ (-(q * (((modulus n / 2 : ℕ) : ℤ) + (modulus n : ℤ) * m))) *
            ((ζ ^ (((modulus n / 2 : ℕ) : ℤ))) ^ (-(2 * c)) *
              (ζ ^ ((modulus n : ℤ))) ^ (-(2 * c * m))) := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hz0, ← zpow_add₀ hz0]
        congr 1
        ring
      rw [key, hhalf, hfull, one_zpow, mul_one, show (-(2 * c) : ℤ) = 2 * (-c) by ring, zpow_mul]
      norm_num
    refine Finset.sum_eq_zero fun χ _ => ?_
    rw [hz, sub_self, mul_zero, mul_zero, mul_zero]
  · have h := hW v hv0 hv1
    have hrw : ∑ χ ∈ B, W χ * ((modulus n : ℂ)⁻¹ *
        ((basis.representation χ).character ((fS (r n) : G) ^ v) *
          (ζ ^ (-(p * v)) - ζ ^ (-(q * v))))) =
        (modulus n : ℂ)⁻¹ * (ζ ^ (-(p * v)) - ζ ^ (-(q * v))) *
          ∑ χ ∈ B, W χ * (basis.representation χ).character ((fS (r n) : G) ^ (v : ℤ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [zpow_natCast]
      ring
    rw [hrw, h, mul_zero]

theorem typeStar_table_hyp (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (θ : C t →* ℂˣ) (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (normalizerBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (lambdaLabel : normalizerBasis.index)
    (hlambda : ∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
      (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
        (x : G) = q * c → (normalizerBasis.representation lambdaLabel).character x =
          thetaG t θ (c : G))
    (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B) :
    ∃ (e : ℤ) (φ : Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ)
      (U V : basis.index → ℤ) (I : Finset (ZMod (modulus n))) (o : ℕ → ZMod (modulus n)),
      (p ^ f % 4 = 1 → e = 1) ∧ (p ^ f % 4 = 3 → e = -1) ∧ (e = 1 ∨ e = -1) ∧
      φ 1 = ((p ^ f : ℕ) : ℂ) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
          (basis.representation χ).character (t * y) =
            ((U χ : ℂ) + V χ * (1 + e * φ y)) * thetaG t θ (y : G)) ∧
      IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I ∧
      o 0 = 1 ∧ Set.InjOn o (Finset.range (2 ^ (n - 3))) ∧
      (∀ i ∈ Finset.range (2 ^ (n - 3)), o i ∈ I) ∧
      (∀ x ∈ I, ∃ i ∈ Finset.range (2 ^ (n - 3)), o i = x) ∧
      TypeStarTableHyp (2 ^ (n - 3)) (coefficientBlock basis (localizedComplexIntegerRing ideal) B)
        (fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ))
        (fun χ => multiplicityColumn basis (fS (r n) : G) (modulus n) 0 χ -
          multiplicityColumn basis (fS (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) χ)
        (fun l χ => multiplicityColumn basis (fS (r n) : G) (modulus n) 0 χ -
          multiplicityColumn basis (fS (r n) : G) (modulus n) (2 * (l : ℤ)) χ)
        (fun j χ => multiplicityColumn basis (fS (r n) : G) (modulus n) ((o j).val : ℤ) χ -
          multiplicityColumn basis (fS (r n) : G) (modulus n) 1 χ) U V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, φ, U, V, he1, he3, he, hφ1, hval, hUU, hUV, hVV, horth⟩ :=
    typeStar_involution_columns fS hn ht hindex hnonab hcentral hnc p f hp hpodd hf hmodel θ hθS
      hθT basis ideal normalizerBasis lambdaLabel hlambda B hB
  have hcols : RotationColumns fS basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) B) :=
    typeStar_rotation_columns fS hn ht hindex θ hθS hθT basis ideal normalizerBasis lambdaLabel
      hlambda B hB
  set Bs := coefficientBlock basis (localizedComplexIntegerRing ideal) B with hBs
  obtain ⟨hM4, hKeven, hK2, hhalf⟩ := modulus_eq_four_mul hn
  set k : ℕ := 2 ^ (n - 3) with hk
  obtain ⟨I, hI⟩ := exists_isOddResidueTransversal (n := n) hn
  have hIk : I.card = k := (sum_range_odd_transversal_columns hM4 hKeven hK2 (fun _ => 0)
    (fun _ _ _ => rfl) (fun _ => rfl) _ (supplied_twist_val hn) I hI.odd hI.pair).2
  obtain ⟨o, ho0, hoinj, homem, hosurj⟩ := exists_enum_of_card I hIk hI.one_mem
  refine ⟨e, φ, U, V, I, o, he1, he3, he, hφ1, hval, hI, ho0, hoinj, homem, hosurj, ?_⟩
  set L := multiplicityColumn basis (fS (r n) : G) (modulus n) with hL
  have hquarter : modulus n / 4 = k := by omega
  have hχ1 : ∀ χ : basis.index, (basis.representation χ).character 1 =
      (((Module.finrank ℂ (basis.representation χ).vector : ℤ)) : ℂ) := fun χ => by
    rw [(basis_character_one basis χ).1, Int.cast_natCast]
  have hoI : ∀ j ∈ Finset.Icc 1 (k - 1), o j ∈ I := fun j hj =>
    homem j (Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hj).2; omega))
  have hone : ∀ j ∈ Finset.Icc 1 (k - 1), o j ≠ 1 := fun j hj h => by
    have h0 : j = 0 := hoinj (Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hj).2; omega))
      (Finset.mem_range.mpr (by omega)) (h.trans ho0.symm)
    have := (Finset.mem_Icc.mp hj).1
    omega
  have hoeq : ∀ j ∈ Finset.Icc 1 (k - 1), ∀ j' ∈ Finset.Icc 1 (k - 1), o j = o j' ↔ j = j' :=
    fun j hj j' hj' => ⟨fun h => hoinj
      (Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hj).2; omega))
      (Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hj').2; omega)) h,
      fun h => by rw [h]⟩
  have hoodd : ∀ j ∈ Finset.Icc 1 (k - 1), Even (((o j).val : ℤ) - 1) := fun j hj =>
    (show Odd (((o j).val : ℕ) : ℤ) by exact_mod_cast hI.odd _ (hoI j hj)).sub_odd odd_one
  obtain ⟨gΘΘ, gΘE, gEE⟩ := even_family_coefficient_gram_of fS basis Bs hn hcols
  obtain ⟨gFF, gFΘ, gFE⟩ := odd_family_coefficient_gram_of fS basis Bs hn hcols hI
  have hrot : ∀ W : basis.index → ℤ, (∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] →
      ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∑ χ ∈ Bs, (W χ : ℂ) * (basis.representation χ).character ((fS (r n) : G) ^ v) = 0) →
      ∀ a b : ℤ, Even (a - b) → ∑ χ ∈ Bs, W χ * (L a χ - L b χ) = 0 := by
    intro W hW a b hab
    have h := sum_mul_multiplicity_diff_eq_zero fS hn basis Bs (fun χ => (W χ : ℂ)) hW a b hab
    exact_mod_cast h
  have hUVrot : ∀ W : basis.index → ℤ, (∀ g : G, (∀ a c : G, a * c = g → Commute a c →
      (∃ k : ℕ, orderOf a = 2 ^ k) → ¬ 2 ∣ orderOf c → ¬ IsConj a t) →
      ∑ χ ∈ Bs, (W χ : ℂ) * starRingEnd ℂ ((basis.representation χ).character g) = 0) →
      ∀ a b : ℤ, Even (a - b) → ∑ χ ∈ Bs, W χ * (L a χ - L b χ) = 0 := by
    intro W hW
    refine hrot W fun v hv0 hv1 => ?_
    obtain ⟨hnv0, hnv1⟩ := noncentral_neg hn hv0 hv1
    rw [← hW _ (rotation_two_part_not_conj_t fS hn ht hnv0 hnv1)]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [finite_character_conjugate_inverse, zpow_neg, inv_inv]
  have hUrot := hUVrot U fun g hg => (horth g hg).1
  have hVrot := hUVrot V fun g hg => (horth g hg).2
  have hdrot := hrot (fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ))
    fun v hv0 hv1 => by
      rw [← hcols.2 v hv0 hv1 1 (not_isConj_rotation_of_sq_eq_one fS hn (one_pow 2) hv0 hv1)]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [hχ1, Int.cast_natCast, map_natCast, mul_comm]
  have hdUV := horth 1 (one_two_part_not_conj_t fS hn ht)
  have hdW : ∀ W : basis.index → ℤ, ∑ χ ∈ Bs, (W χ : ℂ) *
      starRingEnd ℂ ((basis.representation χ).character 1) = 0 →
      ∑ χ ∈ Bs, (Module.finrank ℂ (basis.representation χ).vector : ℤ) * W χ = 0 := by
    intro W h
    simp only [hχ1, Int.cast_natCast, map_natCast] at h
    have h' : ((∑ χ ∈ Bs, (Module.finrank ℂ (basis.representation χ).vector : ℤ) * W χ : ℤ) :
        ℂ) = 0 := by
      rw [← h]
      push_cast
      exact Finset.sum_congr rfl fun χ _ => by ring
    exact_mod_cast h'
  have hdU := hdW U hdUV.1
  have hdV := hdW V hdUV.2
  obtain ⟨-, -, -, -, -, hcongr⟩ :=
    cyclic_multiplicity_central_involution_congruence hn S fS basis Bs I hI
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S fS hindex t
    (orderOf_t fS hn ht) hnonab hcentral hnc p f hp hpodd hf hmodel
  have h2part : 2 ^ padicValNat 2 ((p ^ f) ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, Nat.factorization_def _ Nat.prime_two] at h
    rw [h]
    rfl
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨m, hm⟩ := hpodd
      omega
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have htr : (fS (r n) : G) ^ (modulus n / 2) = t := by
    rw [ht, show modulus n / 2 = 2 ^ (n - 2) by omega]
  have hXt : ∀ χ ∈ Bs, (basis.representation χ).character ((fS (r n) : G) ^ (modulus n / 2)) =
      ((U χ + (1 + e * ((p ^ f : ℕ) : ℤ)) * V χ : ℤ) : ℂ) := fun χ hχ => by
    have h := hval χ hχ 1 (by rw [orderOf_one]; exact odd_one)
    rw [OneMemClass.coe_one, mul_one, hφ1, thetaG_of_mem θ (Subgroup.one_mem _)] at h
    rw [htr, h]
    have h1 : θ ⟨1, Subgroup.one_mem _⟩ = 1 := map_one θ
    rw [h1, Units.val_one, mul_one]
    push_cast
    ring
  have hcong0 := hcongr (p ^ f) e U V hq3 hqodd h2part he1 he3 hXt
  have hIimage : (Finset.range k).image o = I := by
    ext x
    simp only [Finset.mem_image]
    exact ⟨fun ⟨i, hi, hix⟩ => hix ▸ homem i hi, fun hx => hosurj x hx⟩
  have hrange : Finset.range k = insert 0 (Finset.Icc 1 (k - 1)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0Icc : (0 : ℕ) ∉ Finset.Icc 1 (k - 1) := by simp
  have hval1 : (1 : ZMod (modulus n)).val = 1 := by
    have : Fact (1 < modulus n) := ⟨by omega⟩
    exact ZMod.val_one _
  refine
    { hdeg := fun χ _ => by exact_mod_cast (basis_character_one basis χ).2
      hΘΘ := gΘΘ
      hΘE := fun l hl => gΘE l (Finset.mem_Icc.mp hl).1 (by
        rw [hquarter]; exact (Finset.mem_Icc.mp hl).2)
      hEE := fun l hl l' hl' => gEE l l' (Finset.mem_Icc.mp hl).1
        (by rw [hquarter]; exact (Finset.mem_Icc.mp hl).2) (Finset.mem_Icc.mp hl').1
        (by rw [hquarter]; exact (Finset.mem_Icc.mp hl').2)
      hΘF := fun j hj =>
        (Finset.sum_congr rfl fun χ _ => mul_comm _ _).trans (gFΘ (o j) (hoI j hj))
      hEF := fun l _ j hj =>
        (Finset.sum_congr rfl fun χ _ => mul_comm _ _).trans (gFE (o j) (hoI j hj) l)
      hFF := fun j hj j' hj' => by
        rw [gFF (o j) (hoI j hj) (o j') (hoI j' hj') (hone j hj) (hone j' hj')]
        simp only [hoeq j hj j' hj']
      hUU := hUU
      hUV := hUV
      hVV := by
        rw [hVV]
        have h : (2 : ℤ) ^ (n - 2) = 2 * (k : ℤ) := by exact_mod_cast hhalf
        rw [h]
      hUΘ := hUrot 0 _ ⟨-(k : ℤ), by omega⟩
      hVΘ := hVrot 0 _ ⟨-(k : ℤ), by omega⟩
      hUE := fun l _ => hUrot 0 _ ⟨-(l : ℤ), by ring⟩
      hVE := fun l _ => hVrot 0 _ ⟨-(l : ℤ), by ring⟩
      hUF := fun j hj => hUrot _ 1 (hoodd j hj)
      hVF := fun j hj => hVrot _ 1 (hoodd j hj)
      hdegΘ := hdrot 0 _ ⟨-(k : ℤ), by omega⟩
      hdegE := fun l _ => hdrot 0 _ ⟨-(l : ℤ), by ring⟩
      hdegF := fun j hj => hdrot _ 1 (hoodd j hj)
      hdegU := hdU
      hdegV := hdV
      hcong := fun χ hχ => by
        have h := hcong0 χ hχ
        rw [hquarter, ← hIimage, Finset.sum_image fun x hx y hy hxy => hoinj hx hy hxy, hrange,
          Finset.sum_insert h0Icc, ho0] at h
        simp only [Pi.sub_apply, hval1, Nat.cast_one, sub_self, zero_add] at h
        have h' := Int.modEq_zero_iff_dvd.mp h
        rw [show ((modulus n / 2 : ℕ) : ℤ) = 2 * (k : ℤ) by omega] at h' ⊢
        exact h' }

end CFSG.Semidihedral.FieldFactorOne
