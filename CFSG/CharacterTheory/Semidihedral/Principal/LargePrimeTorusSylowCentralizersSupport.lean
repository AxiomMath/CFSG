module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionPrincipalColumnSum
public import CFSG.CharacterTheory.Semidihedral.Principal.SignedDegreeNumerics
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneTorusNormalizer

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

namespace LargePrimeTorus

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.GorensteinWalter

theorem card_fixed_eq_mod_of_prime_power_order {F : Type} [Field F] [Finite F] {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) {σ : Equiv.Perm (Omega F)} (hσG : σ ∈ coordinateG F)
    (hσ1 : σ ≠ 1) {b : ℕ} (hσℓ : σ ^ ℓ ^ b = 1) :
    Nat.card {x : Omega F // σ x = x} = (Nat.card F + 1) % ℓ := by
  have hle : Nat.card {x : Omega F // σ x = x} ≤ 2 := by
    rw [← coordinatePSLAction_range_eq_G] at hσG
    obtain ⟨g, rfl⟩ := hσG
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hσ1 (map_one _)
    let cE : Omega F ≃ PSL2ProjectiveLine F :=
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F
    have he : {x : Omega F // coordinatePSLAction F g x = x} ≃
        {y : PSL2ProjectiveLine F // g • y = y} :=
      cE.subtypeEquiv (fun x => by
        rw [← coordinatePSLAction_point]
        exact cE.injective.eq_iff.symm)
    rw [Nat.card_congr he]
    exact psl2_fixedPoint_card_le_two F g hg1
  have hp : IsPGroup ℓ (Subgroup.zpowers σ) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hℓ.out).mp (orderOf_dvd_of_pow_eq_one hσℓ)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hmod := hp.card_modEq_card_fixedPoints (Omega F)
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) (Omega F)) =
      Nat.card {x : Omega F // σ x = x} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · rintro h ⟨τ, hτ⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h k
  rw [hfix, Finite.card_option] at hmod
  have hmod' : (Nat.card F + 1) % ℓ = Nat.card {x : Omega F // σ x = x} % ℓ := hmod
  rw [hmod', Nat.mod_eq_of_lt (by omega)]

theorem card_fixed_layer_element_eq_mod_of_pow {Γ : Type*} [Group Γ] {L : Subgroup Γ}
    {F : Type} [Field F] [Finite F] (ρ : Γ →* coordinateE F) (hρ : Function.Injective ρ)
    (hL : L.map ρ = specialLayer F) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) {γ : Γ} (hγL : γ ∈ L)
    (hγ1 : γ ≠ 1) {b : ℕ} (hγℓ : γ ^ ℓ ^ b = 1) :
    Nat.card {x : Omega F // ((ρ γ : coordinateE F) : Equiv.Perm (Omega F)) x = x} =
      (Nat.card F + 1) % ℓ := by
  have hmem : ρ γ ∈ specialLayer F := hL ▸ Subgroup.mem_map_of_mem ρ hγL
  have hG : ((ρ γ : coordinateE F) : Equiv.Perm (Omega F)) ∈ coordinateG F := hmem
  refine card_fixed_eq_mod_of_prime_power_order hℓ3 hG ?_ (b := b) ?_
  · intro h
    apply hγ1
    apply hρ
    rw [map_one]
    exact Subtype.ext h
  · rw [← Subgroup.coe_pow, ← map_pow, hγℓ, map_one, Subgroup.coe_one]

theorem succ_mod_eq_one_sub_of_dvd {q ℓ : ℕ} {e : ℤ} (he : e = 1 ∨ e = -1) (hℓ3 : 3 ≤ ℓ)
    (h : (ℓ : ℤ) ∣ q + e) : (((q + 1) % ℓ : ℕ) : ℤ) = 1 - e := by
  obtain ⟨k, hk⟩ := h
  rcases he with rfl | rfl
  · have hk' : ((q + 1 : ℕ) : ℤ) = ℓ * k := by push_cast; linarith
    have hdvd : ℓ ∣ q + 1 := by
      have : (ℓ : ℤ) ∣ ((q + 1 : ℕ) : ℤ) := ⟨k, hk'⟩
      exact_mod_cast this
    rw [Nat.mod_eq_zero_of_dvd hdvd]
    norm_num
  · have hq1 : 1 ≤ q := by
      by_contra h0
      have hq0 : q = 0 := by omega
      subst hq0
      have h1 : (ℓ : ℤ) * k = -1 := by push_cast at hk; linarith
      have hℓ' : (3 : ℤ) ≤ ℓ := by exact_mod_cast hℓ3
      rcases le_or_gt 0 k with hk0 | hk0 <;> nlinarith
    have hdvd : ℓ ∣ q - 1 := by
      have : (ℓ : ℤ) ∣ ((q - 1 : ℕ) : ℤ) := ⟨k, by push_cast [Nat.cast_sub hq1]; linarith⟩
      exact_mod_cast this
    obtain ⟨j, hj⟩ := hdvd
    have hq : q + 1 = 2 + ℓ * j := by omega
    rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    norm_num

open CFSG.LyonsUnitaryFour in
theorem extendedCentralizer_inv {G : Type*} [Group G] (x : G) :
    extendedCentralizer x⁻¹ = extendedCentralizer x := by
  ext g
  rw [mem_extendedCentralizer, mem_extendedCentralizer]
  have h : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
  rw [h, inv_inj, inv_inv, inv_eq_iff_eq_inv]

open CFSG.LyonsUnitaryFour in
theorem extendedCentralizer_le_normalizer_zpowers {G : Type*} [Group G] (x : G) :
    extendedCentralizer x ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  intro g hg
  have hy : Subgroup.zpowers (g⁻¹ * x * g) = Subgroup.zpowers x := by
    rcases (mem_extendedCentralizer x g).mp hg with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]
  have hconj : ∀ k : ℤ, (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
    intro k
    have h := conj_zpow (i := k) (a := g⁻¹) (b := x)
    rwa [inv_inv] at h
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hy]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hconj k⟩
  · intro hh
    rw [← hy] at hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [hconj k] at hk
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa using hk

theorem map_eq_one_of_coprime {X Y : Type*} [Group X] [Group Y] [Finite Y] (f : X →* Y)
    {ℓ v : ℕ} (hℓ : ℓ.Prime) (hY : Nat.card Y = ℓ ^ v) {j : X} (hj : Nat.Coprime ℓ (orderOf j)) :
    f j = 1 := by
  have h1 : orderOf (f j) ∣ orderOf j := orderOf_map_dvd f j
  have h2 : orderOf (f j) ∣ ℓ ^ v := hY ▸ orderOf_dvd_natCard (f j)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hℓ).mp h2
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    have hdvd : ℓ ∣ orderOf j := (dvd_pow_self ℓ (Nat.succ_ne_zero k)).trans (hk ▸ h1)
    exact hℓ.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hj hdvd)

theorem nonempty_equiv_alternating_five_of_model {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 5 1) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨iso⟩⟩ := h
  obtain ⟨⟨e5⟩, -⟩ := CFSG.LinearGroups.five_field_linear_two_alternating_five_model F
    (by rw [hcard]; norm_num)
  exact ⟨iso.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans e5)⟩

theorem card_eq_of_not_dvd_card_normalizer {G : Type*} [Group G] [Finite G] {ℓ v : ℕ}
    [hℓ : Fact ℓ.Prime] (P : Subgroup G) (hP : Nat.card P = ℓ ^ v)
    (hN : ¬ ℓ ^ (v + 1) ∣ Nat.card (Subgroup.normalizer (P : Set G))) :
    Nat.card P = ℓ ^ (Nat.card G).factorization ℓ := by
  have hdvd : ¬ ℓ ^ (v + 1) ∣ Nat.card G := fun h =>
    hN (Sylow.prime_pow_dvd_card_normalizer h hP)
  have hle : ℓ ^ v ∣ Nat.card G := hP ▸ Subgroup.card_subgroup_dvd_card P
  have h1 := (hℓ.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hle
  have h2 : ¬ v + 1 ≤ (Nat.card G).factorization ℓ := fun h =>
    hdvd ((hℓ.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr h)
  rw [hP]
  congr 1
  omega

theorem column_bracket_eq {F x δ : ℂ} (hδ : δ = 1 ∨ δ = -1) (hF : F ≠ 0) (hFδ : F + δ ≠ 0) :
    1 + δ * x ^ 2 / F - δ * (x + δ) ^ 2 / (F + δ) = (F - x) ^ 2 / (F * (F + δ)) := by
  field_simp
  rcases hδ with rfl | rfl <;> ring

theorem generator_coefficient_eq {G : Type*} [Group G] [Fintype G] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (W : Sylow ℓ G) [IsCyclic (W : Subgroup G)] (a : ℕ) (hWcard : Nat.card W = ℓ ^ a)
    (lam : (W : Subgroup G) →* ℂˣ) (hlam : orderOf lam = ℓ) (F : ↥(W : Subgroup G) → ℂ)
    (c₀ : ℂ) (hF : ∀ w : (W : Subgroup G), Subgroup.zpowers (w : G) = W → F w = c₀) :
    ((ℓ : ℂ) ^ a)⁻¹ * ∑ w : (W : Subgroup G), F w * (1 - starRingEnd ℂ (lam w : ℂ)) = c₀ := by
  have hlamℓ : lam ^ ℓ = 1 := by
    have h := pow_orderOf_eq_one lam
    rwa [hlam] at h
  have hlam1 : lam ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hlam
    exact hℓ.out.one_lt.ne hlam
  have hterm : ∀ w : (W : Subgroup G), F w * (1 - starRingEnd ℂ (lam w : ℂ)) =
      c₀ * (1 - starRingEnd ℂ (lam w : ℂ)) := by
    intro w
    by_cases hw : lam w = 1
    · rw [hw, Units.val_one, map_one, sub_self, mul_zero, mul_zero]
    · rw [hF w (CyclicInversion.zpowers_eq_of_ne_one W a hWcard lam hlamℓ w hw)]
  rw [Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← map_sum, CyclicInversion.sum_linear_character W a hWcard lam, ite_eq_right hlam1, map_zero,
    sub_zero, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hWcard]
  have hne : (ℓ : ℂ) ^ a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
  simp only [nsmul_eq_mul, mul_one]
  push_cast
  field_simp

open CFSG.LyonsUnitaryFour CFSG.TwoRankLowerBound.Helpers in
theorem global_local_column_identity {G : Type} [Group G] [Fintype G] {t : G} (ht : t * t = 1)
    (H K : Subgroup G) (hKH : K ≤ H) (K' : Subgroup H) (hK' : ∀ x : H, x ∈ K' ↔ (x : G) ∈ K)
    (ψ : K → ℂ) (ψ' : K' → ℂ) (hψ : ∀ k : K', ψ' k = ψ ⟨((k : H) : G), (hK' k).mp k.2⟩)
    (hsupp : ∀ k : K, ψ k ≠ 0 → extendedCentralizer (k : G) ≤ H)
    (basis : FiniteIrreducibleCharacterBasis G) (localBasis : FiniteIrreducibleCharacterBasis H) :
    (Nat.card G : ℂ) * ∑ α, characterPairing (inducedFunction K ψ)
        (basis.representation α).character *
        ((basis.representation α).character t * (basis.representation α).character t /
          (basis.representation α).character 1) =
      (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 * (Nat.card H : ℂ) *
        ∑ β, characterPairing (inducedFunction K' ψ') (localBasis.representation β).character *
          (classWeight H (localBasis.representation β).character t *
            classWeight H (localBasis.representation β).character t /
              (localBasis.representation β).character 1) := by
  set c : ℂ := (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) with hc
  have hfrobG : ∀ α : basis.index, characterPairing (inducedFunction K ψ)
      (basis.representation α).character =
      (Nat.card K : ℂ)⁻¹ * ∑ k : K, ψ k * (basis.representation α).character ((k : G)⁻¹) := by
    intro α
    rw [characterPairing_inducedFunction_left K ψ _ (fun x g => by
      simp only [FiniteComplexRepresentation.character, Representation.char_conj])]
    rfl
  have hfrobH : ∀ β : localBasis.index, characterPairing (inducedFunction K' ψ')
      (localBasis.representation β).character =
      (Nat.card K' : ℂ)⁻¹ * ∑ k : K', ψ' k *
        (localBasis.representation β).character ((k : H)⁻¹) := by
    intro β
    rw [characterPairing_inducedFunction_left K' ψ' _ (fun x g => by
      simp only [FiniteComplexRepresentation.character, Representation.char_conj])]
    rfl
  have hprodG : ∀ x : G, (Nat.card G : ℂ) * ∑ α, (basis.representation α).character t *
      (basis.representation α).character t * (basis.representation α).character x /
        (basis.representation α).character 1 =
      c * c * (productCount (conjClassFinset t) (conjClassFinset t) x : ℂ) := fun x =>
    (involution_classes_product_character_formula basis t t ht ht x).symm
  have hprodH : ∀ y : H, (Nat.card H : ℂ) * ∑ β,
      classWeight H (localBasis.representation β).character t *
        classWeight H (localBasis.representation β).character t *
          (localBasis.representation β).character y / (localBasis.representation β).character 1 =
      (productCount (classInter H t) (classInter H t) y : ℂ) := fun y =>
    (productCount_classInter H localBasis ht ht y).symm
  have hL : (Nat.card G : ℂ) * ∑ α, characterPairing (inducedFunction K ψ)
        (basis.representation α).character *
        ((basis.representation α).character t * (basis.representation α).character t /
          (basis.representation α).character 1) =
      (Nat.card K : ℂ)⁻¹ * ∑ k : K, ψ k *
        (c * c * (productCount (conjClassFinset t) (conjClassFinset t) (k : G)⁻¹ : ℂ)) := by
    simp_rw [hfrobG, ← hprodG]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun α _ => ?_
    ring
  have hR : (Nat.card H : ℂ) * ∑ β, characterPairing (inducedFunction K' ψ')
        (localBasis.representation β).character *
        (classWeight H (localBasis.representation β).character t *
          classWeight H (localBasis.representation β).character t /
            (localBasis.representation β).character 1) =
      (Nat.card K' : ℂ)⁻¹ * ∑ k : K', ψ' k *
        (productCount (classInter H t) (classInter H t) (k : H)⁻¹ : ℂ) := by
    simp_rw [hfrobH, ← hprodH]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  let ι : K' ≃ K :=
    { toFun := fun k => ⟨((k : H) : G), (hK' k).mp k.2⟩
      invFun := fun k => ⟨⟨k, hKH k.2⟩, (hK' _).mpr k.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Nat.card K' = Nat.card K := Nat.card_congr ι
  have hsum : ∑ k : K', ψ' k * (productCount (classInter H t) (classInter H t) (k : H)⁻¹ : ℂ) =
      ∑ k : K, ψ k * (productCount (conjClassFinset t) (conjClassFinset t) (k : G)⁻¹ : ℂ) := by
    refine Fintype.sum_equiv ι _ _ fun k => ?_
    rw [hψ k]
    change ψ (ι k) * _ = ψ (ι k) * _
    by_cases h0 : ψ (ι k) = 0
    · rw [h0, zero_mul, zero_mul]
    · congr 2
      have hE : extendedCentralizer (((k : H)⁻¹ : H) : G) ≤ H := by
        change extendedCentralizer ((ι k : G)⁻¹) ≤ H
        rw [extendedCentralizer_inv]
        exact hsupp _ h0
      exact (productCount_conjClassFinset_eq H ht ht _ hE).symm
  rw [hL, mul_assoc, hR, hsum, hcard, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem order_column_cancel {Gc c d X Y Y' Z A m q : ℚ} (hX : X ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hq : q ≠ 0) (hG : Gc = c ^ 3 / d ^ 2 * (Y / X ^ 2) * (Z / q))
    (h3 : 3 * Gc * X ^ 2 = A * m * c ^ 2 * Y') :
    3 * c * Y * Z = A * m * d ^ 2 * q * Y' := by
  subst hG
  have h : c ^ 2 * (3 * c * Y * Z - A * m * d ^ 2 * q * Y') = 0 := by
    have h' : 3 * (c ^ 3 / d ^ 2 * (Y / X ^ 2) * (Z / q)) * X ^ 2 * (d ^ 2 * q) =
        A * m * c ^ 2 * Y' * (d ^ 2 * q) := by rw [h3]
    have hl : 3 * (c ^ 3 / d ^ 2 * (Y / X ^ 2) * (Z / q)) * X ^ 2 * (d ^ 2 * q) =
        3 * c ^ 3 * Y * Z := by
      field_simp
    rw [hl] at h'
    linear_combination h'
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0) hc
  · linarith

theorem order_column_int {Gc c m : ℕ} {X Y Y' Z A q e : ℤ} (hX : X ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0)
    (hq : q ≠ 0)
    (hG : (Gc : ℚ) = (c : ℚ) ^ 3 / ((4 * m : ℕ) : ℚ) ^ 2 * ((Y : ℚ) / (X : ℚ) ^ 2) * ((Z : ℚ) / q))
    (h3 : 3 * (Gc : ℤ) * X ^ 2 = A * m * (c : ℤ) ^ 2 * Y') (hm2 : 2 * (m : ℤ) = q + e) :
    3 * (c : ℤ) * Y * Z = A * m * (2 * (q + e)) ^ 2 * q * Y' := by
  have h3Q : 3 * (Gc : ℚ) * (X : ℚ) ^ 2 = (A : ℚ) * (m : ℚ) * (c : ℚ) ^ 2 * (Y' : ℚ) := by
    exact_mod_cast h3
  have h := order_column_cancel (Int.cast_ne_zero.mpr hX) (Nat.cast_ne_zero.mpr hc)
    (Nat.cast_ne_zero.mpr (by omega : 4 * m ≠ 0)) (Int.cast_ne_zero.mpr hq) hG h3Q
  have h' : 3 * (c : ℤ) * Y * Z = A * m * ((4 * m : ℕ) : ℤ) ^ 2 * q * Y' := by exact_mod_cast h
  rw [h']
  push_cast
  rw [show (4 : ℤ) * m = 2 * (2 * m) by ring, hm2]

theorem chi_two_false {q e A Y m : ℤ} (he : e = 1 ∨ e = -1) (hA : A = 9 ∨ A = 5) (hq : 9 ≤ q)
    (hY : Y ≠ 0) (hm : 2 * m = q + e)
    (h : 3 * (2 * q * (q ^ 2 - 1)) * Y * (q - e) = A * m * (2 * (q + e)) ^ 2 * q * Y) :
    False := by
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have h' : 2 * q * Y * (q + e) * (3 * (q - e) ^ 2 - A * (q + e) ^ 2) = 0 := by
    rcases he with rfl | rfl
    · linear_combination h + 2 * A * q * Y * (q + 1) ^ 2 * hm
    · linear_combination h + 2 * A * q * Y * (q + -1) ^ 2 * hm
  have hne : 2 * q * Y * (q + e) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by omega) hY) (by omega)
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  rcases he with rfl | rfl <;> rcases hA with rfl | rfl <;> nlinarith

theorem chi_one_four_false {q e δ f m : ℤ} (he : e = 1 ∨ e = -1) (hδ : δ = 1 ∨ δ = -1)
    (hq : 9 ≤ q) (hf : 1 < f) (hfodd : Odd f) (hm : 2 * m = q + e)
    (h : 3 * (2 * q * (q ^ 2 - 1)) * (f * (f + δ)) * (q + e) =
      9 * m * (2 * (q + e)) ^ 2 * q * (f * (f - δ))) : False := by
  have hf3 : 3 ≤ f := by
    obtain ⟨k, hk⟩ := hfodd
    omega
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have h' : 6 * q * f * (q + e) ^ 2 * ((q - e) * (f + δ) - 3 * (q + e) * (f - δ)) = 0 := by
    rcases he with rfl | rfl
    · linear_combination h + 18 * q * f * (q + 1) ^ 2 * (f - δ) * hm
    · linear_combination h + 18 * q * f * (q + -1) ^ 2 * (f - δ) * hm
  have hne : 6 * q * f * (q + e) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by omega) (by omega)) (pow_ne_zero _ (by omega))
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> nlinarith

theorem chi_one_five_false {q e δ f m : ℤ} (he : e = 1 ∨ e = -1) (hδ : δ = 1 ∨ δ = -1)
    (hm7 : 7 ≤ m) (hm9 : m ≠ 9) (hf : 1 < f) (hm : 2 * m = q + e)
    (h : 3 * (2 * q * (q ^ 2 - 1)) * (f * (f + δ)) * (q + e) =
      5 * m * (2 * (q + e)) ^ 2 * q * (f * (f - δ))) : False := by
  have hq : 13 ≤ q := by rcases he with rfl | rfl <;> omega
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have h' : 2 * q * f * (q + e) ^ 2 * (3 * (q - e) * (f + δ) - 5 * (q + e) * (f - δ)) = 0 := by
    rcases he with rfl | rfl
    · linear_combination h + 10 * q * f * (q + 1) ^ 2 * (f - δ) * hm
    · linear_combination h + 10 * q * f * (q + -1) ^ 2 * (f - δ) * hm
  have hne : 2 * q * f * (q + e) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by omega) (by omega)) (pow_ne_zero _ (by omega))
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  have hkey : (q + 4 * e) * (f - 4 * δ) = -15 * e * δ := by
    have h2 : 2 * ((q + 4 * e) * (f - 4 * δ) + 15 * e * δ) = 0 := by
      rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> linear_combination -h0
    linarith
  set u := f - 4 * δ with hu
  rcases lt_trichotomy u 0 with hu0 | hu0 | hu0
  · rcases le_or_gt u (-2) with hu2 | hu2
    · rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> nlinarith
    · have hu1 : u = -1 := by omega
      rw [hu1] at hkey
      rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> omega
  · rw [hu0] at hkey
    rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> omega
  · rcases le_or_gt 2 u with hu2 | hu2
    · rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> nlinarith
    · have hu1 : u = 1 := by omega
      rw [hu1] at hkey
      rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> omega

theorem chi_three_false {g c' A m f δ y : ℤ} {n : ℕ} (hn : 4 ≤ n) (hδ : δ = 1 ∨ δ = -1)
    (hA : Odd A) (hm : Odd m) (hc' : Odd c') (hf : Odd f) (hy : f + δ = 2 ^ (n - 1) * y)
    (h : 3 * (2 ^ n * g) * (f + δ) ^ 2 = A * m * (2 ^ n * c') ^ 2 * f * (f - δ)) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h1 : (2 : ℤ) ^ (k + 4 - 1) = 8 * 2 ^ k := by
    rw [show k + 4 - 1 = k + 3 by omega, pow_add]
    ring
  rw [h1] at hy
  have hfd : f - δ = 2 * (4 * 2 ^ k * y - δ) := by linear_combination hy
  rw [hy, hfd] at h
  have h' : (2 : ℤ) ^ k * 2 ^ k * 512 * (6 * 2 ^ k * g * y ^ 2 -
      A * m * c' ^ 2 * f * (4 * 2 ^ k * y - δ)) = 0 := by
    linear_combination h
  have hne : (2 : ℤ) ^ k * 2 ^ k * 512 ≠ 0 := by positivity
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  have hodd : Odd (A * m * c' ^ 2 * f * (4 * 2 ^ k * y - δ)) := by
    have hodd' : Odd (4 * 2 ^ k * y - δ) := by
      rcases hδ with rfl | rfl
      · exact ⟨2 * 2 ^ k * y - 1, by ring⟩
      · exact ⟨2 * 2 ^ k * y, by ring⟩
    exact (((hA.mul hm).mul (hc'.pow)).mul hf).mul hodd'
  have heven : Even (6 * 2 ^ k * g * y ^ 2) := ⟨3 * 2 ^ k * g * y ^ 2, by ring⟩
  rw [sub_eq_zero] at h0
  rw [h0] at heven
  exact (Int.not_even_iff_odd.mpr hodd) heven

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open in
theorem layer_fixed_value_of_prime_power {G : Type} [Group G] [Finite G] {t : G}
    (ht2 : orderOf t = 2) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    {F : Type} [Field F] [Finite F] (ρ : Gamma t →* coordinateE F) (hρ : Function.Injective ρ)
    (hLρ : (CFSG.generalizedFitting (Gamma t)).map ρ = specialLayer F)
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) {e : ℤ} (he : e = 1 ∨ e = -1)
    (hℓq : (ℓ : ℤ) ∣ (Nat.card F : ℤ) + e) (w : C t) {b : ℕ} (hb : 1 ≤ b)
    (hw : orderOf w = ℓ ^ b) :
    (Nat.card {x : Omega F // ((ρ (kappa t w) : coordinateE F) : Equiv.Perm (Omega F)) x = x} :
      ℂ) - 1 = -(e : ℂ) := by
  have hℓodd : Odd ℓ := hℓ.out.odd_of_ne_two (by omega)
  have hwodd : Odd (orderOf w) := by rw [hw]; exact hℓodd.pow
  have hwℓ : w ^ ℓ ^ b = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hwY : w ∈ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) := by
    obtain ⟨k, hk⟩ := hwodd
    have h := Subgroup.sq_mem_of_index_two hY (w ^ (k + 1))
    rwa [← pow_mul, show (k + 1) * 2 = orderOf w + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul] at h
  have hκL : kappa t w ∈ CFSG.generalizedFitting (Gamma t) := by
    rw [Subgroup.mem_comap, Subgroup.mem_comap, barKappa_nu] at hwY
    exact hwY
  have hκ1 : kappa t w ≠ 1 := by
    intro h
    have hmem : w ∈ NZ t := (QuotientGroup.eq_one_iff (N := NZ t) w).mp h
    have hZ : w ∈ Z t := by
      have h' : NZ t = Z t := by
        change N t ⊔ Z t = Z t
        rw [hN, bot_sup_eq]
      rwa [h'] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hZ
    have hw2 : w ^ 2 = 1 := by
      have ht2' : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht2',
        pow_orderOf_eq_one, one_zpow]
    have h2 := orderOf_dvd_of_pow_eq_one hw2
    rw [hw] at h2
    have h3 : ℓ ∣ 2 := (dvd_pow_self ℓ (by omega)).trans h2
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hκℓ : kappa t w ^ ℓ ^ b = 1 := by rw [← map_pow, hwℓ, map_one]
  rw [card_fixed_layer_element_eq_mod_of_pow ρ hρ hLρ hℓ3 hκL hκ1 hκℓ]
  have h := succ_mod_eq_one_sub_of_dvd he hℓ3 hℓq
  have h' : (((Nat.card F + 1) % ℓ : ℕ) : ℂ) = ((1 - e : ℤ) : ℂ) := by rw [← h]; norm_cast
  rw [h']
  push_cast
  ring

open CFSG.TwoRankLowerBound.Helpers in
theorem characterPairing_column_eq {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (ρ τ : basis.index) (δ : ℂ)
    (T : G → ℂ) (hT : ∀ g, T g = 1 + δ * (basis.representation ρ).character g -
      δ * (basis.representation τ).character g) (α : basis.index) :
    characterPairing T (basis.representation α).character =
      (if principal = α then 1 else 0) + δ * (if ρ = α then 1 else 0) -
        δ * (if τ = α then 1 else 0) := by
  have hsplit : characterPairing T (basis.representation α).character =
      characterPairing (basis.representation principal).character
          (basis.representation α).character +
        δ * characterPairing (basis.representation ρ).character
          (basis.representation α).character -
        δ * characterPairing (basis.representation τ).character
          (basis.representation α).character := by
    unfold characterPairing
    rw [hprincipal]
    simp only [hT, Pi.one_apply, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  rw [hsplit]
  simp_rw [characterPairing_irreducible _ _ (basis.irreducible _) (basis.irreducible α),
    basis.distinct.eq_iff]

theorem sum_column_coefficients {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c : ι) (δ : ℂ)
    (g : ι → ℂ) :
    ∑ α, ((if a = α then 1 else 0) + δ * (if b = α then 1 else 0) -
      δ * (if c = α then 1 else 0)) * g α = g a + δ * g b - δ * g c := by
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

open CFSG.LyonsUnitaryFour CFSG.TwoRankLowerBound.Helpers in
theorem inducedFunction_congr {G : Type*} [Group G] [Fintype G] {K₁ K₂ : Subgroup G}
    (h : K₁ = K₂) (f₁ : K₁ → ℂ) (f₂ : K₂ → ℂ)
    (hf : ∀ (x : G) (h₁ : x ∈ K₁) (h₂ : x ∈ K₂), f₁ ⟨x, h₁⟩ = f₂ ⟨x, h₂⟩) :
    inducedFunction K₁ f₁ = inducedFunction K₂ f₂ := by
  subst h
  congr 1
  funext k
  exact hf k k.2 k.2

open CFSG.LyonsUnitaryFour CFSG.TwoRankLowerBound.Helpers in
theorem local_column_sum {G : Type} [Group G] [Fintype G] (W : Subgroup G) [IsCyclic W]
    (hodd : Odd (Nat.card W)) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hinv : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hR : (CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))).map
      (Subgroup.centralizer (W : Set G)).subtype = W)
    (hK : Nonempty ((Subgroup.centralizer (W : Set G) ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))) ≃* alternatingGroup (Fin d)))
    (hdih : ∃ P : Sylow 2 (Subgroup.normalizer (W : Set G)),
      Nonempty ((P : Subgroup (Subgroup.normalizer (W : Set G))) ≃* DihedralGroup 4))
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hℓm : ℓ ∣ Nat.card W)
    (hℓd : ¬ ℓ ∣ Nat.card (alternatingGroup (Fin d)))
    {P : Subgroup G} (hPW : P ≤ W) (hPcard : Nat.card P = ℓ ^ (Nat.card W).factorization ℓ)
    {J : Subgroup G} (hJcop : Nat.Coprime ℓ (Nat.card J))
    (hPJ : P ⊔ J = Subgroup.centralizer (W : Set G))
    (hPJc : ∀ p ∈ P, ∀ j ∈ J, p * j = j * p)
    (lam : P →* ℂˣ) (hlam : orderOf lam = ℓ) (μ : G → ℂ)
    (hμ : ∀ p : P, ∀ j ∈ J, μ ((p : G) * j) = 1 - (lam p : ℂ))
    {t : G} (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (W : Set G))) :
    (Nat.card (Subgroup.normalizer (W : Set G)) : ℂ) * ∑ β, characterPairing
        (inducedFunction ((Subgroup.centralizer (W : Set G)).subgroupOf
          (Subgroup.normalizer (W : Set G)))
          (fun k => μ ((k : Subgroup.normalizer (W : Set G)) : G)))
        (localBasis.representation β).character *
        (classWeight (Subgroup.normalizer (W : Set G)) (localBasis.representation β).character t *
          classWeight (Subgroup.normalizer (W : Set G)) (localBasis.representation β).character t /
            (localBasis.representation β).character 1) =
      if d = 4 then 3 * (Nat.card W : ℂ) else 5 * (Nat.card W : ℂ) / 3 := by
  revert localBasis
  set H := Subgroup.normalizer (W : Set G) with hHdef
  set K := Subgroup.centralizer (W : Set G) with hKdef
  intro localBasis
  have hWH : W ≤ H := Subgroup.le_normalizer
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  set W' : Subgroup H := W.subgroupOf H with hW'def
  have hW'n : W'.Normal := Subgroup.normal_in_normalizer
  have hW'card : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv
  have : IsCyclic W' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWH).symm.surjective
  have hcent : Subgroup.centralizer (W' : Set H) = K.subgroupOf H := by
    ext h
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh w hw
      exact congrArg Subtype.val (hh ⟨w, hWH hw⟩ hw)
    · intro hh w hw
      exact Subtype.ext (hh w hw)
  have hindex' : (Subgroup.centralizer (W' : Set H)).index = 2 := by
    rw [hcent]
    exact hKH
  have hinv' : ∀ h : H, h ∉ Subgroup.centralizer (W' : Set H) → ∀ w ∈ W', h * w * h⁻¹ = w⁻¹ := by
    intro h hh w hw
    rw [hcent, Subgroup.mem_subgroupOf] at hh
    exact Subtype.ext (hinv h h.2 hh w hw)
  let hKsub : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH'
  let φ : Subgroup.centralizer (W' : Set H) ≃* K :=
    (MulEquiv.subgroupCongr hcent).trans hKsub
  have hφval : ∀ x : Subgroup.centralizer (W' : Set H), ((φ x : K) : G) = ((x : H) : G) :=
    fun x => rfl
  have hmapN : (W'.subgroupOf (Subgroup.centralizer (W' : Set H))).map φ.toMonoidHom =
      CFSG.pPrimeCore 2 K := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxW : ((x : H) : G) ∈ W := hx
      rw [← hR] at hxW
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxW
      have : y = φ.toMonoidHom x := Subtype.ext (by
        change (y : G) = ((φ x : K) : G)
        rw [hφval]
        exact hyx)
      rw [← this]
      exact hy
    · intro hk
      refine ⟨φ.symm k, ?_, by simp⟩
      change (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) ∈ W
      have h1 : (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) = (k : G) := by
        rw [← hφval, MulEquiv.apply_symm_apply]
      rw [h1, ← hR]
      exact ⟨k, hk, rfl⟩
  obtain ⟨ψ⟩ := hK
  have hquot : Nonempty (Subgroup.centralizer (W' : Set H) ⧸
      W'.subgroupOf (Subgroup.centralizer (W' : Set H)) ≃* alternatingGroup (Fin d)) :=
    ⟨(QuotientGroup.congr _ _ φ hmapN).trans ψ⟩
  have hPH : P ≤ H := hPW.trans hWH
  set P' : Subgroup H := P.subgroupOf H with hP'def
  have hP'W' : P' ≤ W' := fun x hx => hPW hx
  have hP'card' : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  have hP'card : Nat.card P' = ℓ ^ (Nat.card W').factorization ℓ := by
    rw [hP'card', hW'card, hPcard]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  have hgord : orderOf g = Nat.card W := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : ℓ ^ (Nat.card W).factorization ℓ ∣ Nat.card W := Nat.ordProj_dvd _ _
  set Q : Subgroup G := (Subgroup.zpowers (g ^ ℓ ^ (Nat.card W).factorization ℓ)).map W.subtype
    with hQdef
  have hQW : Q ≤ W := Subgroup.map_subtype_le _
  have hQcard : Nat.card Q * ℓ ^ (Nat.card W).factorization ℓ = Nat.card W := by
    rw [hQdef, Subgroup.card_map_of_injective W.subtype_injective, Nat.card_zpowers,
      orderOf_pow_of_dvd (pow_ne_zero _ hℓ.out.ne_zero) (hgord ▸ hdvd), hgord]
    exact Nat.div_mul_cancel hdvd
  have hQH : Q ≤ H := hQW.trans hWH
  set Q' : Subgroup H := Q.subgroupOf H with hQ'def
  have hQ'W' : Q' ≤ W' := fun x hx => hQW hx
  have hQ'card : Nat.card Q' * ℓ ^ (Nat.card W').factorization ℓ = Nat.card W' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hW'card]
    exact hQcard
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation H)
    (principalFiniteComplexRepresentation_isIrreducible H)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨J', π', -, -, -, -, -, -, -, -, hπP', -, -, hcardin, hcardout, -, -, hcol⟩ :=
    odd_cyclic_A4_A5_inversion_normalizer_principal_sylow_column_sum W' (hW'card ▸ hodd) d hd
      hindex' hinv' hquot hdih ℓ hℓ5 (hW'card ▸ hℓm) hℓd P' Q' hP'W' hP'card hQ'W' hQ'card
      localBasis localPrincipal hlocalPrincipal
  let eP : P' ≃* P := Subgroup.subgroupOfEquivOfLe hPH
  set lam' : P' →* ℂˣ := MulEquiv.monoidHomCongrLeft eP.symm lam with hlam'def
  have hlam'val : ∀ y : P', lam' y = lam (eP y) := fun y => rfl
  have hlam'ord : orderOf lam' = ℓ := by
    rw [hlam'def, MulEquiv.orderOf_eq, hlam]
  obtain ⟨θε, θμ, -, -, -, hfin⟩ := hcol lam' hlam'ord
  obtain ⟨⟨t₀, ht₀C, ht₀2⟩⟩ : Nonempty {u : H // u ∈ Subgroup.centralizer (W' : Set H) ∧
      orderOf u = 2} := by
    have h : 0 < Nat.card {u : H // u ∈ Subgroup.centralizer (W' : Set H) ∧ orderOf u = 2} := by
      rw [hcardin]
      split_ifs <;> norm_num
    exact (Nat.card_pos_iff.mp h).1
  obtain ⟨⟨x₀, hx₀C, hx₀2⟩⟩ : Nonempty {u : H // u ∉ Subgroup.centralizer (W' : Set H) ∧
      orderOf u = 2} := by
    have h : 0 < Nat.card {u : H // u ∉ Subgroup.centralizer (W' : Set H) ∧ orderOf u = 2} := by
      rw [hcardout]
      apply Nat.mul_pos
      · split_ifs <;> norm_num
      · exact Nat.card_pos
    exact (Nat.card_pos_iff.mp h).1
  obtain ⟨-, -, -, -, hsum⟩ := hfin t₀ ht₀C ht₀2 x₀ hx₀C hx₀2
  have hJK : J ≤ K := hPJ ▸ le_sup_right
  have hPK : P ≤ K := hPJ ▸ le_sup_left
  have hPcJ : P ≤ Subgroup.centralizer (J : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hPJc x hx j hj).symm
  have hmemC : ∀ y : H, (y : G) ∈ K → y ∈ Subgroup.centralizer (W' : Set H) := by
    intro y hy
    rw [hcent, Subgroup.mem_subgroupOf]
    exact hy
  have hind : inducedFunction (Subgroup.centralizer (W' : Set H))
      (fun k => 1 - (lam' (π' k) : ℂ)) =
      inducedFunction (K.subgroupOf H) (fun k => μ ((k : H) : G)) := by
    refine inducedFunction_congr hcent _ _ fun x h₁ h₂ => ?_
    have hxK : (x : G) ∈ P ⊔ J := hPJ ▸ (Subgroup.mem_subgroupOf.mp h₂)
    obtain ⟨p, hp, j, hj, hpj⟩ := exists_mul_eq_of_mem_sup_of_le_centralizer hPcJ hxK
    set pC : Subgroup.centralizer (W' : Set H) := ⟨⟨p, hPH hp⟩, hmemC _ (hPK hp)⟩ with hpC
    set jC : Subgroup.centralizer (W' : Set H) := ⟨⟨j, hKH' (hJK hj)⟩, hmemC _ (hJK hj)⟩
      with hjC
    have hx : (⟨x, h₁⟩ : Subgroup.centralizer (W' : Set H)) = pC * jC :=
      Subtype.ext (Subtype.ext hpj.symm)
    have hπp : (π' pC : H) = ⟨p, hPH hp⟩ := hπP' pC hp
    have hπj : π' jC = 1 := by
      refine map_eq_one_of_coprime π' hℓ.out hP'card ?_
      rw [hjC, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard J hj) hJcop
    have hval : eP (π' ⟨x, h₁⟩) = ⟨p, hp⟩ := by
      apply Subtype.ext
      change (((π' ⟨x, h₁⟩ : P') : H) : G) = p
      rw [hx, map_mul, hπj, mul_one, hπp]
    change 1 - (lam (eP (π' ⟨x, h₁⟩)) : ℂ) = μ ((x : H) : G)
    rw [hval, ← hpj]
    exact (hμ ⟨p, hp⟩ j hj).symm
  have hcw : ∀ β : localBasis.index, (Nat.card H : ℂ)⁻¹ *
      ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
        (localBasis.representation β).character u =
      classWeight H (localBasis.representation β).character t := by
    intro β
    rw [classWeight, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : IsConj (x : G) t ↔ orderOf x = 2 := by rw [← hinvol, Subgroup.orderOf_coe]
    by_cases h : orderOf x = 2
    · rw [ite_eq_left (hx.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hx.mp h')), ite_eq_right h]
  rw [hind, hW'card] at hsum
  rw [← hsum]
  refine congrArg _ (Finset.sum_congr rfl fun β _ => ?_)
  rw [hcw β]
  ring

end LargePrimeTorus

namespace LargePrimeTorus

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.LyonsUnitaryFour

theorem map_pPrimeCore_congr {G : Type*} [Group G] {A B : Subgroup G} (h : A = B) :
    (CFSG.pPrimeCore 2 A).map A.subtype = (CFSG.pPrimeCore 2 B).map B.subtype := by
  subst h
  rfl

theorem torus_sylow_centralizer_ne
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (d : ℕ) (hd : d = 4 ∨ d = 5) :
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin d)) →
    Nat.card H = (if d = 4 then 24 else 120) * Nat.card W →
    ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → (d = 5 → 7 ≤ ℓ) → ℓ ∣ Nat.card W →
    ∀ P : Subgroup G, P ≤ W → Nat.card P = ℓ ^ (Nat.card W).factorization ℓ →
      Subgroup.centralizer (P : Set G) = K → Subgroup.normalizer (P : Set G) = H → False := by
  intro s₀ V D W K H hquot hHcard ℓ hℓ hℓ5 hℓ7 hℓW P hPW hPcard hCP hNP
  set q : ℕ := p ^ f with hqdef
  set e : ℤ := if q % 4 = 1 then 1 else -1 with hedef
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨hzt, ht2, hcent, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨hC, hW1, hWcyc, hWodd, hWcard, ⟨hsup, hdisj, -⟩, hcentw, -, -,
      ⟨d₀, -, -, -, -, -, ⟨eD⟩, -, P₀, hP₀⟩, -, -, -, hKH, hinvH, -, -, -, hOK, -, -, -, -, -,
      -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have : IsCyclic W := hWcyc
  have hWodd : Odd (Nat.card W) := hWodd
  have hKH : K.relIndex H = 2 := hKH
  have hinvH : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹ := hinvH
  have hOK : (CFSG.pPrimeCore 2 K).map K.subtype = W := hOK
  have hsup : V ⊔ W = D := hsup
  have hdisj : Disjoint V W := hdisj
  have he : e = 1 ∨ e = -1 := by
    change (if q % 4 = 1 then (1 : ℤ) else -1) = 1 ∨ (if q % 4 = 1 then (1 : ℤ) else -1) = -1
    split_ifs <;> simp
  have hqodd : Odd q := hpodd.pow
  have hqe : (q : ℤ) + e = 2 * Nat.card W := by
    have heven : (2 : ℤ) ∣ (q : ℤ) + e := by
      obtain ⟨k, hk⟩ := hqodd
      have hk' : (q : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      rcases he with h | h
      · exact ⟨k + 1, by rw [h, hk']; ring⟩
      · exact ⟨k, by rw [h, hk']; ring⟩
    have h := Int.ediv_mul_cancel heven
    have hWcard' : (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 := hWcard
    rw [← hWcard'] at h
    linarith
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hDcard, -, hDK, -, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have hWD : W ≤ D := hsup ▸ le_sup_right
  have hWH : W ≤ H := Subgroup.le_normalizer
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hVD : V ≤ D := hsup ▸ le_sup_left
  have htK : t ∈ K := hDK (hVD htV)
  have h24 : ¬ ℓ ∣ 24 := by
    intro h
    have h' : ℓ ∣ 2 ^ 3 * 3 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hℓ).mp h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hℓ.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  have h120 : d = 5 → ¬ ℓ ∣ 120 := by
    intro hd5 h
    have hℓ7' := hℓ7 hd5
    have h' : ℓ ∣ 2 ^ 3 * 3 * 5 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hℓ).mp h' with h23 | h5
    · rcases (Nat.Prime.dvd_mul hℓ).mp h23 with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hℓ.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
    · have := Nat.le_of_dvd (by norm_num) h5
      omega
  have hℓd : ¬ ℓ ∣ Nat.card (alternatingGroup (Fin d)) := by
    rcases hd with rfl | rfl
    · have ha : Nat.card (alternatingGroup (Fin 4)) = 12 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      rw [ha]
      exact fun h => h24 (h.trans (by norm_num))
    · rw [CyclicAlternatingFive.nat_card_alternating]
      exact fun h => h120 rfl (h.trans (by norm_num))
  set v := (Nat.card W).factorization ℓ with hvdef
  have hv1 : 1 ≤ v := (hℓ.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hℓW
  have hHv : ¬ ℓ ^ (v + 1) ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
    rw [hNP, hHcard]
    intro hdvd
    have hcop : Nat.Coprime (ℓ ^ (v + 1)) (if d = 4 then 24 else 120) := by
      apply Nat.Coprime.pow_left
      rcases hd with rfl | rfl
      · exact (Nat.Prime.coprime_iff_not_dvd hℓ).mpr h24
      · exact (Nat.Prime.coprime_iff_not_dvd hℓ).mpr (h120 rfl)
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hℓ (hcop.dvd_of_dvd_mul_left hdvd)
  have hPsyl := card_eq_of_not_dvd_card_normalizer P hPcard hHv
  set PS : Sylow ℓ G := Sylow.ofCard P hPsyl with hPSdef
  have hPS : (PS : Subgroup G) = P := Sylow.coe_ofCard _ _
  have : IsCyclic (PS : Subgroup G) := by
    rw [hPS]
    exact Subgroup.isCyclic_of_le hPW
  have hPScard : Nat.card (PS : Subgroup G) = ℓ ^ v := by rw [hPS, hPcard]
  have hCPS : Subgroup.centralizer (PS : Set G) = K := by
    change Subgroup.centralizer ((PS : Subgroup G) : Set G) = K
    rw [hPS, hCP]
  have hNPS : Subgroup.normalizer (PS : Set G) = H := by
    change Subgroup.normalizer ((PS : Subgroup G) : Set G) = H
    rw [hPS, hNP]
  have hPSidx : (Subgroup.centralizer (PS : Set G)).relIndex
      (Subgroup.normalizer (PS : Set G)) = 2 := by
    rw [hCPS, hNPS]
    exact hKH
  obtain ⟨⟨ideal₂, hmax₂, h2mem⟩, hchar₂⟩ := CFSG.BlockBasics.residue_prime_existence 2
    Nat.prime_two
  have : ideal₂.IsMaximal := hmax₂
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2 := hchar₂ ideal₂ hmax₂ h2mem
  obtain ⟨⟨idealℓ, hmaxℓ, hℓmem⟩, hcharℓ⟩ := CFSG.BlockBasics.residue_prime_existence ℓ hℓ
  have : idealℓ.IsMaximal := hmaxℓ
  have : CharP (ComplexAlgebraicIntegers ⧸ idealℓ) ℓ := hcharℓ idealℓ hmaxℓ hℓmem
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨F, hfield, hfinite, ρF, hFcard, hρF, hLρF, -, hrest⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal₂ basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  obtain ⟨hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ₂, ν₂, hfam, hdeg, -, hOFall⟩ := hrest
  have hOF := hOFall S fS hcent
  have heF : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = e := by rw [hFcard]
  have hq3 : 3 ≤ Nat.card F := by rw [hFcard]; omega
  have hqoddF : Odd (Nat.card F) := by rw [hFcard]; exact hqodd
  have he1 : Nat.card F % 4 = 1 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 :=
    fun h => by simp [h]
  have he3 : Nat.card F % 4 = 3 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 :=
    fun h => by simp [show ¬ Nat.card F % 4 = 1 by omega]
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have hqM : 2 ^ padicValNat 2 (Nat.card F ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, Nat.factorization_def _ Nat.prime_two] at h
    rw [hFcard, h]
    rfl
  obtain ⟨hf₁, hf₂, hf₃, ho₁, ho₂, ho₃, hsigns, hsum2, hprod, -, -⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal₂ principal hprincipal
      localBasis localPrincipal (Nat.card F) hq3 hqoddF hqM _ he1 he3 _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄
      ψ₂ ν₂ hfam hdeg
  obtain ⟨hrot, -, -, -⟩ := actual_principal_rotation_values_and_congruences hG hn ht2 hnonab
    basis ideal₂ principal hprincipal localBasis localPrincipal (Nat.card F) hq3 hqoddF _ he1 he3
    _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ₂ ν₂ hfam hdeg fS hcent
  obtain ⟨-, hδ₁, hδ₂, hδ₃, -, hnd, -, -, -, -, -, hB, -, hodd2, hsec, -⟩ := hfam
  obtain ⟨h₁t, h₂t, h₃t, -⟩ := hsec 1 (by rw [orderOf_one]; decide)
  simp only [OneMemClass.coe_one, mul_one, hφ1] at h₁t h₂t h₃t
  obtain ⟨-, -, hc₃⟩ := perfect_semidihedral_rotation_values_full_sylow_degree_congruences hn
    S fS (fS (r n) : G) t rfl hcent.symm (Nat.card F) hq3 hqoddF hqM _ he1 he3
    (basis.representation χ₁) (basis.representation χ₂) (basis.representation χ₃) δ₁ δ₂ δ₃ hδ₁
    hδ₂ hδ₃ (by rw [h₁t]; push_cast; ring) (by rw [h₂t]; push_cast; ring)
    (by rw [h₃t]; push_cast; ring) (fun v hv0 hv1 => (hrot v hv0 hv1).1)
    (fun v hv0 hv1 => (hrot v hv0 hv1).2.1) (fun v hv0 hv1 => (hrot v hv0 hv1).2.2)
  set f₁ := Module.finrank ℂ (basis.representation χ₁).vector with hf₁def
  set f₂ := Module.finrank ℂ (basis.representation χ₂).vector with hf₂def
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector with hf₃def
  have hM3 : (modulus n : ℤ) ∣ (f₃ : ℤ) + δ₃ := by
    have h := (Int.ModEq.dvd hc₃.symm)
    obtain ⟨k, hk⟩ := h
    exact ⟨2 * k + δ₃, by linear_combination hk⟩
  have hdistinct := signed_degree_product_two_part_congruence_distinct (Nat.card F) f₁ f₂ f₃
    δ₁ δ₂ δ₃ (by omega) hqoddF hf₁ hf₂ hf₃ hsigns hsum2 hprod (by rw [hqM]; exact hM3)
  have hℓ3 : 3 ≤ ℓ := by omega
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two (by omega)
  have hℓq : (ℓ : ℤ) ∣ (Nat.card F : ℤ) + (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) := by
    rw [heF, hFcard]
    rw [show ((p ^ f : ℕ) : ℤ) = (q : ℤ) from rfl, hqe]
    exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hℓW) 2
  have heF' : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 ∨
      (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    rw [heF]
    exact he
  have hee : (e : ℂ) * e = 1 := by
    rcases he with h | h <;> rw [h] <;> norm_num
  have hvalgen : ∀ w ∈ P, Subgroup.zpowers w = P →
      (basis.representation χ₁).character (t * w) = -δ₁ ∧
      (basis.representation χ₂).character (t * w) = δ₂ ∧
      (basis.representation χ₃).character (t * w) = -δ₃ := by
    intro w hwP hgen
    have hwW : w ∈ W := hPW hwP
    have hwt : w * t = t * w := (Subgroup.mem_centralizer_iff.mp (hWD hwW) t htV).symm
    have hwC : w ∈ C t := Subgroup.mem_centralizer_singleton_iff.mpr hwt
    set w' : C t := ⟨w, hwC⟩ with hw'def
    have hword : orderOf w = ℓ ^ v := by rw [← Nat.card_zpowers, hgen, hPcard]
    have hw'o : orderOf w' = ℓ ^ v := by rw [Subgroup.orderOf_mk]; exact hword
    have hw'odd : Odd (orderOf w') := by rw [hw'o]; exact hℓodd.pow
    have hφw := layer_fixed_value_of_prime_power ht2 hN hY ρF hρF hLρF hℓ3 heF' hℓq w' hv1 hw'o
    obtain ⟨h₁w, h₂w, h₃w, -⟩ := hsec w' hw'odd
    beta_reduce at h₁w h₂w
    rw [hφw, heF] at h₁w h₂w
    refine ⟨?_, ?_, h₃w⟩
    · change (basis.representation χ₁).character (t * w) = _ at h₁w
      rw [h₁w]
      linear_combination (-(δ₁ : ℂ)) * hee
    · change (basis.representation χ₂).character (t * w) = _ at h₂w
      rw [h₂w]
      linear_combination (δ₂ : ℂ) * hee
  obtain ⟨localBasisK⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (PS : Set G))
  obtain ⟨localPrincipalK, hlocalPrincipalK⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasisK (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipalK
  obtain ⟨J, π, hJK, -, hJcop, hsupJ, -, hcommJ, -, hπP, hπJ, -, -, -, -, -,
      ⟨lam₁, lam₂, hl₁, hl₂, hl₃, hl₄⟩, hcols⟩ :=
    cyclic_odd_sylow_inversion_normalizer_two_generator_supported_principal_columns ℓ hℓ5 v hv1
      basis idealℓ principal hprincipal PS hPScard hPSidx localBasisK localPrincipalK
      hlocalPrincipalK
  obtain ⟨hlist, -, ρ, τ₁, τ₂, δ, hδ, hρB, -, -, hρ1, hτ₁1, hτ₂1, hρτ₁, -, hτ₁τ₂, hρreal,
      hτ₁real, hτ₂real, hT₁, -, hτ₁deg, hτ₂deg, hpos, hreg⟩ := hcols lam₁ lam₂ hl₁ hl₂ hl₃ hl₄
  obtain ⟨-, -, -, -, hcoef⟩ := hlist lam₁ (by simp)
  have hmem2 : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index),
      c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hrealodd : ∀ θ : basis.index, (∀ g, starRingEnd ℂ ((basis.representation θ).character g) =
      (basis.representation θ).character g) →
      Odd (Module.finrank ℂ (basis.representation θ).vector) → θ ≠ principal →
      θ = χ₁ ∨ θ = χ₂ ∨ θ = χ₃ := by
    intro θ hθr hθo hθp
    have hθB := real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal₂ principal
      hprincipal θ hθr hθo
    rcases (hodd2 θ hθB).mp hθo with h | h
    · exact absurd h hθp
    · exact h
  obtain ⟨hd₁₂, hd₁₃, hd₂₃⟩ := hdistinct
  set Fρ := Module.finrank ℂ (basis.representation ρ).vector with hFρdef
  have hτ₁₂ : Module.finrank ℂ (basis.representation τ₁).vector =
      Module.finrank ℂ (basis.representation τ₂).vector := by
    have h : (Module.finrank ℂ (basis.representation τ₁).vector : ℤ) =
        Module.finrank ℂ (basis.representation τ₂).vector := by rw [hτ₁deg, hτ₂deg]
    exact_mod_cast h
  have hFodd : Odd Fρ := by
    by_contra hFe
    have hFe' : Even Fρ := Nat.not_odd_iff_even.mp hFe
    have hτodd : Odd (Module.finrank ℂ (basis.representation τ₁).vector) := by
      obtain ⟨k, hk⟩ := hFe'
      have h : (Module.finrank ℂ (basis.representation τ₁).vector : ℤ) = 2 * k + δ := by
        rw [hτ₁deg, hk]
        push_cast
        ring
      rcases hδ with rfl | rfl
      · exact ⟨k, by omega⟩
      · exact ⟨k - 1, by omega⟩
    have h1 := hrealodd τ₁ hτ₁real hτodd hτ₁1
    have h2 := hrealodd τ₂ hτ₂real (hτ₁₂ ▸ hτodd) hτ₂1
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rw [h1, h2] at hτ₁₂ <;>
      first
      | exact hτ₁τ₂ (h1.trans h2.symm)
      | exact hd₁₂ (by exact_mod_cast hτ₁₂)
      | exact hd₁₃ (by exact_mod_cast hτ₁₂)
      | exact hd₂₃ (by exact_mod_cast hτ₁₂)
      | exact hd₁₂ (by exact_mod_cast hτ₁₂.symm)
      | exact hd₁₃ (by exact_mod_cast hτ₁₂.symm)
      | exact hd₂₃ (by exact_mod_cast hτ₁₂.symm)
  have hρχ := hrealodd ρ hρreal hFodd hρ1
  have htA : t ∈ Subgroup.centralizer (PS : Set G) := hCPS ▸ htK
  have ht2' : ¬ ℓ ∣ orderOf t := by
    rw [ht2]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hcoefρ := hcoef ρ hρB t htA ht2'
  rw [characterPairing_column_eq basis principal hprincipal ρ τ₁ δ _ hT₁ ρ,
    ite_eq_right (Ne.symm hρ1), ite_eq_left rfl, ite_eq_right hρτ₁.symm] at hcoefρ
  have hgen : ∀ w : (PS : Subgroup G), Subgroup.zpowers (w : G) = PS → (w : G) ∈ P ∧
      Subgroup.zpowers (w : G) = P := fun w hw => ⟨hPS ▸ w.2, hw.trans hPS⟩
  have hδval : (ρ = χ₁ → δ = -δ₁) ∧ (ρ = χ₂ → δ = δ₂) ∧ (ρ = χ₃ → δ = -δ₃) := by
    refine ⟨fun hρ => ?_, fun hρ => ?_, fun hρ => ?_⟩
    · have h := generator_coefficient_eq PS v hPScard lam₁ hl₁
        (fun w => (basis.representation ρ).character ((w : G) * t)) (-(δ₁ : ℂ)) fun w hw => by
          obtain ⟨hwP, hwg⟩ := hgen w hw
          rw [(Subgroup.mem_centralizer_iff.mp (hWD (hPW hwP)) t htV).symm, hρ]
          exact (hvalgen _ hwP hwg).1
      have h' : (δ : ℂ) = -(δ₁ : ℂ) := by rw [← h]; simpa using hcoefρ
      exact_mod_cast h'
    · have h := generator_coefficient_eq PS v hPScard lam₁ hl₁
        (fun w => (basis.representation ρ).character ((w : G) * t)) ((δ₂ : ℂ)) fun w hw => by
          obtain ⟨hwP, hwg⟩ := hgen w hw
          rw [(Subgroup.mem_centralizer_iff.mp (hWD (hPW hwP)) t htV).symm, hρ]
          exact (hvalgen _ hwP hwg).2.1
      have h' : (δ : ℂ) = (δ₂ : ℂ) := by rw [← h]; simpa using hcoefρ
      exact_mod_cast h'
    · have h := generator_coefficient_eq PS v hPScard lam₁ hl₁
        (fun w => (basis.representation ρ).character ((w : G) * t)) (-(δ₃ : ℂ)) fun w hw => by
          obtain ⟨hwP, hwg⟩ := hgen w hw
          rw [(Subgroup.mem_centralizer_iff.mp (hWD (hPW hwP)) t htV).symm, hρ]
          exact (hvalgen _ hwP hwg).2.2
      have h' : (δ : ℂ) = -(δ₃ : ℂ) := by rw [← h]; simpa using hcoefρ
      exact_mod_cast h'
  have hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t := by
    obtain ⟨-, -, h⟩ := CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn
      S fS
    have hz : (((fS (r n)) ^ 2 ^ (n - 2) : S) : G) = t := by rw [ht, Subgroup.coe_pow]
    intro x
    rw [← hz]
    exact h Group.IsPerfect.commutator_eq_top x
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  obtain ⟨μ, hμdef⟩ : ∃ μ : G → ℂ, ∀ (g : G) (hg : g ∈ Subgroup.centralizer (PS : Set G)),
      μ g = 1 - (lam₁ (π ⟨g, hg⟩) : ℂ) :=
    ⟨fun g => if hg : g ∈ Subgroup.centralizer (PS : Set G) then 1 - (lam₁ (π ⟨g, hg⟩) : ℂ)
      else 0, fun g hg => dite_eq_left hg⟩
  have hTμ : CyclicInversion.inversionColumn PS π lam₁ =
      inducedFunction (Subgroup.centralizer (PS : Set G)) (fun k => μ k) := by
    unfold CyclicInversion.inversionColumn
    congr 1
    funext k
    rw [hμdef k k.2]
  have hPSJ : (PS : Subgroup G) ≤ Subgroup.centralizer (J : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hcommJ x hx j hj).symm
  have hdec : ∀ k : Subgroup.centralizer (PS : Set G), ∃ j ∈ J, (k : G) = (π k : G) * j := by
    intro k
    have hk : (k : G) ∈ (PS : Subgroup G) ⊔ J := by rw [hsupJ]; exact k.2
    obtain ⟨x, hx, j, hj, hxj⟩ := exists_mul_eq_of_mem_sup_of_le_centralizer hPSJ hk
    have hxK : x ∈ Subgroup.centralizer (PS : Set G) := by
      rw [← hsupJ]; exact Subgroup.mem_sup_left hx
    have hjK : j ∈ Subgroup.centralizer (PS : Set G) := by
      rw [← hsupJ]; exact Subgroup.mem_sup_right hj
    have hk' : k = ⟨x, hxK⟩ * ⟨j, hjK⟩ := Subtype.ext hxj.symm
    have hπk : (π k : G) = x := by
      rw [hk', map_mul, hπJ ⟨j, hjK⟩ hj, mul_one]
      exact hπP ⟨x, hxK⟩ hx
    exact ⟨j, hj, by rw [hπk, hxj]⟩
  have hμ : ∀ x : (PS : Subgroup G), ∀ j ∈ J, μ ((x : G) * j) = 1 - (lam₁ x : ℂ) := by
    intro x j hj
    have hxK : (x : G) ∈ Subgroup.centralizer (PS : Set G) := by
      rw [← hsupJ]; exact Subgroup.mem_sup_left x.2
    have hjK : j ∈ Subgroup.centralizer (PS : Set G) := by
      rw [← hsupJ]; exact Subgroup.mem_sup_right hj
    have hxj : (x : G) * j ∈ Subgroup.centralizer (PS : Set G) :=
      Subgroup.mul_mem _ hxK hjK
    have hπ : π ⟨(x : G) * j, hxj⟩ = x := by
      have h : (⟨(x : G) * j, hxj⟩ : Subgroup.centralizer (PS : Set G)) =
          ⟨x, hxK⟩ * ⟨j, hjK⟩ := rfl
      rw [h, map_mul, hπJ ⟨j, hjK⟩ hj, mul_one]
      exact Subtype.ext (hπP ⟨x, hxK⟩ x.2)
    rw [hμdef _ hxj, hπ]
  have hsupp : ∀ k : Subgroup.centralizer (PS : Set G), μ k ≠ 0 →
      extendedCentralizer (k : G) ≤ H := by
    intro k hk
    have hlam : lam₁ (π k) ≠ 1 := by
      intro h1
      apply hk
      rw [hμdef k k.2, h1, Units.val_one, sub_self]
    have hlamℓ : lam₁ ^ ℓ = 1 := by
      have h := pow_orderOf_eq_one lam₁
      rwa [hl₁] at h
    have hgen' := CyclicInversion.zpowers_eq_of_ne_one PS v hPScard lam₁ hlamℓ (π k) hlam
    obtain ⟨j, hj, hkj⟩ := hdec k
    have hcomm : Commute (π k : G) j := hcommJ _ (π k).2 j hj
    have hjcop : Nat.Coprime ℓ (orderOf j) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard J hj) hJcop
    have hπord : orderOf (π k : G) ∣ ℓ ^ v := by
      rw [← hPScard]
      exact Subgroup.orderOf_dvd_natCard _ (π k).2
    obtain ⟨-, -, -, -, -, hloc⟩ := involution_product_extended_centralizer_localization (k : G)
      (∅ : Finset G) (∅ : Finset G) (by simp) (by simp)
    have hE := hloc ℓ (π k) j v hπord hcomm hjcop
    rw [← hkj] at hE
    refine hE.trans ((extendedCentralizer_le_normalizer_zpowers _).trans ?_)
    rw [hgen', hPS, hNP]
  have hKPH : Subgroup.centralizer (PS : Set G) ≤ H := hCPS ▸ hKH'
  have hK' : ∀ x : H, x ∈ K.subgroupOf H ↔ (x : G) ∈ Subgroup.centralizer (PS : Set G) :=
    fun x => by rw [Subgroup.mem_subgroupOf, hCPS]
  obtain ⟨localBasisH⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
  have hGL := global_local_column_identity htt H (Subgroup.centralizer (PS : Set G)) hKPH
    (K.subgroupOf H) hK' (fun k => μ k) (fun k => μ ((k : H) : G)) (fun k => rfl) hsupp basis
    localBasisH
  have hdih : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4) :=
    ⟨P₀, ⟨(Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
      ((MulEquiv.subgroupCongr hP₀).trans eD)⟩⟩
  have hloc : (Nat.card H : ℂ) * ∑ β, characterPairing
      (inducedFunction (K.subgroupOf H) (fun k => μ ((k : H) : G)))
      (localBasisH.representation β).character *
      (classWeight H (localBasisH.representation β).character t *
        classWeight H (localBasisH.representation β).character t /
          (localBasisH.representation β).character 1) =
      if d = 4 then 3 * (Nat.card W : ℂ) else 5 * (Nat.card W : ℂ) / 3 :=
    local_column_sum W hWodd hd hKH hinvH hOK hquot hdih hℓ5 hℓW hℓd (hPS ▸ hPW)
      (by rw [hPS]; exact hPcard) hJcop (by rw [hsupJ, hCPS]) hcommJ lam₁ hl₁ μ hμ hinvol
      localBasisH
  rw [mul_assoc, hloc, ← hTμ] at hGL
  have hFc : ∀ θ : basis.index, (basis.representation θ).character 1 =
      (Module.finrank ℂ (basis.representation θ).vector : ℂ) := fun θ =>
    (basis_character_one basis θ).1
  have hτ₁t : (basis.representation τ₁).character t =
      (basis.representation ρ).character t + δ := (hreg t ht2').1
  have hτ₁F : (basis.representation τ₁).character 1 = (Fρ : ℂ) + δ := by
    rw [hFc]
    exact_mod_cast hτ₁deg
  have hcoefs : ∀ α, characterPairing (CyclicInversion.inversionColumn PS π lam₁)
      (basis.representation α).character = (if principal = α then 1 else 0) +
        (δ : ℂ) * (if ρ = α then 1 else 0) - (δ : ℂ) * (if τ₁ = α then 1 else 0) := fun α =>
    characterPairing_column_eq basis principal hprincipal ρ τ₁ δ _ hT₁ α
  simp_rw [hcoefs] at hGL
  rw [sum_column_coefficients principal ρ τ₁ (δ : ℂ) (fun α =>
    (basis.representation α).character t * (basis.representation α).character t /
      (basis.representation α).character 1)] at hGL
  simp only [hprincipal, Pi.one_apply, mul_one, div_one, hτ₁t, hτ₁F, hFc ρ] at hGL
  obtain ⟨x, hx⟩ : ∃ x : ℂ, (basis.representation ρ).character t = x := ⟨_, rfl⟩
  rw [hx, ← hFρdef] at hGL
  have hδC : (δ : ℂ) = 1 ∨ (δ : ℂ) = -1 := by
    rcases hδ with h | h <;> rw [h] <;> norm_num
  have hFpos : 0 < Fρ := hFodd.pos
  have hF0 : (Fρ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hFpos.ne'
  have hFδ0 : (Fρ : ℂ) + δ ≠ 0 := by
    have h : ((Fρ : ℤ) + δ : ℤ) ≠ 0 := hpos.ne'
    exact_mod_cast h
  have hbr : 1 + (δ : ℂ) * (x * x / Fρ) - δ * ((x + δ) * (x + δ) / (Fρ + δ)) =
      ((Fρ : ℂ) - x) ^ 2 / (Fρ * (Fρ + δ)) := by
    rw [← column_bracket_eq hδC hF0 hFδ0]
    ring
  rw [hbr] at hGL
  set A : ℂ := if d = 4 then 9 else 5 with hAdef
  have h3C : 3 * (Nat.card G : ℂ) * ((Fρ : ℂ) - x) ^ 2 =
      A * (Nat.card W : ℂ) * (Nat.card (C t) : ℂ) ^ 2 * ((Fρ : ℂ) * (Fρ + δ)) := by
    have h := hGL
    rw [mul_div_assoc', div_eq_iff (mul_ne_zero hF0 hFδ0)] at h
    rw [hAdef]
    split_ifs at h ⊢ with hd4
    · linear_combination 3 * h
    · linear_combination 3 * h
  obtain ⟨hne₁, hne₂, hG₁, hG₂⟩ := hOF
  rw [heF, hFcard] at hne₁ hne₂ hG₁ hG₂
  have hdD : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 4 * Nat.card W := by
    rw [← hDcard]
    change _ = Nat.card (Subgroup.centralizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G))
    rw [centralizer_zpowers_sup_zpowers]
  rw [hdD] at hG₁ hG₂
  rw [heF, hFcard] at h₁t h₂t
  rw [show p ^ f = q from rfl] at hne₁ hne₂ hG₁ hG₂ h₁t h₂t
  have hm0 : Nat.card W ≠ 0 := Nat.card_pos.ne'
  have hℓm : ℓ ≤ Nat.card W := Nat.le_of_dvd Nat.card_pos hℓW
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
  have hq9 : (9 : ℤ) ≤ q := by rcases he with h | h <;> rw [h] at hqe <;> omega
  have hcZ : (Nat.card (C t) : ℤ) = 2 * q * ((q : ℤ) ^ 2 - 1) := by
    rw [hC]
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by positivity))
    push_cast [Nat.cast_sub h1]
    rfl
  have hc0 : Nat.card (C t) ≠ 0 := Nat.card_pos.ne'
  have hqZ0 : (q : ℤ) ≠ 0 := by omega
  set A' : ℤ := if d = 4 then 9 else 5 with hA'def
  have hAA : A = (A' : ℂ) := by
    rw [hAdef, hA'def]
    split_ifs <;> norm_num
  rw [hAA] at h3C
  rcases hρχ with hρ | hρ | hρ
  ·
    have hδ1 : δ = -δ₁ := hδval.1 hρ
    have hxv : x = (δ₁ : ℂ) * e * q := by rw [← hx, hρ, h₁t]
    have hFv : Fρ = f₁ := by rw [hFρdef, hρ]
    rw [hxv, hδ1, hFv] at h3C
    have h3Z : 3 * (Nat.card G : ℤ) * ((f₁ : ℤ) - e * δ₁ * q) ^ 2 =
        A' * Nat.card W * (Nat.card (C t) : ℤ) ^ 2 * ((f₁ : ℤ) * (f₁ - δ₁)) := by
      apply Int.cast_injective (α := ℂ)
      push_cast at h3C ⊢
      linear_combination h3C
    have hX : (f₁ : ℤ) - e * δ₁ * q ≠ 0 := by
      intro h0
      apply hne₁
      have h0' : (((f₁ : ℤ) - e * δ₁ * q : ℤ) : ℚ) = 0 := by exact_mod_cast h0
      rw [← h0']
      push_cast
      ring
    have hord := order_column_int (Y := (f₁ : ℤ) * (f₁ + δ₁)) (Z := (q : ℤ) + e) hX hc0 hm0
      hqZ0 (by rw [hG₁]; push_cast; ring) h3Z hqe.symm
    rw [hcZ] at hord
    have hf₁' : (1 : ℤ) < f₁ := hf₁
    rcases hd with hd4 | hd5
    · have hA9 : A' = 9 := by rw [hA'def, ite_eq_left hd4]
      rw [hA9] at hord
      exact chi_one_four_false he hδ₁ hq9 hf₁' ho₁ hqe.symm hord
    · have hA5 : A' = 5 := by rw [hA'def, ite_eq_right (by omega : ¬ d = 4)]
      rw [hA5] at hord
      have hℓ7' := hℓ7 hd5
      have hm7 : (7 : ℤ) ≤ Nat.card W := by exact_mod_cast hℓ7'.trans hℓm
      have hm9 : (Nat.card W : ℤ) ≠ 9 := by
        intro h9
        have h9' : Nat.card W = 9 := by exact_mod_cast h9
        rw [h9'] at hℓW
        have := Nat.le_of_dvd (by norm_num) hℓW
        interval_cases ℓ <;> first | omega | exact absurd hℓ (by norm_num)
      exact chi_one_five_false he hδ₁ hm7 hm9 hf₁' hqe.symm hord
  ·
    have hδ2 : δ = δ₂ := hδval.2.1 hρ
    have hxv : x = -((δ₂ : ℂ) * e * q) := by
      rw [← hx, hρ, h₂t]
    have hFv : Fρ = f₂ := by rw [hFρdef, hρ]
    rw [hxv, hδ2, hFv] at h3C
    have h3Z : 3 * (Nat.card G : ℤ) * ((f₂ : ℤ) + e * δ₂ * q) ^ 2 =
        A' * Nat.card W * (Nat.card (C t) : ℤ) ^ 2 * ((f₂ : ℤ) * (f₂ + δ₂)) := by
      have h : (3 * (Nat.card G : ℤ) * ((f₂ : ℤ) + e * δ₂ * q) ^ 2 : ℤ) =
          (A' * Nat.card W * (Nat.card (C t) : ℤ) ^ 2 * ((f₂ : ℤ) * (f₂ + δ₂)) : ℤ) := by
        apply Int.cast_injective (α := ℂ)
        push_cast
        rw [← h3C]
        ring
      exact h
    have hX : (f₂ : ℤ) + e * δ₂ * q ≠ 0 := by
      intro h0
      apply hne₂
      have h0' : ((f₂ : ℤ) + e * δ₂ * q : ℚ) = 0 := by exact_mod_cast h0
      rw [← h0']
      push_cast
      ring
    have hord := order_column_int (Y := (f₂ : ℤ) * (f₂ + δ₂)) (Z := (q : ℤ) - e) hX hc0 hm0
      hqZ0 (by rw [hG₂]; push_cast; ring) h3Z hqe.symm
    rw [hcZ] at hord
    have hf₂' : (1 : ℤ) < f₂ := hf₂
    exact chi_two_false he (by rw [hA'def]; split_ifs <;> simp) hq9
      (mul_ne_zero (by omega) (by rcases hδ₂ with h | h <;> rw [h] <;> omega)) hqe.symm hord
  ·
    have hδ3 : δ = -δ₃ := hδval.2.2 hρ
    have hxv : x = -(δ₃ : ℂ) := by rw [← hx, hρ, h₃t]
    have hFv : Fρ = f₃ := by rw [hFρdef, hρ]
    rw [hxv, hδ3, hFv] at h3C
    have h3Z : 3 * (Nat.card G : ℤ) * ((f₃ : ℤ) + δ₃) ^ 2 =
        A' * Nat.card W * (Nat.card (C t) : ℤ) ^ 2 * ((f₃ : ℤ) * (f₃ - δ₃)) := by
      apply Int.cast_injective (α := ℂ)
      push_cast at h3C ⊢
      linear_combination h3C
    have hScard : Nat.card (S : Subgroup G) = 2 ^ n := by
      rw [← Nat.card_congr fS.toEquiv]
      exact CFSG.Semidihedral.card n (by omega)
    have hfac : (Nat.card G).factorization 2 = n := by
      have h := S.card_eq_multiplicity
      rw [hScard] at h
      exact (Nat.pow_right_injective le_rfl h).symm
    have hGdec := Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) 2
    have hGodd := Nat.not_dvd_ordCompl Nat.prime_two (Nat.card_pos (α := G)).ne'
    rw [hfac] at hGdec hGodd
    have hq21 : q ^ 2 - 1 ≠ 0 := by
      have : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (by omega)
      omega
    have hv2 : padicValNat 2 (q ^ 2 - 1) = n - 1 := by
      have h := hqM
      rw [hFcard, modulus] at h
      exact Nat.pow_right_injective le_rfl h
    have hqdec := Nat.ordProj_mul_ordCompl_eq_self (q ^ 2 - 1) 2
    have huodd := Nat.not_dvd_ordCompl Nat.prime_two hq21
    rw [Nat.factorization_def _ Nat.prime_two, hv2] at hqdec huodd
    set u := (q ^ 2 - 1) / 2 ^ (n - 1) with hudef
    set g := Nat.card G / 2 ^ n with hgdef
    have hcdec : (Nat.card (C t) : ℤ) = 2 ^ n * ((q : ℤ) * u) := by
      rw [hcZ]
      have h1 : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
        have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
        push_cast [Nat.cast_sub this]
        ring
      have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [← h1, ← hqdec, h2]
      push_cast
      ring
    have hGZ : (Nat.card G : ℤ) = 2 ^ n * g := by
      rw [← hGdec]
      push_cast
      ring
    obtain ⟨y, hy⟩ := hM3
    have hy' : (f₃ : ℤ) + δ₃ = 2 ^ (n - 1) * y := by
      rw [hy, modulus]
      push_cast
      ring
    have hAodd : Odd A' := by
      rw [hA'def]
      split_ifs
      · exact ⟨4, by norm_num⟩
      · exact ⟨2, by norm_num⟩
    have hWoddZ : Odd (Nat.card W : ℤ) := by exact_mod_cast hWodd
    have hc'odd : Odd ((q : ℤ) * u) := by
      have hqo : Odd (q : ℤ) := by exact_mod_cast hqodd
      have huo : Odd (u : ℤ) := by
        have : Odd u := Nat.odd_iff.mpr (by omega)
        exact_mod_cast this
      exact hqo.mul huo
    have hgodd : Odd (g : ℤ) := by
      have : Odd g := Nat.odd_iff.mpr (by omega)
      exact_mod_cast this
    rw [hGZ, hcdec] at h3Z
    exact chi_three_false (g := (g : ℤ)) hn hδ₃ hAodd hWoddZ hc'odd ho₃ hy'
      (by linear_combination h3Z)

end LargePrimeTorus

end CFSG.Semidihedral.Principal
