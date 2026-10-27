module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSubfieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedCoordinates
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (mem_coordinateG_iff
  sl_eq_of_coordinateGLAction_eq exists_coordinateE_factor coordinateE_factor_unique
  fieldExtension_mem_E fieldExtension_mem_G_iff fieldExtension_mul fieldExtension_inv
  coordinateD_eq_G even_linear_two_involution_normal_forms coordinateGLAction_toGL
  eq_one_of_sq_eq_one)
open CFSG.Wreathed.CentralSL2 (fieldPerm fieldPerm_apply)

namespace EvenCatalog

section General

theorem eq_one_of_mem_oddCore_of_two_pow {G : Type*} [Group G] [Finite G] {x : G}
    (hx : x ∈ CFSG.oddCore G) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card (CFSG.oddCore G) := Subgroup.orderOf_dvd_natCard _ hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.oddCore G)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr odd_card_oddCore)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem oddCore_eq_bot_of_forall_two_pow {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, ∃ k : ℕ, x ^ 2 ^ k = 1) : CFSG.oddCore G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := h x
  exact eq_one_of_mem_oddCore_of_two_pow hx hk

variable {M : Type*} [Group M]

theorem oddCore_eq_bot_of_normal_of_centralizer {X R : Subgroup M} [Finite X] (hRX : R ≤ X)
    (hnorm : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hR : CFSG.oddCore R = ⊥)
    (hcent : ∀ x ∈ X, (∀ r ∈ R, x * r = r * x) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    CFSG.oddCore X = ⊥ := by
  set O := CFSG.oddCore X with hO
  set P : Subgroup M := O.map X.subtype ⊓ R with hP
  have hPodd : Odd (Nat.card P) := by
    have h1 : Nat.card P ∣ Nat.card (O.map X.subtype) := Subgroup.card_dvd_of_le inf_le_left
    rw [Subgroup.card_map_of_injective X.subtype_injective] at h1
    exact odd_card_oddCore.of_dvd_nat h1
  have hmemO : ∀ g ∈ R, ∀ n ∈ O.map X.subtype, g * n * g⁻¹ ∈ O.map X.subtype := by
    rintro g hg _ ⟨o, ho, rfl⟩
    refine ⟨⟨g, hRX hg⟩ * o * (⟨g, hRX hg⟩ : X)⁻¹,
      (inferInstance : O.Normal).conj_mem _ ho _, ?_⟩
    simp
  have hPR : P.subgroupOf R = ⊥ := by
    have hle : P.subgroupOf R ≤ CFSG.oddCore R := by
      refine le_oddCore_of_normal ⟨fun n hn g => ?_⟩ ?_
      · rw [Subgroup.mem_subgroupOf] at hn ⊢
        have hn' := Subgroup.mem_inf.mp hn
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · simpa using hmemO g g.2 n hn'.1
        · simpa using mul_mem (mul_mem g.2 hn'.2) (inv_mem g.2)
      · rw [show Nat.card (P.subgroupOf R) = Nat.card P from
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
        exact hPodd
    rwa [hR, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hqR : ∀ r ∈ R, (q : M) * r = r * q := by
    intro r hr
    set c : M := (q : M) * r * (q : M)⁻¹ * r⁻¹ with hc
    have hcR : c ∈ R := mul_mem (hnorm q q.2 r hr) (inv_mem hr)
    have hcO : c ∈ O.map X.subtype := by
      have h1 : (⟨r, hRX hr⟩ : X) * q⁻¹ * (⟨r, hRX hr⟩ : X)⁻¹ ∈ O :=
        (inferInstance : O.Normal).conj_mem _ (inv_mem hq) _
      refine ⟨q * ((⟨r, hRX hr⟩ : X) * q⁻¹ * (⟨r, hRX hr⟩ : X)⁻¹), mul_mem hq h1, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hc]
      group
    have hc1 : (⟨c, hcR⟩ : R) ∈ P.subgroupOf R := Subgroup.mem_subgroupOf.mpr ⟨hcO, hcR⟩
    rw [hPR, Subgroup.mem_bot] at hc1
    have hc' : c = 1 := congrArg Subtype.val hc1
    calc (q : M) * r = c * (r * q) := by rw [hc]; group
      _ = r * q := by rw [hc', one_mul]
  obtain ⟨k, hk⟩ := hcent q q.2 hqR
  exact eq_one_of_mem_oddCore_of_two_pow hq (Subtype.ext (by simpa using hk))

end General

section Translations

variable {K : Type} [Field K]

theorem translation_mul_translation (b c : K) :
    translation K b * translation K c = translation K (b + c) := by
  rw [← CFSG.LinearGroups.translationHom_apply, ← CFSG.LinearGroups.translationHom_apply,
    ← map_mul, ← ofAdd_add, CFSG.LinearGroups.translationHom_apply]

theorem translation_zero : translation K 0 = 1 := by
  rw [← CFSG.LinearGroups.translationHom_apply, ofAdd_zero, map_one]

theorem translation_injective : Function.Injective (translation K) := fun b c h => by
  have h1 := congrArg (fun π : Equiv.Perm (Omega K) => π (some 0)) h
  simpa [translation_some] using h1

theorem mem_coordinateU_iff {u : Equiv.Perm (Omega K)} :
    u ∈ coordinateU K ↔ ∃ b : K, u = translation K b := by
  rw [CFSG.LinearGroups.coordinateU_eq_range]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨Multiplicative.toAdd b, (CFSG.LinearGroups.translationHom_apply _).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Multiplicative.ofAdd b, CFSG.LinearGroups.translationHom_apply b⟩

theorem fieldExtension_conj_translation (φ : K ≃+* K) (b : K) :
    fieldExtension K φ * translation K b * (fieldExtension K φ)⁻¹ = translation K (φ b) := by
  rw [UnbalancedGS.SubfieldCentralizer.fieldExtension_mul_translation, mul_inv_cancel_right]

theorem translation_mem_coordinateE (b : K) : translation K b ∈ coordinateE K :=
  coordinateD_le_E K (coordinateG_le_D K (CFSG.LinearGroups.translation_mem_coordinateG b))

theorem coordinateGLAction_upper (b : K) :
    coordinateGLAction K (SpecialLinearGroup.toGL (sl2UpperUnipotent b)) = translation K b := by
  rw [coordinateGLAction_toGL]
  exact coordinatePSLAction_upper K b

variable [CharP K 2]

theorem translation_mul_self (b : K) : translation K b * translation K b = 1 := by
  rw [translation_mul_translation, CharTwo.add_self_eq_zero, translation_zero]

theorem eq_sl2UpperUnipotent_of_commute {A : SpecialLinearGroup (Fin 2) K}
    (h : A * sl2UpperUnipotent 1 = sl2UpperUnipotent 1 * A) :
    A = sl2UpperUnipotent ((A : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  have h' : (A : Matrix (Fin 2) (Fin 2) K) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (A : Matrix (Fin 2) (Fin 2) K) := by
    have h1 := congrArg Subtype.val h
    exact h1
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hdet := A.2
  rw [det_fin_two] at hdet
  have h10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := e00
  have h11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    linear_combination -e01
  have h00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    refine eq_one_of_sq_eq_one ?_
    rw [h10, h11, mul_zero, sub_zero] at hdet
    rw [sq]
    exact hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2UpperUnipotent, h00, h10, h11]

variable [Finite K]

theorem mem_inf_centralizer_translation_one_iff {x : Equiv.Perm (Omega K)} :
    x ∈ coordinateE K ⊓ Subgroup.centralizer {translation K 1} ↔
      ∃ b : K, ∃ φ : K ≃+* K, x = translation K b * fieldExtension K φ := by
  constructor
  · intro hx'
    obtain ⟨hxE, hx⟩ := Subgroup.mem_inf.mp hx'
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨d, hd, φ, rfl⟩ := exists_coordinateE_factor hxE
    have hφ : fieldExtension K φ * translation K 1 = translation K 1 * fieldExtension K φ := by
      rw [UnbalancedGS.SubfieldCentralizer.fieldExtension_mul_translation, map_one]
    have hd1 : d * translation K 1 = translation K 1 * d := by
      have h1 : d * translation K 1 * fieldExtension K φ =
          translation K 1 * d * fieldExtension K φ := by
        rw [mul_assoc, ← hφ, ← mul_assoc, hx, mul_assoc]
      exact mul_right_cancel h1
    obtain ⟨A, rfl⟩ := mem_coordinateG_iff.mp hd
    have hA : A * sl2UpperUnipotent 1 = sl2UpperUnipotent 1 * A := by
      apply sl_eq_of_coordinateGLAction_eq
      rw [map_mul, map_mul, map_mul, map_mul, coordinateGLAction_upper, hd1]
    refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 1, φ, ?_⟩
    rw [← coordinateGLAction_upper]
    congr 3
    exact eq_sl2UpperUnipotent_of_commute hA
  · rintro ⟨b, φ, rfl⟩
    refine Subgroup.mem_inf.mpr
      ⟨mul_mem (translation_mem_coordinateE b) (fieldExtension_mem_E φ), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc,
      UnbalancedGS.SubfieldCentralizer.fieldExtension_mul_translation, map_one, ← mul_assoc,
      translation_mul_translation, ← mul_assoc, translation_mul_translation, add_comm]

end Translations

section Inner

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem conj_mem_coordinateU {x u : Equiv.Perm (Omega K)}
    (hx : x ∈ coordinateE K ⊓ Subgroup.centralizer {translation K 1})
    (hu : u ∈ coordinateU K) : x * u * x⁻¹ ∈ coordinateU K := by
  obtain ⟨b, φ, rfl⟩ := mem_inf_centralizer_translation_one_iff.mp hx
  obtain ⟨c, rfl⟩ := mem_coordinateU_iff.mp hu
  rw [mem_coordinateU_iff]
  refine ⟨φ c, ?_⟩
  rw [_root_.mul_inv_rev, show translation K b * fieldExtension K φ * translation K c *
      ((fieldExtension K φ)⁻¹ * (translation K b)⁻¹) = translation K b *
        (fieldExtension K φ * translation K c * (fieldExtension K φ)⁻¹) *
          (translation K b)⁻¹ by group,
    fieldExtension_conj_translation, translation_mul_translation, add_comm,
    ← translation_mul_translation, mul_inv_cancel_right]

theorem inf_centralizer_translation_one_eq :
    coordinateE K ⊓ Subgroup.centralizer {translation K 1} =
      coordinateU K ⊔ (fieldPerm K).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, φ, rfl⟩ := mem_inf_centralizer_translation_one_iff.mp hx
    exact mul_mem (Subgroup.mem_sup_left (CFSG.LinearGroups.translation_mem_coordinateU b))
      (Subgroup.mem_sup_right ⟨φ, fieldPerm_apply K φ⟩)
  · refine sup_le ?_ ?_
    · intro u hu
      obtain ⟨b, rfl⟩ := mem_coordinateU_iff.mp hu
      have h := mem_inf_centralizer_translation_one_iff.mpr ⟨b, 1, rfl⟩
      rwa [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_one, mul_one] at h
    · rintro _ ⟨φ, rfl⟩
      have h := mem_inf_centralizer_translation_one_iff.mpr ⟨0, φ, rfl⟩
      rwa [translation_zero, one_mul, ← fieldPerm_apply] at h

theorem oddCore_inf_centralizer_translation_one {H : Subgroup (Equiv.Perm (Omega K))}
    (hGH : coordinateG K ≤ H) (hHE : H ≤ coordinateE K) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {translation K 1}) = ⊥ := by
  have hX : ∀ x ∈ H ⊓ Subgroup.centralizer {translation K 1},
      ∃ b : K, ∃ φ : K ≃+* K, x = translation K b * fieldExtension K φ := fun x hx =>
    mem_inf_centralizer_translation_one_iff.mp
      (Subgroup.mem_inf.mpr ⟨hHE (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩)
  refine oddCore_eq_bot_of_normal_of_centralizer (R := coordinateU K) ?_ ?_ ?_ ?_
  · intro u hu
    obtain ⟨b, rfl⟩ := mem_coordinateU_iff.mp hu
    refine Subgroup.mem_inf.mpr ⟨hGH (CFSG.LinearGroups.translation_mem_coordinateG b), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, translation_mul_translation,
      translation_mul_translation, add_comm]
  · intro x hx u hu
    exact conj_mem_coordinateU
      (Subgroup.mem_inf.mpr ⟨hHE (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩) hu
  · refine oddCore_eq_bot_of_forall_two_pow fun u => ⟨1, Subtype.ext ?_⟩
    obtain ⟨b, hb⟩ := mem_coordinateU_iff.mp u.2
    rw [Subgroup.coe_pow, pow_one, sq, hb, translation_mul_self, Subgroup.coe_one]
  · intro x hx hcomm
    obtain ⟨b, φ, rfl⟩ := hX x hx
    have hφ : φ = 1 := RingEquiv.ext fun c => by
      have h1 := hcomm (translation K c) (CFSG.LinearGroups.translation_mem_coordinateU c)
      rw [mul_assoc, UnbalancedGS.SubfieldCentralizer.fieldExtension_mul_translation,
        ← mul_assoc, ← mul_assoc, translation_mul_translation, translation_mul_translation]
        at h1
      have h2 := translation_injective (mul_right_cancel h1)
      change φ c = c
      linear_combination h2
    subst hφ
    refine ⟨1, ?_⟩
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_one, mul_one, pow_one,
      sq, translation_mul_self]

end Inner

section Conj

variable {M : Type*} [Group M]

@[expose] def centralizerConjEquiv (H : Subgroup M) {h : M} (hh : h ∈ H) (t : M) :
    ↥(H ⊓ Subgroup.centralizer {h * t * h⁻¹}) ≃* ↥(H ⊓ Subgroup.centralizer {t}) where
  toFun x := ⟨h⁻¹ * x * h, Subgroup.mem_inf.mpr
    ⟨mul_mem (mul_mem (inv_mem hh) (Subgroup.mem_inf.mp x.2).1) hh, by
      have hx := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h⁻¹ * x * h * t = h⁻¹ * (x * (h * t * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * t * h⁻¹) * x) * h := by rw [hx]
        _ = t * (h⁻¹ * x * h) := by group⟩⟩
  invFun y := ⟨h * y * h⁻¹, Subgroup.mem_inf.mpr
    ⟨mul_mem (mul_mem hh (Subgroup.mem_inf.mp y.2).1) (inv_mem hh), by
      have hy := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * y * h⁻¹ * (h * t * h⁻¹) = h * (y * t) * h⁻¹ := by group
        _ = h * (t * y) * h⁻¹ := by rw [hy]
        _ = h * t * h⁻¹ * (h * y * h⁻¹) := by group⟩⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem card_oddCore_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (CFSG.oddCore G) = Nat.card (CFSG.oddCore H) := by
  have h := CFSG.LocalCores.piCore_map_mulEquiv {q : Nat.Primes | q.val ≠ 2} e
  rw [← CFSG.oddCore_eq_piCore, ← CFSG.oddCore_eq_piCore] at h
  rw [← h, Subgroup.card_map_of_injective e.injective]

end Conj

section Subfield

open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField mem_fixedField_iff
  subfieldCoordinateMap subfieldCoordinateImage subfieldCoordinateImage_eq_D_centralizer
  subfieldCoordinateEquivImage)
open UnbalancedGS.SubfieldCentralizer (subfieldD)

variable {K : Type} [Field K] [Finite K]

abbrev subfieldGImage (k : Subfield K) : Subgroup (Equiv.Perm (Omega K)) :=
  ((coordinateG k).subgroupOf (coordinateD k)).map ((coordinateD K).subtype.comp (subfieldD k))

theorem subfieldD_eq_subfieldCoordinateMap (k : Subfield K) :
    subfieldD k = subfieldCoordinateMap K k :=
  rfl

omit [Finite K] in
theorem fieldExtension_commute (hcyc : IsCyclic (K ≃+* K)) (φ ψ : K ≃+* K) :
    fieldExtension K φ * fieldExtension K ψ = fieldExtension K ψ * fieldExtension K φ := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg φ)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg ψ)
  rw [fieldExtension_mul, fieldExtension_mul, (Commute.zpow_zpow_self g m n).eq]

variable [CharP K 2]

theorem subfieldGImage_eq (k : Subfield K) :
    subfieldGImage k = subfieldCoordinateImage K k := by
  have htop : (coordinateG k).subgroupOf (coordinateD k) = ⊤ := by
    rw [coordinateD_eq_G (K := k), Subgroup.subgroupOf_self]
  rw [subfieldGImage, htop, ← MonoidHom.range_eq_map]
  rfl

theorem subfieldGImage_le_G (k : Subfield K) : subfieldGImage k ≤ coordinateG K := by
  rintro _ ⟨x, -, rfl⟩
  have h : ((subfieldD k x : coordinateD K) : Equiv.Perm (Omega K)) ∈ coordinateD K :=
    (subfieldD k x).2
  exact (coordinateD_eq_G (K := K)).le h

variable {σ : K ≃+* K} (hσ : orderOf σ = 2)
include hσ

theorem subfieldGImage_eq_centralizer :
    subfieldGImage (fixedField K σ) =
      coordinateG K ⊓ Subgroup.centralizer {fieldExtension K σ} := by
  rw [subfieldGImage_eq, subfieldCoordinateImage_eq_D_centralizer K σ hσ, coordinateD_eq_G]

theorem inf_centralizer_fieldExtension (hcyc : IsCyclic (K ≃+* K)) :
    coordinateE K ⊓ Subgroup.centralizer {fieldExtension K σ} =
      subfieldGImage (fixedField K σ) ⊔ (fieldPerm K).range := by
  apply le_antisymm
  · intro x hx'
    obtain ⟨hxE, hx⟩ := Subgroup.mem_inf.mp hx'
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨d, hd, φ, rfl⟩ := exists_coordinateE_factor hxE
    have hd1 : d * fieldExtension K σ = fieldExtension K σ * d := by
      have h1 : d * fieldExtension K σ * fieldExtension K φ =
          fieldExtension K σ * d * fieldExtension K φ := by
        rw [mul_assoc, fieldExtension_commute hcyc σ φ, ← mul_assoc, hx, mul_assoc]
      exact mul_right_cancel h1
    have hdj : d ∈ subfieldGImage (fixedField K σ) := by
      rw [subfieldGImage_eq_centralizer hσ]
      exact Subgroup.mem_inf.mpr ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr hd1⟩
    exact mul_mem (Subgroup.mem_sup_left hdj) (Subgroup.mem_sup_right ⟨φ, fieldPerm_apply K φ⟩)
  · refine sup_le ?_ ?_
    · rw [subfieldGImage_eq_centralizer hσ]
      exact inf_le_inf_right _ (le_trans (coordinateG_le_D K) (coordinateD_le_E K))
    · rintro _ ⟨φ, rfl⟩
      rw [fieldPerm_apply]
      exact Subgroup.mem_inf.mpr ⟨fieldExtension_mem_E φ,
        Subgroup.mem_centralizer_singleton_iff.mpr (fieldExtension_commute hcyc φ σ)⟩

omit hσ in
theorem subfieldGImage_inf_fieldPerm (k : Subfield K) :
    subfieldGImage k ⊓ (fieldPerm K).range = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hG, φ, rfl⟩ := Subgroup.mem_inf.mp hx
  have h := subfieldGImage_le_G k hG
  rw [fieldPerm_apply, fieldExtension_mem_G_iff] at h
  rw [Subgroup.mem_bot, h, map_one]

theorem conj_mem_subfieldGImage {x g : Equiv.Perm (Omega K)}
    (hx : x ∈ coordinateE K ⊓ Subgroup.centralizer {fieldExtension K σ})
    (hg : g ∈ subfieldGImage (fixedField K σ)) :
    x * g * x⁻¹ ∈ subfieldGImage (fixedField K σ) := by
  rw [subfieldGImage_eq_centralizer hσ] at hg ⊢
  obtain ⟨hxE, hxc⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.mp hg
  refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hxc hgc) (inv_mem hxc)⟩
  have hgE : g ∈ coordinateE K := coordinateD_le_E K (coordinateG_le_D K hgG)
  have h := (coordinateG_normal_in_E K).conj_mem ⟨g, hgE⟩
    (Subgroup.mem_subgroupOf.mpr hgG) ⟨x, hxE⟩
  exact Subgroup.mem_subgroupOf.mp h

end Subfield

section SubfieldGroup

open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField mem_fixedField_iff
  subfieldCoordinateEquivImage)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem inf_centralizer_subfieldGImage {g : ℕ} (hg : 1 ≤ g) (hK : Nat.card K = 2 ^ (2 * g))
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2 ^ g) :
    coordinateE K ⊓ Subgroup.centralizer (subfieldGImage (fixedField K σ) : Set _) =
      Subgroup.zpowers (fieldExtension K σ) := by
  rw [inf_comm]
  exact (UnbalancedGS.quadratic_projective_linear_two_subfield_pointwise_centralizer
    Nat.prime_two hg hK σ hσ (fixedField K σ) (mem_fixedField_iff K σ)).2.2.2.2

theorem orderOf_translation_one (k : Type) [Field k] [CharP k 2] :
    orderOf (⟨translation k 1, CFSG.LinearGroups.translation_mem_coordinateG 1⟩ :
      coordinateG k) = 2 := by
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
  · rw [Subgroup.coe_pow, sq, translation_mul_self, Subgroup.coe_one]
  · have h1 := congrArg Subtype.val h
    rw [Subgroup.coe_one, ← translation_zero] at h1
    exact one_ne_zero (translation_injective h1)

@[expose] def pslEquivSubfieldGImage (k : Subfield K) :
    ProjectiveSpecialLinearGroup (Fin 2) k ≃* subfieldGImage k :=
  (pslEquivCoordinateG k).trans ((MulEquiv.subgroupCongr (coordinateD_eq_G (K := k)).symm).trans
    ((subfieldCoordinateEquivImage K k).trans
      (MulEquiv.subgroupCongr (subfieldGImage_eq k).symm)))

theorem oddCore_subfieldGImage_eq_bot (k : Subfield K) (hk : 4 ≤ Nat.card k) :
    CFSG.oddCore (subfieldGImage k) = ⊥ := by
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) k) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hk
  have heven : Even (Nat.card (ProjectiveSpecialLinearGroup (Fin 2) k)) := by
    rw [Nat.card_congr (pslEquivCoordinateG k).toEquiv]
    exact even_iff_two_dvd.mpr (orderOf_translation_one k ▸ orderOf_dvd_natCard _)
  exact oddCore_eq_bot_of_mulEquiv (pslEquivSubfieldGImage k)
    (oddCore_eq_bot_of_isSimpleGroup heven)

theorem coordinateG_eq_top_of_card_eq_two (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = 2) : coordinateG k = ⊤ := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hunits : Nat.card kˣ = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hk]
  have hsq : Nat.card (powMonoidHom 2 : kˣ →* kˣ).range = 1 := by
    have h1 := Subgroup.card_subgroup_dvd_card (powMonoidHom 2 : kˣ →* kˣ).range
    rw [hunits] at h1
    exact Nat.dvd_one.mp h1
  have hG : Nat.card (coordinateG k) = 6 := by
    rw [CFSG.LinearGroups.card_coordinateG, CFSG.LinearGroups.card_coordinateB, hk, hsq]
  apply Subgroup.eq_top_of_card_eq
  rw [hG, Nat.card_perm, Finite.card_option, hk]
  rfl

theorem nonempty_subfieldGImage_mulEquiv_perm (k : Subfield K) (hk : Nat.card k = 2) :
    Nonempty (subfieldGImage k ≃* Equiv.Perm (Fin 3)) := by
  have htop := coordinateG_eq_top_of_card_eq_two k hk
  have hΩ : Nat.card (Omega k) = 3 := by rw [Finite.card_option, hk]
  refine ⟨(pslEquivSubfieldGImage k).symm.trans ((pslEquivCoordinateG k).trans
    ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans
      (Equiv.permCongrHom (Finite.equivFinOfCardEq hΩ)))))⟩

end SubfieldGroup

section Outer

open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField mem_fixedField_iff)
open UnbalancedGS.SubfieldCentralizer (subfieldD fieldExtension_commute_subfieldD)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem fieldExtension_sq_eq_one {σ : K ≃+* K} (hσ2 : orderOf σ = 2) :
    fieldExtension K σ ^ 2 = 1 := by
  rw [sq, fieldExtension_mul, ← sq, ← hσ2, pow_orderOf_eq_one,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_one]

theorem oddCore_inf_centralizer_fieldExtension {g : ℕ} (hg : 1 ≤ g)
    (hK : Nat.card K = 2 ^ (2 * g)) {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2 ^ g)
    (hσ2 : orderOf σ = 2) (hk : 4 ≤ Nat.card (fixedField K σ))
    {H : Subgroup (Equiv.Perm (Omega K))} (hGH : coordinateG K ≤ H) (hHE : H ≤ coordinateE K) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {fieldExtension K σ}) = ⊥ := by
  refine oddCore_eq_bot_of_normal_of_centralizer (R := subfieldGImage (fixedField K σ)) ?_ ?_
    (oddCore_subfieldGImage_eq_bot _ hk) ?_
  · rw [subfieldGImage_eq_centralizer hσ2]
    exact inf_le_inf_right _ hGH
  · intro x hx r hr
    exact conj_mem_subfieldGImage hσ2
      (Subgroup.mem_inf.mpr ⟨hHE (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩) hr
  · intro x hx hcomm
    have hxc : x ∈ coordinateE K ⊓
        Subgroup.centralizer (subfieldGImage (fixedField K σ) : Set _) :=
      Subgroup.mem_inf.mpr ⟨hHE (Subgroup.mem_inf.mp hx).1,
        Subgroup.mem_centralizer_iff.mpr fun r hr => (hcomm r hr).symm⟩
    rw [inf_centralizer_subfieldGImage hg hK hσ] at hxc
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxc
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      fieldExtension_sq_eq_one hσ2, _root_.one_zpow]

theorem eq_zero_or_one_of_card_two {k : Type*} [Field k] (hk : Nat.card k = 2) (x : k) :
    x = 0 ∨ x = 1 := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have : Fintype k := Fintype.ofFinite k
  have huniv : ({0, 1} : Finset k) = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hk])
  have hx : x ∈ ({0, 1} : Finset k) := huniv ▸ Finset.mem_univ x
  simpa using hx

theorem card_oddCore_perm_three_prod :
    Nat.card (CFSG.oddCore (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) = 3 := by
  set G := Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)
  set N : Subgroup G := (alternatingGroup (Fin 3)).prod ⊥
  have hA : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hN3 : Nat.card N = 3 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
      mul_one, hA]
  have hle : N ≤ CFSG.oddCore G := le_oddCore_of_normal inferInstance (by rw [hN3]; decide)
  have h3 : 3 ∣ Nat.card (CFSG.oddCore G) :=
    (dvd_of_eq hN3.symm).trans (Subgroup.card_dvd_of_le hle)
  have hG : Nat.card G = 12 := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_fin,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]
    rfl
  have h12 : Nat.card (CFSG.oddCore G) ∣ 4 * 3 := by
    rw [show 4 * 3 = 12 from rfl, ← hG]
    exact Subgroup.card_subgroup_dvd_card _
  have hcop : Nat.Coprime (Nat.card (CFSG.oddCore G)) 4 :=
    Nat.Coprime.pow_right 2 (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr odd_card_oddCore))
  exact Nat.dvd_antisymm (hcop.dvd_of_dvd_mul_left h12) h3

end Outer

section FieldFour

open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField)
open UnbalancedGS.SubfieldCentralizer (subfieldD fieldExtension_commute_subfieldD)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nonempty_inf_centralizer_mulEquiv (hK : Nat.card K = 2 ^ 2) {σ : K ≃+* K}
    (hσ2 : orderOf σ = 2) (hk2 : Nat.card (fixedField K σ) = 2) :
    Nonempty (↥(coordinateE K ⊓ Subgroup.centralizer {fieldExtension K σ}) ≃*
      Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) := by
  obtain ⟨φ₀, -, -, hzp, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (n := 2) (by norm_num) hK
  have hcyc : IsCyclic (K ≃+* K) := ⟨⟨φ₀, fun x =>
    Subgroup.mem_zpowers_iff.mp (by rw [hzp]; exact Subgroup.mem_top x)⟩⟩
  obtain ⟨-, -, -, -, -, hinjF, -⟩ := even_linear_two_involution_normal_forms (by norm_num) hK
  set k := fixedField K σ with hkdef
  set J := subfieldGImage k with hJ
  set F := (fieldPerm K).range with hF
  have hfix : ∀ φ : K ≃+* K, ∀ x ∈ k, φ x = x := by
    intro φ x hx
    rcases eq_zero_or_one_of_card_two hk2 ⟨x, hx⟩ with h | h
    · rw [show x = 0 from congrArg Subtype.val h, map_zero]
    · rw [show x = 1 from congrArg Subtype.val h, map_one]
  have hcomm : ∀ (r : J) (s : F), Commute (J.subtype r) (F.subtype s) := by
    rintro ⟨_, x, -, rfl⟩ ⟨_, φ, rfl⟩
    exact (fieldExtension_commute_subfieldD k φ (hfix φ) x).symm
  set ψ := MonoidHom.noncommCoprod J.subtype F.subtype hcomm with hψ
  have hrange : ψ.range = coordinateE K ⊓ Subgroup.centralizer {fieldExtension K σ} := by
    rw [hψ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype,
      inf_centralizer_fieldExtension hσ2 hcyc]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨r, s⟩ h
    have h' : (r : Equiv.Perm (Omega K)) * s = 1 := by simpa [hψ] using h
    have h1 : (r : Equiv.Perm (Omega K)) = (s : Equiv.Perm (Omega K))⁻¹ :=
      eq_inv_of_mul_eq_one_left h'
    have hr : (r : Equiv.Perm (Omega K)) ∈ J ⊓ F :=
      Subgroup.mem_inf.mpr ⟨r.2, h1 ▸ inv_mem s.2⟩
    have hbot : J ⊓ F = ⊥ := subfieldGImage_inf_fieldPerm k
    rw [hbot, Subgroup.mem_bot] at hr
    rw [hr, one_mul] at h'
    exact Prod.ext (Subtype.ext hr) (Subtype.ext h')
  have e1 : J × F ≃* ↥(coordinateE K ⊓ Subgroup.centralizer {fieldExtension K σ}) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  obtain ⟨e2⟩ := nonempty_subfieldGImage_mulEquiv_perm k hk2
  have e3 : F ≃* Multiplicative (ZMod 2) :=
    (MonoidHom.ofInjective hinjF).symm.trans ((zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv))
  exact ⟨e1.symm.trans (MulEquiv.prodCongr e2 e3)⟩

end FieldFour

end EvenCatalog

open EvenCatalog
open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField mem_fixedField_iff)
open UnbalancedGS.SubfieldCentralizer (subfieldD subfieldD_injective subfieldD_mk)

theorem even_linear_two_full_centralizer_odd_core {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ f) :
    (∀ H : Subgroup (Equiv.Perm (Omega K)), coordinateG K ≤ H → H ≤ coordinateE K →
      ∀ a ∈ H, orderOf a = 2 →
        (CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({a} : Set _)) ≠ ⊥ ↔
          f = 2 ∧ a ∉ coordinateG K)) ∧
    (∀ H : Subgroup (Equiv.Perm (Omega K)), coordinateG K ≤ H → H ≤ coordinateE K →
      ∀ a ∈ H, orderOf a = 2 → f = 2 → a ∉ coordinateG K →
        H = coordinateE K ∧
        Nonempty (↥(H ⊓ Subgroup.centralizer ({a} : Set _)) ≃*
          Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) ∧
        IsCyclic ↥(CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({a} : Set _))) ∧
        Nat.card ↥(CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({a} : Set _))) = 3) ∧
    (coordinateE K ⊓ Subgroup.centralizer {translation K 1} =
        coordinateU K ⊔ (fieldPerm K).range ∧
      coordinateU K ⊓ (fieldPerm K).range = ⊥ ∧
      (∀ x ∈ coordinateE K ⊓ Subgroup.centralizer {translation K 1}, ∀ u ∈ coordinateU K,
        x * u * x⁻¹ ∈ coordinateU K) ∧
      ∀ (φ : K ≃+* K) (b : K),
        fieldExtension K φ * translation K b * (fieldExtension K φ)⁻¹ = translation K (φ b)) ∧
    (Even f → ∀ σ : K ≃+* K, (∀ x, σ x = x ^ 2 ^ (f / 2)) →
      Function.Injective ((subfieldD (fixedField K σ)).comp
        ((coordinateG (fixedField K σ)).subgroupOf (coordinateD (fixedField K σ))).subtype) ∧
      subfieldGImage (fixedField K σ) ≤ coordinateG K ∧
      (∀ A : GL (Fin 2) (fixedField K σ),
        (subfieldD (fixedField K σ) (pglEquivCoordinateD _ (Matrix.ProjGenLinGroup.mk A)) :
          Equiv.Perm (Omega K)) =
            coordinateGLAction K (Matrix.GeneralLinearGroup.map (fixedField K σ).subtype A)) ∧
      coordinateE K ⊓ Subgroup.centralizer {fieldExtension K σ} =
        subfieldGImage (fixedField K σ) ⊔ (fieldPerm K).range ∧
      subfieldGImage (fixedField K σ) ⊓ (fieldPerm K).range = ⊥ ∧
      (∀ x ∈ coordinateE K ⊓ Subgroup.centralizer {fieldExtension K σ},
        ∀ g ∈ subfieldGImage (fixedField K σ),
          x * g * x⁻¹ ∈ subfieldGImage (fixedField K σ)) ∧
      coordinateE K ⊓ Subgroup.centralizer (subfieldGImage (fixedField K σ) : Set _) =
        Subgroup.zpowers (fieldExtension K σ)) := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  obtain ⟨φ₀, -, -, hzp, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ f) hK
  have hcyc : IsCyclic (K ≃+* K) := ⟨⟨φ₀, fun x =>
    Subgroup.mem_zpowers_iff.mp (by rw [hzp]; exact Subgroup.mem_top x)⟩⟩
  obtain ⟨-, -, -, -, hGF, -, -, -, -, hinv⟩ :=
    even_linear_two_involution_normal_forms (by omega) hK
  have hσfacts : Even f → ∀ σ : K ≃+* K, (∀ x, σ x = x ^ 2 ^ (f / 2)) →
      orderOf σ = 2 ∧ Nat.card (fixedField K σ) = 2 ^ (f / 2) := by
    intro hfe σ hσ
    obtain ⟨σ', hσ', hσ'1, hσ'2, F, hF, hFcard⟩ :=
      CFSG.LinearGroups.finite_field_quadratic_frobenius Nat.prime_two (f := f / 2) (K := K)
        (by omega) (by rw [hK, ← pow_mul]; congr 1; obtain ⟨m, hm⟩ := hfe; omega)
    have hσσ' : σ = σ' := RingEquiv.ext fun x => by rw [hσ, hσ']
    subst hσσ'
    refine ⟨orderOf_eq_prime hσ'2 hσ'1, ?_⟩
    rw [← hFcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [mem_fixedField_iff, hF, hσ'])
  have hK2 : Even f → Nat.card K = 2 ^ (2 * (f / 2)) := fun hfe => by
    rw [hK]
    congr 1
    obtain ⟨m, hm⟩ := hfe
    omega
  have houter : ∀ H : Subgroup (Equiv.Perm (Omega K)), coordinateG K ≤ H →
      H ≤ coordinateE K → ∀ a ∈ H, orderOf a = 2 → a ∉ coordinateG K →
        (f ≠ 2 → CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({a} : Set _)) = ⊥) ∧
        (f = 2 → H = coordinateE K ∧
          Nonempty (↥(H ⊓ Subgroup.centralizer ({a} : Set _)) ≃*
            Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) ∧
          IsCyclic ↥(CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({a} : Set _))) ∧
          Nat.card ↥(CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({a} : Set _))) = 3) := by
    intro H hGH hHE a haH ha2 haG
    rcases hinv a (hHE haH) ha2 with ⟨haG', -⟩ | ⟨-, hfe, σ, hσ1, hσσ, hσ, huniq, ⟨d, hd, had⟩,
        ⟨h, hh, hah⟩, -⟩
    · exact absurd haG' haG
    obtain ⟨hσ2, hkcard⟩ := hσfacts hfe σ hσ
    have hhH : h ∈ H := hGH hh
    subst hah
    refine ⟨fun hf2 => ?_, fun hf2 => ?_⟩
    ·
      have hk4 : 4 ≤ Nat.card (fixedField K σ) := by
        rw [hkcard]
        obtain ⟨m, hm⟩ := hfe
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (f / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact oddCore_eq_bot_of_mulEquiv (centralizerConjEquiv H hhH _).symm
        (oddCore_inf_centralizer_fieldExtension (g := f / 2) (by omega) (hK2 hfe) hσ hσ2 hk4
          hGH hHE)
    ·
      subst hf2
      have hk2 : Nat.card (fixedField K σ) = 2 := by rw [hkcard]; norm_num
      have hσH : fieldExtension K σ ∈ H := by
        have h1 := mul_mem (inv_mem (hGH hd)) haH
        rwa [had, inv_mul_cancel_left] at h1
      have hHE' : H = coordinateE K := by
        refine le_antisymm hHE fun x hx => ?_
        obtain ⟨g, hg, φ, rfl⟩ := exists_coordinateE_factor hx
        by_cases hφ : φ = 1
        · rw [hφ, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_one, mul_one]
          exact hGH hg
        · have hφφ : φ * φ = 1 := by
            rw [← sq, ← hcardAut]
            exact pow_card_eq_one'
          rw [huniq φ hφ hφφ]
          exact mul_mem (hGH hg) hσH
      subst hHE'
      obtain ⟨e⟩ := nonempty_inf_centralizer_mulEquiv hK hσ2 hk2
      have e' := (centralizerConjEquiv (coordinateE K) hhH (fieldExtension K σ)).trans e
      have hcard3 : Nat.card ↥(CFSG.oddCore ↥(coordinateE K ⊓
          Subgroup.centralizer ({h * fieldExtension K σ * h⁻¹} : Set _))) = 3 := by
        rw [card_oddCore_congr e', card_oddCore_perm_three_prod]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact ⟨rfl, ⟨e'⟩, isCyclic_of_prime_card hcard3, hcard3⟩
  have hinner : ∀ H : Subgroup (Equiv.Perm (Omega K)), coordinateG K ≤ H →
      H ≤ coordinateE K → ∀ a ∈ H, orderOf a = 2 → a ∈ coordinateG K →
        CFSG.oddCore ↥(H ⊓ Subgroup.centralizer ({a} : Set _)) = ⊥ := by
    intro H hGH hHE a haH ha2 haG
    rcases hinv a (hHE haH) ha2 with ⟨-, h, hh, rfl⟩ | ⟨haG', -⟩
    · exact oddCore_eq_bot_of_mulEquiv (centralizerConjEquiv H (hGH hh) _).symm
        (oddCore_inf_centralizer_translation_one hGH hHE)
    · exact absurd haG haG'
  refine ⟨fun H hGH hHE a haH ha2 => ?_, fun H hGH hHE a haH ha2 hf2 haG =>
    (houter H hGH hHE a haH ha2 haG).2 hf2, ⟨inf_centralizer_translation_one_eq, ?_,
      fun x hx u hu => conj_mem_coordinateU hx hu, fieldExtension_conj_translation⟩,
    fun hfe σ hσ => ?_⟩
  · constructor
    · intro hne
      by_cases haG : a ∈ coordinateG K
      · exact absurd (hinner H hGH hHE a haH ha2 haG) hne
      · by_cases hf2 : f = 2
        · exact ⟨hf2, haG⟩
        · exact absurd ((houter H hGH hHE a haH ha2 haG).1 hf2) hne
    · rintro ⟨hf2, haG⟩ hbot
      have h3 := ((houter H hGH hHE a haH ha2 haG).2 hf2).2.2.2
      rw [hbot, Subgroup.card_bot] at h3
      omega
  · rw [eq_bot_iff, ← hGF]
    exact inf_le_inf_right _ CFSG.LinearGroups.coordinateU_le_coordinateG
  · obtain ⟨hσ2, -⟩ := hσfacts hfe σ hσ
    exact ⟨(subfieldD_injective _).comp (Subgroup.subtype_injective _),
      subfieldGImage_le_G _, subfieldD_mk _, inf_centralizer_fieldExtension hσ2 hcyc,
      subfieldGImage_inf_fieldPerm _, fun x hx g hg => conj_mem_subfieldGImage hσ2 hx hg,
      inf_centralizer_subfieldGImage (g := f / 2) (by omega) (hK2 hfe) hσ⟩

end CFSG.ComponentClassification.UnbalancedCatalog
