module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)

section General

variable {G : Type*} [Group G]

theorem card_mulAut_dvd_card_mul_card_outer (C : Type*) [Group C] :
    Nat.card (MulAut C) ∣ Nat.card C * Nat.card (OuterAutomorphisms.Outer C) := by
  rw [← Subgroup.card_mul_index (OuterAutomorphisms.inner C)]
  exact Nat.mul_dvd_mul (Subgroup.card_range_dvd _) dvd_rfl

variable [Finite G] {L : Subgroup G}

theorem card_dvd_two_mul_card_mulAut_of_le_centralizer (hL : standardComponentIsStandard L)
    {C : Type*} [Group C] (e : L ≃* C) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) : Nat.card X ∣ 2 * Nat.card (MulAut C) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hXN : X ≤ normalizer (L : Set G) :=
    hXt.trans (centralizer_le_normalizer_of_standard hL htK.1 ht)
  have hker : Nat.card (restrictAut e hXN).ker ∣ 2 := by
    have hle : (restrictAut e hXN).ker.map X.subtype ≤ zpowers t := by
      rintro _ ⟨y, hy, rfl⟩
      have hy1 : normalizerAut e (Subgroup.inclusion hXN y) = 1 := hy
      rw [normalizerAut_eq_one_iff] at hy1
      exact hKt ▸ mem_inf.2 ⟨hy1, hXt y.2⟩
    have h := card_dvd_of_le hle
    rwa [card_map_of_injective X.subtype_injective, Nat.card_zpowers, ht] at h
  rw [← card_ker_mul_card_range (restrictAut e hXN)]
  exact Nat.mul_dvd_mul hker (Subgroup.card_subgroup_dvd_card _)

omit [Finite G] in
theorem exists_involution_centralizer_le_of_inner_of_center_eq_bot {t : G} (ht : orderOf t = 2)
    {M : Subgroup G}
    {C : Type*} [Group C] (eM : M ≃* C) (hZ : center C = ⊥) {w₀ : C} (hw₀ : orderOf w₀ = 2)
    {m₀ : G} (hm₀M : m₀ ∈ M) (hm₀ : ∀ x ∈ M, t * x * t⁻¹ = m₀ * x * m₀⁻¹) :
    ∃ w ∈ M, orderOf w = 2 ∧ ∀ x ∈ M, x * w = w * x → x * t = t * x := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  by_cases h1 : m₀ = 1
  · refine ⟨(eM.symm w₀ : G), (eM.symm w₀).2, ?_, fun x hx _ => ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hw₀]
    · have h := hm₀ x hx
      rw [h1, one_mul, inv_one, mul_one] at h
      calc x * t = t * x * t⁻¹ * t := by rw [h]
        _ = t * x := by group
  · refine ⟨m₀, hm₀M, ?_, fun x hx hxw => ?_⟩
    · have hcomm : ∀ x ∈ M, m₀ * m₀ * x = x * (m₀ * m₀) := by
        intro x hx
        have hx' : t * x * t⁻¹ ∈ M := by
          rw [hm₀ x hx]
          exact mul_mem (mul_mem hm₀M hx) (inv_mem hm₀M)
        have h2 := hm₀ _ hx'
        have h3 : t * (t * x * t⁻¹) * t⁻¹ = x := by
          calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
            _ = x := by rw [ht2, one_mul, inv_one, mul_one]
        rw [h3, hm₀ x hx] at h2
        calc m₀ * m₀ * x = m₀ * (m₀ * x * m₀⁻¹) * m₀⁻¹ * (m₀ * m₀) := by group
          _ = x * (m₀ * m₀) := by rw [← h2]
      have hcen : eM ⟨m₀ * m₀, mul_mem hm₀M hm₀M⟩ ∈ center C := by
        rw [Subgroup.mem_center_iff]
        intro y
        rw [← eM.apply_symm_apply y, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcomm _ (eM.symm y).2).symm
      rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hcen
      have hsq : m₀ ^ 2 = 1 := by
        rw [sq]
        exact congrArg Subtype.val hcen
      exact orderOf_eq_prime hsq h1
    · have h := hm₀ x hx
      have hx' : m₀ * x * m₀⁻¹ = x := by
        calc m₀ * x * m₀⁻¹ = (x * m₀) * m₀⁻¹ := by rw [← hxw]
          _ = x := by group
      rw [hx'] at h
      calc x * t = t * x * t⁻¹ * t := by rw [h]
        _ = t * x := by group

end General


section TwoParts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem factorization_card_le_of_le_centralizer_E6 (hL : standardComponentIsStandard L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) :
    (Nat.card X).factorization 2 ≤ 36 * f + 2 + f.factorization 2 := by
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  have h1 := card_dvd_two_mul_card_mulAut_of_le_centralizer hL e ht hKt hXt
  have h2 := card_mulAut_dvd_card_mul_card_outer (adjointGroup .E6 K)
  have h3 := (ordinary_E_outer_order_Cartan_divisor TwistTag.E6.tag (Or.inl rfl) Nat.prime_two hf
    K hK 3 2 (Or.inl ⟨rfl, rfl, rfl⟩)).1
  have h4 : Nat.card X ∣ 2 * (Nat.card (adjointGroup .E6 K) * (2 * 3 * f)) :=
    h1.trans (Nat.mul_dvd_mul_left 2 (h2.trans (Nat.mul_dvd_mul_left _
      (h3.trans (by rw [show (3 : ℕ) * 2 = 2 * 3 by norm_num])))))
  have hC0 : Nat.card (adjointGroup .E6 K) ≠ 0 := Nat.card_pos.ne'
  have hf0 : f ≠ 0 := by omega
  have h6 : (2 * 3 * f : ℕ) ≠ 0 := by positivity
  have hN0 : Nat.card (adjointGroup .E6 K) * (2 * 3 * f) ≠ 0 := mul_ne_zero hC0 h6
  have h5 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (mul_ne_zero two_ne_zero hN0)).2 h4 2
  rw [Nat.factorization_mul two_ne_zero hN0, Finsupp.add_apply, Nat.factorization_mul hC0 h6,
    Finsupp.add_apply, Nat.factorization_mul (by norm_num : (2 * 3 : ℕ) ≠ 0) hf0,
    Finsupp.add_apply, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3),
    factorization_card_adjointGroup hK, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E6] at h5
  omega

end TwoParts

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem orderOf_pinnedX_one_adjointGroup {τ : Tag} {K : Type} [Field K] [CharP K 2]
    (α : Fin τ.rank → ℤ) :
    orderOf (⟨pinnedX τ K α 1, pinnedX_mem_adjointGroup α 1⟩ : adjointGroup τ K) = 2 := by
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
  · change pinnedX τ K α 1 ^ 2 = 1
    rw [sq, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  · have h' : pinnedX τ K α 1 = pinnedX τ K α 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (pinnedX_injective τ K α h')

omit
  [Finite G] in
theorem not_exists_inner_of_two_pow_dvd_centralizer {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    {C : Type*} [Group C] (eM : M ≃* C) (hZ : center C = ⊥) {w₀ : C} (hw₀ : orderOf w₀ = 2)
    {a : ℕ} (hA : ∀ w : C, orderOf w = 2 → 2 ^ a ∣ Nat.card (centralizer ({w} : Set C)))
    (hB : ¬ 2 ^ a ∣ Nat.card (centralizer ({t} : Set G))) :
    ¬ ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹ := by
  rintro ⟨m₀, hm₀M, hm₀⟩
  obtain ⟨w, hwM, hw2, hwC⟩ :=
    exists_involution_centralizer_le_of_inner_of_center_eq_bot ht eM hZ hw₀ hm₀M hm₀
  have hw' : orderOf (eM ⟨w, hwM⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hw2]
  set φ : C →* G := M.subtype.comp eM.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := M.subtype_injective.comp eM.symm.injective
  have hφw : φ (eM ⟨w, hwM⟩) = w := by simp [hφ]
  have hle : (centralizer ({eM ⟨w, hwM⟩} : Set C)).map φ ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    have hpw := mem_centralizer_singleton_iff.1 hp
    have hpw' : φ p * w = w * φ p := by
      rw [← hφw, ← map_mul, ← map_mul, hpw]
    exact mem_centralizer_singleton_iff.2 (hwC _ (eM.symm p).2 hpw')
  have h := card_dvd_of_le hle
  rw [card_map_of_injective hφinj] at h
  exact hB ((hA _ hw').trans h)

theorem not_exists_inner_E6_field (hset : StandardSetting G L)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .E6 K₂) :
    ¬ ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹ := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  refine not_exists_inner_of_two_pow_dvd_centralizer ht eM (center_adjointGroup_eq_bot_field _ K₂)
    (orderOf_pinnedX_one_adjointGroup (τ := .E6) (Pi.single (0 : Fin 6) 1)) (a := 26 * (2 * f))
    (fun w hw => two_pow_dvd_card_centralizer_E6 hK₂ hw) fun hdvd => ?_
  have hb := factorization_card_le_of_le_centralizer_E6 hset.standard hK e ht hKt
    (le_refl (centralizer ({t} : Set G)))
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  omega

theorem not_mem_E6_field (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .E6 K₂) :
    t ∉ M :=
  fun htM => not_exists_inner_E6_field hset hK e ht hKt hK₂ eM ⟨t, htM, fun _ _ => rfl⟩

end Inner

end CFSG.SeitzReduction.E6Pilot
