module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCExponentObstruction
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCElementaryCoset
public import CFSG.GroupTheory.FrattiniQuotient

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G]

theorem commutator_zpowers_eq_of_not_commute {L : Subgroup G} {z : G}
    (hLz : ⁅L, L⁆ = zpowers z) (hz : orderOf z = 2) {b : G} (hb : b ∈ L)
    (hbnc : ∃ y ∈ L, b * y ≠ y * b) : ⁅zpowers b, L⁆ = zpowers z := by
  apply le_antisymm
  · rw [← hLz]
    exact commutator_mono (zpowers_le.mpr hb) le_rfl
  · obtain ⟨y, hy, hby⟩ := hbnc
    have hne : ⁅zpowers b, L⁆ ≠ ⊥ := by
      intro h
      apply hby
      have hle := commutator_eq_bot_iff_le_centralizer.mp h
      exact (mem_centralizer_iff.mp (hle (mem_zpowers b)) y hy).symm
    obtain ⟨⟨c, hc⟩, hc1⟩ := ne_bot_iff_exists_ne_one.mp hne
    have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hcz : c ∈ zpowers z := by
      rw [← hLz]
      exact commutator_mono (zpowers_le.mpr hb) le_rfl hc
    rcases eq_one_or_eq_of_mem_zpowers hz hcz with h | h
    · exact absurd h hc1'
    · rw [zpowers_le, ← h]
      exact hc

theorem eq_or_eq_of_mem_zpowers_of_orderOf_eq_four {t x : G} (ht : orderOf t = 4)
    (hx : x ∈ zpowers t) (hxo : orderOf x = 4) : x = t ∨ x = t ^ 3 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hk : t ^ (k % 4) = t ^ k := by simpa [ht] using zpow_mod_orderOf t k
  rw [← hk] at hxo ⊢
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg _ (by norm_num)
  have h4 : k % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 by omega) with h | h | h | h
  · rw [h, zpow_zero, orderOf_one] at hxo
    exact absurd hxo (by norm_num)
  · left
    rw [h, zpow_one]
  · exfalso
    rw [h, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
      orderOf_pow' t (by norm_num), ht] at hxo
    norm_num at hxo
  · right
    rw [h, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]

theorem natCard_eq_two_pow_finrank (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
  classical
  have : Fintype W := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem cyclic_four_normalizer_forces_small_quadratic_action [Finite G] {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) {z : G} (hΦ : (frattini Q).map Q.subtype = zpowers z)
    (hQ' : ⁅Q, Q⁆ = zpowers z) (hz : orderOf z = 2) {t : G}
    (htN : t ∈ normalizer (Q : Set G)) (ht : orderOf t = 4) (haQ : t ^ 2 ∈ Q)
    (haZ : ∃ q ∈ Q, t ^ 2 * q ≠ q * t ^ 2) (htZ : ∀ c : Q, c ∈ center Q → t * c = c * t)
    (hNX : normalizer (zpowers t : Set G) = centralizer {t ^ 2}) :
    t ∉ Q ∧
    (∃ _ : IsElementaryAbelian 2 (Q ⧸ center Q),
      ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ center Q)),
        (∀ x y : Q, ((⁅x, y⁆ : Q) : G) = z ^ (b (Additive.ofMul (x : Q ⧸ center Q))
          (Additive.ofMul (y : Q ⧸ center Q))).val) ∧
        (∀ b' : LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ center Q)),
          (∀ x y : Q, ((⁅x, y⁆ : Q) : G) = z ^ (b' (Additive.ofMul (x : Q ⧸ center Q))
            (Additive.ofMul (y : Q ⧸ center Q))).val) → b' = b) ∧
        b.IsAlt ∧ b.Nondegenerate ∧
        ∃ T : Module.End (ZMod 2) (Additive (Q ⧸ center Q)),
          (∀ x y : Q, (y : G) = t * x * t⁻¹ →
            T (Additive.ofMul (x : Q ⧸ center Q)) = Additive.ofMul (y : Q ⧸ center Q)) ∧
          T ≠ 1 ∧ T * T = 1 ∧
          (∀ v, T v = v ↔
            ∃ q : Q, (q : G) * t = t * q ∧ v = Additive.ofMul (q : Q ⧸ center Q)) ∧
          (∃ m : ℕ, Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = m ∧
            (centralizer {t}).relIndex Q = 2 ^ m ∧ (m = 1 ∨ m = 2) ∧
            Nat.card {x | ∃ q ∈ Q, x = q⁻¹ * t * q} = 2 ^ m) ∧
          (∀ v, b v ((T - 1) v) = b v (Additive.ofMul ((⟨t ^ 2, haQ⟩ : Q) : Q ⧸ center Q))) ∧
          ∃ v, b v (Additive.ofMul ((⟨t ^ 2, haQ⟩ : Q) : Q ⧸ center Q)) ≠ 0) ∧
    (∃ q₀ ∈ Q, CFSG.conjugate (zpowers t) q₀ ≠ zpowers t ∧
      (∀ q ∈ Q, CFSG.conjugate (zpowers t) q = zpowers t ∨
        CFSG.conjugate (zpowers t) q = CFSG.conjugate (zpowers t) q₀) ∧
      (∀ x ∈ zpowers t, ∀ y ∈ CFSG.conjugate (zpowers t) q₀, x * y = y * x) ∧
      zpowers t ⊓ CFSG.conjugate (zpowers t) q₀ = ⊥ ∧
      closure {x | ∃ q ∈ Q, x = q⁻¹ * t * q} = zpowers t ⊔ CFSG.conjugate (zpowers t) q₀) ∧
    Nonempty (closure {x | ∃ q ∈ Q, x = q⁻¹ * t * q} ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    Q ≤ normalizer ((closure {x | ∃ q ∈ Q, x = q⁻¹ * t * q} : Subgroup G) : Set G) ∧
    Nat.card (closure {x | ∃ q ∈ Q, x = q⁻¹ * t * q} ⊓ Q : Subgroup G) = 8 ∧
    IsMulCommutative (closure {x | ∃ q ∈ Q, x = q⁻¹ * t * q} ⊓ Q : Subgroup G) ∧
    ∀ q ∈ Q, t⁻¹ * (q⁻¹ * t * q) ∈ Q ∧
      (t⁻¹ * (q⁻¹ * t * q)) ^ 2 = (t ^ 2)⁻¹ * (q⁻¹ * t ^ 2 * q) ∧
      q⁻¹ * (t⁻¹ * (q⁻¹ * t * q)) * q = (t⁻¹ * (q⁻¹ * t * q))⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two hz
  have hzsq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz
  have hzQ : z ∈ Q := commutator_le_self Q (hQ' ▸ mem_zpowers z)
  have hzc : ∀ g ∈ normalizer (Q : Set G), g * z = z * g := fun g hg => by
    have h := conj_eq_of_mem_normalizer_of_commutator_eq hQ' hz hg
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h]
  have hsq : ∀ x : Q, (x : G) ^ 2 = 1 ∨ (x : G) ^ 2 = z := by
    intro x
    obtain ⟨-, -, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ2
    have h1 : x ^ 2 ∈ frattini Q := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hpow _
    have h2 : ((x ^ 2 : Q) : G) ∈ zpowers z := hΦ ▸ mem_map_of_mem Q.subtype h1
    rw [Subgroup.coe_pow] at h2
    exact eq_one_or_eq_of_mem_zpowers hz h2
  have hcm : ∀ x y : Q, ((⁅x, y⁆ : Q) : G) = 1 ∨ ((⁅x, y⁆ : Q) : G) = z := by
    intro x y
    have h1 : ((⁅x, y⁆ : Q) : G) = ⁅(x : G), (y : G)⁆ := map_commutatorElement Q.subtype _ _
    have h2 : ⁅(x : G), (y : G)⁆ ∈ zpowers z := hQ' ▸ commutator_mem_commutator x.2 y.2
    rw [h1]
    exact eq_one_or_eq_of_mem_zpowers hz h2
  set z' : Q := ⟨z, hzQ⟩ with hz'def
  have hz'Z : z' ∈ center Q := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * z = z * g
    exact hzc g (le_normalizer g.2)
  have hz'o : orderOf z' = 2 := by rw [Subgroup.orderOf_mk, hz]
  have hzz' : ∀ x y : Q, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z' := by
    intro x y
    rcases hcm x y with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hmemZ : ∀ c : Q, (c : G) = 1 ∨ (c : G) = z → c ∈ center Q := by
    intro c hc
    rcases hc with h | h
    · rw [show c = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show c = z' from Subtype.ext h]
      exact hz'Z
  have hEA : IsElementaryAbelian 2 (Q ⧸ center Q) := by
    refine { toIsMulCommutative := ⟨⟨fun u w => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [h1]
      exact hmemZ _ (hcm _ _)
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun u => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      apply hmemZ
      rw [Subgroup.coe_pow]
      exact hsq x
  have htQ : t ∉ Q := by
    intro htQ
    obtain ⟨q, hq, hne⟩ := haZ
    apply hne
    have h1 := hsq ⟨t, htQ⟩
    rcases h1 with h | h
    · change t ^ 2 = 1 at h
      rw [h, one_mul, mul_one]
    · change t ^ 2 = z at h
      rw [h]
      exact (hzc q (le_normalizer hq)).symm
  have hexp : ∀ x ∈ Q, x ^ (2 ^ 2) = 1 := by
    intro x hx
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul]
    rcases hsq ⟨x, hx⟩ with h | h
    · change x ^ 2 = 1 at h
      rw [h, one_pow]
    · change x ^ 2 = z at h
      rw [h, ← hz, pow_orderOf_eq_one]
  have hXL : zpowers t ≤ normalizer (Q : Set G) := zpowers_le.mpr htN
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hX1 : zpowers t ≠ ⊥ := by
    intro h
    apply ht1
    have := mem_zpowers t
    rw [h, mem_bot] at this
    exact this
  have hX2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ht]; norm_num)
  have haX : t ^ 2 ∈ zpowers t := pow_mem (mem_zpowers t) 2
  have hao : orderOf (t ^ 2) = 2 := by
    rw [orderOf_pow' t two_ne_zero, ht]
    norm_num
  obtain ⟨q₁, hq₁, hq₁ne⟩ := haZ
  have haL : ⁅zpowers (t ^ 2), Q⁆ = zpowers z :=
    commutator_zpowers_eq_of_not_commute hQ' hz haQ ⟨q₁, hq₁, hq₁ne⟩
  obtain ⟨⟨q₀, hq₀Q, hX₁ne, htwo, hcommX, hinf, hLN, hiso⟩, hdclaim, -, -⟩ :=
    cyclic_involution_normalizer_exponent_obstruction hQ2 ⟨t ^ 2, haQ, q₁, hq₁, hq₁ne⟩ hQ' hz
      (by norm_num : 1 ≤ 2) hexp hXL hX1 hX2 haX hao haL hNX
  set X₁ := CFSG.conjugate (zpowers t) q₀ with hX₁
  set A : Subgroup G := closure {x | ∃ q ∈ Q, x = q⁻¹ * t * q} with hA
  have hAeq : A = zpowers t ⊔ X₁ := by
    apply le_antisymm
    · rw [hA, closure_le]
      rintro x ⟨q, hq, rfl⟩
      have h1 : q⁻¹ * t * q ∈ CFSG.conjugate (zpowers t) q :=
        inv_mul_mul_mem_conjugate (mem_zpowers t)
      rcases htwo q hq with h | h
      · rw [h] at h1
        exact mem_sup_left h1
      · rw [h] at h1
        exact mem_sup_right h1
    · apply sup_le
      · rw [zpowers_le]
        exact subset_closure ⟨1, one_mem _, by group⟩
      · have h1 : X₁ = zpowers (q₀⁻¹ * t * q₀) := by
          rw [hX₁]
          unfold CFSG.conjugate
          rw [MonoidHom.map_zpowers]
          simp
        rw [h1, zpowers_le]
        exact subset_closure ⟨q₀, hq₀Q, rfl⟩
  have hXC4 : zpowers t ≃* Multiplicative (ZMod 4) :=
    mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, ht]; simp)
  have hAiso : A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
    ((MulEquiv.subgroupCongr hAeq).trans (Classical.choice hiso)).trans
      (MulEquiv.prodCongr hXC4 hXC4)
  have hAcard : Nat.card A = 16 := by
    rw [Nat.card_congr hAiso.toEquiv, Nat.card_prod]
    simp
  have hAcomm : ∀ x y : A, x * y = y * x := by
    intro x y
    apply hAiso.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have htA : t ∈ A := subset_closure ⟨1, one_mem _, by group⟩
  have hAQ : ∀ x ∈ A, x ∈ Q ∨ x * t⁻¹ ∈ Q := by
    intro x hx
    rw [hA] at hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      right
      have h1 : t * q * t⁻¹ ∈ Q := (mem_normalizer_iff.mp htN q).mp hq
      rw [show q⁻¹ * t * q * t⁻¹ = q⁻¹ * (t * q * t⁻¹) by group]
      exact mul_mem (inv_mem hq) h1
    | one => exact Or.inl (one_mem _)
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (mul_mem hx hy)
      · right
        rw [mul_assoc]
        exact mul_mem hx hy
      · right
        have h1 : t * y * t⁻¹ ∈ Q := (mem_normalizer_iff.mp htN y).mp hy
        rw [show x * y * t⁻¹ = x * t⁻¹ * (t * y * t⁻¹) by group]
        exact mul_mem hx h1
      · left
        have h1 : t * (y * t⁻¹) * t⁻¹ ∈ Q := (mem_normalizer_iff.mp htN _).mp hy
        rw [show x * y = x * t⁻¹ * (t * (y * t⁻¹) * t⁻¹) * t ^ 2 by group]
        exact mul_mem (mul_mem hx h1) haQ
    | inv x _ hx =>
      rcases hx with hx | hx
      · exact Or.inl (inv_mem hx)
      · right
        have h1 : t⁻¹ * (x * t⁻¹)⁻¹ * t ∈ Q :=
          (mem_normalizer_iff''.mp htN _).mp (inv_mem hx)
        rw [show x⁻¹ * t⁻¹ = t⁻¹ * (x * t⁻¹)⁻¹ * t * (t ^ 2)⁻¹ by group]
        exact mul_mem h1 (inv_mem haQ)
  have hindex : (Q.subgroupOf A).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨t, htA⟩, fun y => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul]
    by_cases hy : (y : G) ∈ Q
    · have h1 : (y : G) * t ∉ Q := fun h => htQ (by
        rw [show t = (y : G)⁻¹ * (y * t) by group]
        exact mul_mem (inv_mem hy) h)
      exact Or.inr ⟨hy, h1⟩
    · have h1 := (hAQ y y.2).resolve_left hy
      have h2 : (y : G) * t ∈ Q := by
        rw [show (y : G) * t = y * t⁻¹ * t ^ 2 by group]
        exact mul_mem h1 haQ
      exact Or.inl ⟨h2, hy⟩
  have hAQcard : Nat.card (A ⊓ Q : Subgroup G) = 8 := by
    have h1 := card_mul_index (Q.subgroupOf A)
    rw [hindex, hAcard] at h1
    have h2 : Nat.card (Q.subgroupOf A) = Nat.card (A ⊓ Q : Subgroup G) := by
      rw [← card_subtype A (Q.subgroupOf A), subgroupOf_map_subtype, inf_comm]
    omega
  have hAQcomm : IsMulCommutative (A ⊓ Q : Subgroup G) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have := congrArg Subtype.val (hAcomm ⟨x, (mem_inf.mp x.2).1⟩ ⟨y, (mem_inf.mp y.2).1⟩)
    simpa using this
  have hcommtq : ∀ q ∈ Q, t * (q⁻¹ * t * q) = q⁻¹ * t * q * t := by
    intro q hq
    have h1 : q⁻¹ * t * q ∈ CFSG.conjugate (zpowers t) q :=
      inv_mul_mul_mem_conjugate (mem_zpowers t)
    rcases htwo q hq with h | h
    · rw [h] at h1
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
      rw [← hk]
      exact ((Commute.refl t).zpow_right k).eq
    · rw [h] at h1
      exact hcommX t (mem_zpowers t) _ h1
  have hdQ : ∀ q ∈ Q, t⁻¹ * (q⁻¹ * t * q) ∈ Q := by
    intro q hq
    have h1 : t⁻¹ * q⁻¹ * t ∈ Q := (mem_normalizer_iff''.mp htN _).mp (inv_mem hq)
    rw [show t⁻¹ * (q⁻¹ * t * q) = t⁻¹ * q⁻¹ * t * q by group]
    exact mul_mem h1 hq
  have hdsq : ∀ q ∈ Q, (t⁻¹ * (q⁻¹ * t * q)) ^ 2 = (t ^ 2)⁻¹ * (q⁻¹ * t ^ 2 * q) := by
    intro q hq
    have h1 := hcommtq q hq
    have h2 : q⁻¹ * t * q * t⁻¹ = t⁻¹ * (q⁻¹ * t * q) := by
      calc q⁻¹ * t * q * t⁻¹ = t⁻¹ * (t * (q⁻¹ * t * q)) * t⁻¹ := by group
        _ = t⁻¹ * (q⁻¹ * t * q * t) * t⁻¹ := by rw [h1]
        _ = t⁻¹ * (q⁻¹ * t * q) := by group
    calc (t⁻¹ * (q⁻¹ * t * q)) ^ 2 = t⁻¹ * (q⁻¹ * t * q * t⁻¹) * (q⁻¹ * t * q) := by
          rw [pow_two]
          group
      _ = t⁻¹ * (t⁻¹ * (q⁻¹ * t * q)) * (q⁻¹ * t * q) := by rw [h2]
      _ = (t ^ 2)⁻¹ * (q⁻¹ * t ^ 2 * q) := by
          simp only [pow_two]
          group
  have hdinv : ∀ q ∈ Q, q⁻¹ * (t⁻¹ * (q⁻¹ * t * q)) * q = (t⁻¹ * (q⁻¹ * t * q))⁻¹ := by
    intro q hq
    have hq2 : (q * q) * t = t * (q * q) := by
      rcases hsq ⟨q, hq⟩ with h | h
      · change q ^ 2 = 1 at h
        rw [← pow_two, h, one_mul, mul_one]
      · change q ^ 2 = z at h
        rw [← pow_two, h]
        exact (hzc t htN).symm
    calc q⁻¹ * (t⁻¹ * (q⁻¹ * t * q)) * q = q⁻¹ * t⁻¹ * q * (q * q)⁻¹ * (t * (q * q)) := by
          group
      _ = q⁻¹ * t⁻¹ * q * (q * q)⁻¹ * (q * q * t) := by rw [hq2]
      _ = (t⁻¹ * (q⁻¹ * t * q))⁻¹ := by group
  have hconj_a : ∀ q ∈ Q, q⁻¹ * t ^ 2 * q = t ^ 2 ∨ q⁻¹ * t ^ 2 * q = t ^ 2 * z := by
    intro q hq
    have h1 := hcm ⟨(t ^ 2)⁻¹, inv_mem haQ⟩ ⟨q⁻¹, inv_mem hq⟩
    have h2 : ((⁅(⟨(t ^ 2)⁻¹, inv_mem haQ⟩ : Q), (⟨q⁻¹, inv_mem hq⟩ : Q)⁆ : Q) : G) =
        (t ^ 2)⁻¹ * q⁻¹ * t ^ 2 * q := by
      rw [show ((⁅(⟨(t ^ 2)⁻¹, inv_mem haQ⟩ : Q), (⟨q⁻¹, inv_mem hq⟩ : Q)⁆ : Q) : G) =
        ⁅(t ^ 2)⁻¹, q⁻¹⁆ from map_commutatorElement Q.subtype _ _, commutatorElement_def]
      simp
    rw [h2] at h1
    rcases h1 with h | h
    · left
      calc q⁻¹ * t ^ 2 * q = t ^ 2 * ((t ^ 2)⁻¹ * q⁻¹ * t ^ 2 * q) := by group
        _ = t ^ 2 := by rw [h, mul_one]
    · right
      calc q⁻¹ * t ^ 2 * q = t ^ 2 * ((t ^ 2)⁻¹ * q⁻¹ * t ^ 2 * q) := by group
        _ = t ^ 2 * z := by rw [h]
  have : IsElementaryAbelian 2 (Q ⧸ center Q) := hEA
  set b := commSignForm hzz' hz'o with hb
  set σ : MulAut Q := Q.normalizerMonoidHom ⟨t, htN⟩ with hσ
  have hσapp : ∀ x : Q, ((σ x : Q) : G) = t * x * t⁻¹ := fun x =>
    Q.normalizerMonoidHom_apply_apply_coe _ x
  set T : Module.End (ZMod 2) (Additive (Q ⧸ center Q)) :=
    CFSG.SignalizerFunctor.Helpers.elementaryAutomorphismEnd 2
      (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (center Q) σ) with hT
  have hTapp : ∀ x : Q, T (Additive.ofMul (x : Q ⧸ center Q)) =
      Additive.ofMul ((σ x : Q) : Q ⧸ center Q) := fun x => rfl
  have hV : ∀ v : Additive (Q ⧸ center Q), ∃ x : Q, v = Additive.ofMul (x : Q ⧸ center Q) := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨x, by rw [hx]; rfl⟩
  have hTT : T * T = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := hV v
    rw [Module.End.mul_apply, hTapp, hTapp, Module.End.one_apply]
    congr 1
    rw [QuotientGroup.eq]
    apply hmemZ
    have h1 : (((σ (σ x))⁻¹ * x : Q) : G) = ⁅t ^ 2, (x : G)⁻¹⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσapp, hσapp, commutatorElement_def]
      group
    rw [h1]
    have h2 := hcm ⟨t ^ 2, haQ⟩ x⁻¹
    rwa [show ((⁅(⟨t ^ 2, haQ⟩ : Q), x⁻¹⁆ : Q) : G) = ⁅t ^ 2, (x : G)⁻¹⁆ from
      map_commutatorElement Q.subtype _ _] at h2
  have hTinj : Function.Injective T := by
    intro v w h
    have h1 : T (T v) = T (T w) := by rw [h]
    rwa [← Module.End.mul_apply, hTT, Module.End.one_apply, ← Module.End.mul_apply, hTT,
      Module.End.one_apply] at h1
  have hfix : ∀ q : Q, T (Additive.ofMul (q : Q ⧸ center Q)) = Additive.ofMul (q : Q ⧸ center Q) →
      (q : G) * t = t * q := by
    intro q hTq
    let q' : Q := ⟨t⁻¹ * q * t, (mem_normalizer_iff''.mp htN _).mp q.2⟩
    have hTq' : T (Additive.ofMul (q' : Q ⧸ center Q)) = Additive.ofMul (q : Q ⧸ center Q) := by
      rw [hTapp]
      congr 2
      apply Subtype.ext
      rw [hσapp]
      change t * (t⁻¹ * q * t) * t⁻¹ = q
      group
    have h1 := hTinj (hTq.trans hTq'.symm)
    have h2 : (q : Q ⧸ center Q) = (q' : Q ⧸ center Q) := Additive.ofMul.injective h1
    rw [QuotientGroup.eq] at h2
    have hdZ : ∀ y : Q, (t⁻¹ * ((q : G)⁻¹ * t * q)) * y = y * (t⁻¹ * ((q : G)⁻¹ * t * q)) := by
      intro y
      have h3 := congrArg Subtype.val (mem_center_iff.mp (inv_mem h2) y)
      have h4 : (((q⁻¹ * q')⁻¹ : Q) : G) = t⁻¹ * ((q : G)⁻¹ * t * q) := by
        change ((q : G)⁻¹ * (t⁻¹ * q * t))⁻¹ = t⁻¹ * ((q : G)⁻¹ * t * q)
        group
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h4] at h3
      exact h3.symm
    rcases hconj_a q q.2 with ha | ha
    ·
      have hqN : (q : G) ∈ normalizer (zpowers t : Set G) := by
        rw [hNX, mem_centralizer_singleton_iff]
        calc (q : G) * t ^ 2 = q * ((q : G)⁻¹ * t ^ 2 * q) := by rw [ha]
          _ = t ^ 2 * q := by group
      have h5 : (q : G)⁻¹ * t * q ∈ zpowers t := by
        have := inv_mul_mul_mem_conjugate (H := zpowers t) (g := (q : G)) (mem_zpowers t)
        rwa [mem_normalizer_iff_conjugate_eq.mp hqN] at this
      have h6 : orderOf ((q : G)⁻¹ * t * q) = 4 := by
        rw [← ht]
        have h := MulEquiv.orderOf_eq (MulAut.conj (q : G)⁻¹) t
        rwa [MulAut.conj_apply, inv_inv] at h
      rcases eq_or_eq_of_mem_zpowers_of_orderOf_eq_four ht h5 h6 with h7 | h7
      · calc (q : G) * t = q * ((q : G)⁻¹ * t * q) := by rw [h7]
          _ = t * q := by group
      · exfalso
        apply hq₁ne
        have h8 : t⁻¹ * ((q : G)⁻¹ * t * q) = t ^ 2 := by
          rw [h7]
          group
        have h9 := hdZ ⟨q₁, hq₁⟩
        rw [h8] at h9
        exact h9
    ·
      exfalso
      apply hz1
      have h5 := hdsq q q.2
      rw [ha, show (t ^ 2)⁻¹ * (t ^ 2 * z) = z by group] at h5
      have h6 := hdinv q q.2
      have h7 : (q : G)⁻¹ * (t⁻¹ * ((q : G)⁻¹ * t * q)) * q = t⁻¹ * ((q : G)⁻¹ * t * q) := by
        rw [mul_assoc, hdZ q, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h7] at h6
      rw [← h5, pow_two]
      calc t⁻¹ * ((q : G)⁻¹ * t * q) * (t⁻¹ * ((q : G)⁻¹ * t * q)) =
          (t⁻¹ * ((q : G)⁻¹ * t * q))⁻¹ * (t⁻¹ * ((q : G)⁻¹ * t * q)) := by
            rw [← h6]
        _ = 1 := inv_mul_cancel _
  have hfixiff : ∀ v, T v = v ↔
      ∃ q : Q, (q : G) * t = t * q ∧ v = Additive.ofMul (q : Q ⧸ center Q) := by
    intro v
    constructor
    · intro hv
      obtain ⟨q, rfl⟩ := hV v
      exact ⟨q, hfix q hv, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      rw [hTapp]
      congr 2
      apply Subtype.ext
      rw [hσapp, ← hq]
      group
  have hT1 : T ≠ 1 := by
    intro h
    apply hq₁ne
    have h1 : T (Additive.ofMul ((⟨q₁, hq₁⟩ : Q) : Q ⧸ center Q)) =
        Additive.ofMul ((⟨q₁, hq₁⟩ : Q) : Q ⧸ center Q) := by
      rw [h]
      rfl
    have h2 : q₁ * t = t * q₁ := hfix _ h1
    calc t ^ 2 * q₁ = t * (t * q₁) := by rw [pow_two, mul_assoc]
      _ = t * (q₁ * t) := by rw [h2]
      _ = (t * q₁) * t := by rw [mul_assoc]
      _ = (q₁ * t) * t := by rw [h2]
      _ = q₁ * t ^ 2 := by rw [mul_assoc, ← pow_two]
  set CQt : Subgroup Q := (centralizer {t}).subgroupOf Q with hCQt
  have hZle : center Q ≤ CQt := fun c hc => by
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    exact (htZ c hc).symm
  let φ : CQt →* Q ⧸ center Q := (QuotientGroup.mk' (center Q)).comp CQt.subtype
  have hφrange : ∀ u : Q ⧸ center Q, u ∈ φ.range ↔
      Additive.ofMul u ∈ LinearMap.ker (T - 1) := by
    intro u
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · rintro ⟨c, rfl⟩
      have hc : ((c : Q) : G) * t = t * c :=
        mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp c.2)
      exact (hfixiff _).mpr ⟨c, hc, rfl⟩
    · intro hu
      obtain ⟨q, hq, hqu⟩ := (hfixiff _).mp hu
      exact ⟨⟨q, mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr hq)⟩,
        (Additive.ofMul.injective hqu).symm⟩
  have hφker : Nat.card φ.ker = Nat.card (center Q) := by
    have h : φ.ker = (center Q).subgroupOf CQt := by
      ext c
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    rw [h]
    exact Nat.card_congr (subgroupOfEquivOfLe hZle).toEquiv
  have hCQtcard : Nat.card CQt = Nat.card (center Q) * Nat.card (LinearMap.ker (T - 1)) := by
    have h1 : Nat.card φ.range = Nat.card (LinearMap.ker (T - 1)) :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul hφrange)
    rw [← hφker, ← h1, ← index_ker, card_mul_index]
  have hQcard : Nat.card Q = Nat.card (center Q) * Nat.card (Q ⧸ center Q) := by
    rw [card_eq_card_quotient_mul_card_subgroup (center Q), mul_comm]
  have hVcard : Nat.card (Q ⧸ center Q) =
      2 ^ Module.finrank (ZMod 2) (Additive (Q ⧸ center Q)) :=
    natCard_eq_two_pow_finrank (Additive (Q ⧸ center Q))
  have hKcard : Nat.card (LinearMap.ker (T - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (T - 1)) := natCard_eq_two_pow_finrank _
  have hrn := LinearMap.finrank_range_add_finrank_ker (T - 1)
  set m := Module.finrank (ZMod 2) (LinearMap.range (T - 1)) with hm
  have hidx : CQt.index = 2 ^ m := by
    have h1 := index_mul_card CQt
    rw [hCQtcard, hKcard, hQcard, hVcard, ← hrn, pow_add] at h1
    have hpos : 0 < Nat.card (center Q) * 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (T - 1)) :=
      Nat.mul_pos Nat.card_pos (by positivity)
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  have hinfcard : Nat.card (Q ⊓ centralizer {t} : Subgroup G) = Nat.card CQt := by
    rw [hCQt, ← card_subtype Q ((centralizer {t}).subgroupOf Q), subgroupOf_map_subtype, inf_comm]
  have hclass : Nat.card {x | ∃ q ∈ Q, x = q⁻¹ * t * q} = 2 ^ m := by
    rw [← hidx]
    have horbit := ComponentInitial.card_conj_orbit_mul_card_inf_centralizer Q t
    rw [hinfcard] at horbit
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (horbit.trans (index_mul_card CQt).symm)
  have hm0 : m ≠ 0 := by
    intro h0
    apply hT1
    have h1 : LinearMap.range (T - 1) = ⊥ := Submodule.finrank_eq_zero.mp (hm ▸ h0)
    exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp h1)
  have hm2 : m ≤ 2 := by
    have hsub : {x | ∃ q ∈ Q, x = q⁻¹ * t * q} ⊆
        (({t, t ^ 3, q₀⁻¹ * t * q₀, q₀⁻¹ * t ^ 3 * q₀} : Finset G) : Set G) := by
      rintro x ⟨q, hq, rfl⟩
      have h1 : q⁻¹ * t * q ∈ CFSG.conjugate (zpowers t) q :=
        inv_mul_mul_mem_conjugate (mem_zpowers t)
      have h6 : orderOf (q⁻¹ * t * q) = 4 := by
        rw [← ht]
        have h := MulEquiv.orderOf_eq (MulAut.conj q⁻¹) t
        rwa [MulAut.conj_apply, inv_inv] at h
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rcases htwo q hq with h | h
      · rw [h] at h1
        rcases eq_or_eq_of_mem_zpowers_of_orderOf_eq_four ht h1 h6 with h7 | h7
        · exact Or.inl h7
        · exact Or.inr (Or.inl h7)
      · rw [h] at h1
        have h8 : q₀ * (q⁻¹ * t * q) * q₀⁻¹ ∈ zpowers t := mem_conjugate_iff_conj_mem.mp h1
        have h9 : orderOf (q₀ * (q⁻¹ * t * q) * q₀⁻¹) = 4 := by
          rw [← h6]
          have h := MulEquiv.orderOf_eq (MulAut.conj q₀) (q⁻¹ * t * q)
          rwa [MulAut.conj_apply] at h
        have h10 : q⁻¹ * t * q = q₀⁻¹ * (q₀ * (q⁻¹ * t * q) * q₀⁻¹) * q₀ := by group
        rcases eq_or_eq_of_mem_zpowers_of_orderOf_eq_four ht h8 h9 with h7 | h7
        · exact Or.inr (Or.inr (Or.inl (by rw [h10, h7])))
        · exact Or.inr (Or.inr (Or.inr (by rw [h10, h7])))
    have hle : Nat.card {x | ∃ q ∈ Q, x = q⁻¹ * t * q} ≤ 4 := by
      rw [Nat.card_coe_set_eq]
      calc Set.ncard {x | ∃ q ∈ Q, x = q⁻¹ * t * q} ≤
          Set.ncard (({t, t ^ 3, q₀⁻¹ * t * q₀, q₀⁻¹ * t ^ 3 * q₀} : Finset G) : Set G) :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = Finset.card {t, t ^ 3, q₀⁻¹ * t * q₀, q₀⁻¹ * t ^ 3 * q₀} := Set.ncard_coe_finset _
        _ ≤ 4 := Finset.card_le_four
    rw [hclass] at hle
    by_contra h
    have h3 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hV2 : ∀ u : Q ⧸ center Q, u⁻¹ = u := fun u => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Q ⧸ center Q)) u
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  have hbT : ∀ v, b v ((T - 1) v) =
      b v (Additive.ofMul ((⟨t ^ 2, haQ⟩ : Q) : Q ⧸ center Q)) := by
    intro v
    obtain ⟨q, rfl⟩ := hV v
    set d : Q := ⟨t⁻¹ * ((q : G)⁻¹ * t * q), hdQ q q.2⟩ with hd
    let q'' : Q := ⟨t⁻¹ * (q : G)⁻¹ * t, (mem_normalizer_iff''.mp htN _).mp (inv_mem q.2)⟩
    have h1a : T (Additive.ofMul (q'' : Q ⧸ center Q)) = Additive.ofMul (q⁻¹ : Q ⧸ center Q) := by
      rw [hTapp]
      congr 2
      apply Subtype.ext
      rw [hσapp]
      change t * (t⁻¹ * (q : G)⁻¹ * t) * t⁻¹ = (q : G)⁻¹
      group
    have h1b : T (Additive.ofMul ((σ q⁻¹ : Q) : Q ⧸ center Q)) =
        Additive.ofMul (q⁻¹ : Q ⧸ center Q) := by
      rw [← hTapp, ← Module.End.mul_apply, hTT, Module.End.one_apply, QuotientGroup.mk_inv]
    have h2 : (q'' : Q ⧸ center Q) = ((σ q : Q) : Q ⧸ center Q)⁻¹ := by
      have h3 := Additive.ofMul.injective (hTinj (h1a.trans h1b.symm))
      rw [h3, map_inv, QuotientGroup.mk_inv]
    have hdq : (d : Q ⧸ center Q) = (q'' : Q ⧸ center Q) * (q : Q ⧸ center Q) := by
      rw [← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      change t⁻¹ * ((q : G)⁻¹ * t * q) = t⁻¹ * (q : G)⁻¹ * t * q
      group
    have hTd : (T - 1) (Additive.ofMul (q : Q ⧸ center Q)) = Additive.ofMul (d : Q ⧸ center Q) := by
      rw [LinearMap.sub_apply, Module.End.one_apply, hTapp, ← ofMul_div, hdq, h2, hV2,
        div_eq_mul_inv, hV2]
    rw [hTd, hb, commSignForm_apply, commSignForm_apply]
    have hiff : ⁅q, d⁆ = 1 ↔ ⁅q, (⟨t ^ 2, haQ⟩ : Q)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm, commutatorElement_eq_one_iff_mul_comm,
        Subtype.ext_iff, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_mul]
      change (q : G) * (t⁻¹ * ((q : G)⁻¹ * t * q)) = t⁻¹ * ((q : G)⁻¹ * t * q) * q ↔
        (q : G) * t ^ 2 = t ^ 2 * q
      have hdsq' := hdsq q q.2
      have hdinv' := hdinv q q.2
      constructor
      · intro h
        have h4 : (q : G)⁻¹ * (t⁻¹ * ((q : G)⁻¹ * t * q)) * q = t⁻¹ * ((q : G)⁻¹ * t * q) := by
          rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [h4] at hdinv'
        have h5 : (t⁻¹ * ((q : G)⁻¹ * t * q)) ^ 2 = 1 := by
          rw [pow_two]
          nth_rewrite 1 [hdinv']
          exact inv_mul_cancel _
        rw [hdsq'] at h5
        have h6 : (q : G)⁻¹ * t ^ 2 * q = t ^ 2 := by
          calc (q : G)⁻¹ * t ^ 2 * q = t ^ 2 * ((t ^ 2)⁻¹ * ((q : G)⁻¹ * t ^ 2 * q)) := by group
            _ = t ^ 2 := by rw [h5, mul_one]
        calc (q : G) * t ^ 2 = q * ((q : G)⁻¹ * t ^ 2 * q) := by rw [h6]
          _ = t ^ 2 * q := by group
      · intro h
        have h6 : (q : G)⁻¹ * t ^ 2 * q = t ^ 2 := by
          rw [mul_assoc, ← h]
          group
        rw [h6, inv_mul_cancel] at hdsq'
        have h7 : (t⁻¹ * ((q : G)⁻¹ * t * q))⁻¹ = t⁻¹ * ((q : G)⁻¹ * t * q) := by
          rw [pow_two] at hdsq'
          exact inv_eq_of_mul_eq_one_right hdsq'
        rw [h7] at hdinv'
        calc (q : G) * (t⁻¹ * ((q : G)⁻¹ * t * q)) =
            q * ((q : G)⁻¹ * (t⁻¹ * ((q : G)⁻¹ * t * q)) * q) := by rw [hdinv']
          _ = t⁻¹ * ((q : G)⁻¹ * t * q) * q := by group
    unfold commSign
    by_cases h : ⁅q, d⁆ = 1
    · simp only [h, hiff.mp h, ↓reduceIte]
    · have h' : ¬ ⁅q, (⟨t ^ 2, haQ⟩ : Q)⁆ = 1 := fun h' => h (hiff.mpr h')
      simp only [h, h', ↓reduceIte]
  have hbnz : ∃ v, b v (Additive.ofMul ((⟨t ^ 2, haQ⟩ : Q) : Q ⧸ center Q)) ≠ 0 := by
    refine ⟨Additive.ofMul ((⟨q₁, hq₁⟩ : Q) : Q ⧸ center Q), ?_⟩
    rw [hb, commSignForm_apply]
    intro h
    apply hq₁ne
    have h1 := commutatorElement_eq_one_iff_mul_comm.mp (commSign_eq_zero_iff.mp h)
    exact (congrArg Subtype.val h1).symm
  have hruleQ : ∀ x y : Q, ⁅x, y⁆ = z' ^ (b (Additive.ofMul (x : Q ⧸ center Q))
      (Additive.ofMul (y : Q ⧸ center Q))).val := by
    intro x y
    rw [hb, commSignForm_apply]
    exact commutatorElement_eq_pow_commSign hzz' x y
  have hruleG : ∀ x y : Q, ((⁅x, y⁆ : Q) : G) = z ^ (b (Additive.ofMul (x : Q ⧸ center Q))
      (Additive.ofMul (y : Q ⧸ center Q))).val := by
    intro x y
    rw [hruleQ x y, Subgroup.coe_pow]
  have huniq : ∀ b' : LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ center Q)),
      (∀ x y : Q, ((⁅x, y⁆ : Q) : G) = z ^ (b' (Additive.ofMul (x : Q ⧸ center Q))
        (Additive.ofMul (y : Q ⧸ center Q))).val) → b' = b := by
    intro b' hb'
    refine bilinForm_eq_of_commutator_rule hz'o hruleQ fun x y => ?_
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hb' x y
  have hTprop : ∀ x y : Q, (y : G) = t * x * t⁻¹ →
      T (Additive.ofMul (x : Q ⧸ center Q)) = Additive.ofMul (y : Q ⧸ center Q) := by
    intro x y hy
    rw [hTapp]
    congr 2
    apply Subtype.ext
    rw [hσapp, hy]
  refine ⟨htQ, ⟨hEA, b, hruleG, huniq, commSignForm_isAlt hzz' hz'o,
    commSignForm_nondegenerate hzz' hz'o, T, hTprop, hT1, hTT, hfixiff,
    ⟨m, rfl, hidx, by omega, hclass⟩, hbT, hbnz⟩,
    ⟨q₀, hq₀Q, hX₁ne, htwo, hcommX, hinf, hAeq⟩, ⟨hAiso⟩, hAeq ▸ hLN, hAQcard, hAQcomm,
    fun q hq => ⟨hdQ q hq, hdsq q hq, hdinv q hq⟩⟩

end CFSG.LocalAnalysis.GorensteinLyons
