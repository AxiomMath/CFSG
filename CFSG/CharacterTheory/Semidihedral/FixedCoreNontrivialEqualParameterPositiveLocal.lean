module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterLocal
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusOvergroup
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositiveTorus

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

namespace Positive

variable {G : Type*} [Group G]

theorem mem_of_pow_eq_one_of_mem_sup_of_coprime [Finite G] {W Z : Subgroup G}
    (hWZ : ∀ w ∈ W, ∀ z ∈ Z, w * z = z * w) (hcop : Nat.Coprime (Nat.card W) (Nat.card Z))
    {v : G} (hv : v ∈ W ⊔ Z) {m : ℕ} (hm : Nat.Coprime m (Nat.card Z)) (hvm : v ^ m = 1) :
    v ∈ W := by
  obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_sup hWZ hv
  have hc : Commute w z := hWZ w hw z hz
  have hzm : z ^ m ∈ W := by
    have : z ^ m = (w ^ m)⁻¹ := by
      rw [hc.mul_pow] at hvm
      exact eq_inv_of_mul_eq_one_right hvm
    rw [this]
    exact W.inv_mem (W.pow_mem hw m)
  have hzm1 : z ^ m = 1 := by
    have hmem : z ^ m ∈ W ⊓ Z := Subgroup.mem_inf.mpr ⟨hzm, Z.pow_mem hz m⟩
    rwa [(Subgroup.disjoint_of_coprime_natCard hcop).eq_bot, Subgroup.mem_bot] at hmem
  have h1 : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hzm1
  have h2 : orderOf z ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hz
  rw [orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hm h1 h2), mul_one]
  exact hw

theorem exists_two_point_generator {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (x₀ : Omega K) :
    ∃ y₀ : Omega K, ∃ τ : Equiv.Perm (Omega K), x₀ ≠ y₀ ∧ τ ∈ coordinateD K ∧
      τ ∉ coordinateG K ∧ τ x₀ = x₀ ∧ τ y₀ = y₀ ∧ orderOf τ = Nat.card K - 1 ∧
      ∀ z ∈ coordinateD K, z x₀ = x₀ → z y₀ = y₀ → z ∈ Subgroup.zpowers τ := by
  classical
  obtain ⟨y₀, hxy⟩ : ∃ y₀ : Omega K, x₀ ≠ y₀ := by
    cases x₀ with
    | none => exact ⟨some 0, (Option.some_ne_none (0 : K)).symm⟩
    | some a => exact ⟨none, Option.some_ne_none a⟩
  obtain ⟨g, hgG, hgx, hgy⟩ := CFSG.Semidihedral.Principal.exists_coordinateG_infinity_zero hxy
  have hgx' : g⁻¹ x₀ = none := Equiv.Perm.inv_eq_iff_eq.mpr hgx.symm
  have hgy' : g⁻¹ y₀ = some 0 := Equiv.Perm.inv_eq_iff_eq.mpr hgy.symm
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgD : g ∈ coordinateD K := Subgroup.subset_closure (Or.inl hgG)
  have hmD : multiplier K μ ∈ coordinateD K := Subgroup.subset_closure (Or.inr ⟨μ, rfl⟩)
  have hinj : Function.Injective (CFSG.Semidihedral.UnitaryBranch.multiplierHom K) := by
    intro a b hab
    have h1 := congrArg (fun e : Equiv.Perm (Omega K) => e (some 1)) hab
    change multiplier K a (some 1) = multiplier K b (some 1) at h1
    rw [multiplier_some, multiplier_some, mul_one, mul_one] at h1
    exact Units.ext (Option.some_injective _ h1)
  have hμord : orderOf μ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_units]
  have hmord : orderOf (multiplier K μ) = Nat.card K - 1 := by
    rw [← hμord]
    exact orderOf_injective _ hinj μ
  have hK3 : 3 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    obtain ⟨k, hk⟩ := hodd
    omega
  refine ⟨y₀, g * multiplier K μ * g⁻¹, hxy, mul_mem (mul_mem hgD hmD) (inv_mem hgD), ?_, ?_, ?_,
    ?_, ?_⟩
  · intro hτG
    have hmG : multiplier K μ ∈ coordinateG K := by
      have e : multiplier K μ = g⁻¹ * (g * multiplier K μ * g⁻¹) * g := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hgG) hτG) hgG
    rw [multiplier_mem_coordinateG_iff] at hmG
    obtain ⟨r, hr⟩ := hmG
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact μ.ne_zero hr
    have hμr : μ = Units.mk0 r hr0 * Units.mk0 r hr0 := Units.ext (by simp [hr])
    have hpow : μ ^ ((Nat.card K - 1) / 2) = 1 := by
      have h2 : 2 * ((Nat.card K - 1) / 2) = Nat.card K - 1 := by
        obtain ⟨k, hk⟩ := hodd
        omega
      rw [hμr, ← pow_two, ← pow_mul, h2, ← Nat.card_units]
      exact pow_card_eq_one'
    have hle := orderOf_le_of_pow_eq_one (by omega) hpow
    omega
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgx', multiplier_none, hgx]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgy', multiplier_some, mul_zero, hgy]
  · rw [← hmord]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
  · intro z hzD hzx hzy
    have hz'D : g⁻¹ * z * g ∈ coordinateD K := mul_mem (mul_mem (inv_mem hgD) hzD) hgD
    have hz'inf : (g⁻¹ * z * g) none = none := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgx, hzx, hgx']
    have hz'0 : (g⁻¹ * z * g) (some 0) = some 0 := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgy, hzy, hgy']
    obtain ⟨ν, hν⟩ := eq_multiplier_of_fixes_infty_zero hz'D hz'inf hz'0
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hμ ν)
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have hmi : multiplier K ν = (multiplier K μ) ^ i := by
      rw [← hi]
      exact map_zpow (CFSG.Semidihedral.UnitaryBranch.multiplierHom K) μ i
    rw [conj_zpow, ← hmi, ← hν]
    group

end Positive

open _root_.CFSG.Semidihedral.FixedCoreNontrivial.Positive

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem layer_le_of_not_le_normalizer
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 1) {X : Subgroup G} (hXC : X ≤ C t) (hWX : torusW G t s₀ ≤ X)
    (hBX : (N t).map (C t).subtype ≤ X) (htX : t ∈ X)
    (hX : ¬ X ≤ Subgroup.normalizer ((torusW G t s₀ : Subgroup G) : Set G)) : J ≤ X := by
  have hL := h.localData
  obtain ⟨hWcyc, -, -, -, hBK, -⟩ := h.clauses
  obtain ⟨hw, -⟩ := h.card_W_B.1 he
  obtain ⟨hWC, -⟩ := clause_facts h
  set W := torusW G t s₀ with hWdef
  set B := (N t).map (C t).subtype with hBdef
  have hcop : Nat.Coprime (Nat.card W) (Nat.card B * 2) :=
    Nat.Coprime.mul_right h.card_W_B_arith.2.2 (Nat.coprime_two_right.mpr h.odd_card_W)
  set Cb := (W.subgroupOf (C t)).map κ with hCb
  have hCbcard : Nat.card Cb = (Nat.card F + 1) / 2 := by
    rw [h.card_map_κ_of_coprime hWC hcop, h.card_F]
    omega
  have hCbcyc : IsCyclic Cb := by
    have : IsCyclic (W.subgroupOf (C t)) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWC).symm.toMonoidHom
        (MulEquiv.surjective _)
    exact isCyclic_of_surjective (κ.subgroupMap _) (κ.subgroupMap_surjective _)
  set X' := (X.subgroupOf (C t)).map κ with hX'
  have hCbX' : Cb ≤ X' := Subgroup.map_mono (Subgroup.comap_mono hWX)
  have hX'D : X' ≤ coordinateD F := by
    rw [← h.range_κ]
    exact Subgroup.map_le_range κ _
  have hq13 : 13 ≤ Nat.card F := by
    rw [h.card_F]
    have := h.q_gt
    omega
  have hq4 : Nat.card F % 4 = 1 := by
    rw [h.card_F]
    exact he
  rcases le_normalizer_or_coordinateG_le h.prime h.odd h.card_F hq4 hq13 Cb X' hCbX' hX'D hCbcyc
    hCbcard with hN | hG
  ·
    exfalso
    apply hX
    intro c hc
    apply mem_normalizer_of_conj_mem
    intro w hw'
    have hcC := hXC hc
    have hwC := hWC hw'
    have hcwC : c * w * c⁻¹ ∈ C t := (C t).mul_mem ((C t).mul_mem hcC hwC) ((C t).inv_mem hcC)
    have hκ : κ ⟨c * w * c⁻¹, hcwC⟩ ∈ Cb := by
      have hκc : κ ⟨c, hcC⟩ ∈ Subgroup.normalizer (Cb : Set (Equiv.Perm (Omega F))) :=
        hN ⟨⟨c, hcC⟩, hc, rfl⟩
      have hκw : κ ⟨w, hwC⟩ ∈ Cb := ⟨⟨w, hwC⟩, hw', rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp hκc _).mp hκw
      have h2 : κ ⟨c * w * c⁻¹, hcwC⟩ = κ ⟨c, hcC⟩ * κ ⟨w, hwC⟩ * (κ ⟨c, hcC⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h2]
      exact h1
    have hmem := h.mem_sup_ker_of_κ_mem (M := W) hκ
    have hZW : ∀ x ∈ W, ∀ z ∈ B ⊔ Subgroup.zpowers t, x * z = z * x := by
      intro x hx z hz
      have htK : t ∈ Subgroup.centralizer (W : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (hWC hy)
      have hzK : z ∈ Subgroup.centralizer (W : Set G) :=
        (sup_le hBK (Subgroup.zpowers_le.mpr htK) :
          B ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer (W : Set G)) hz
      exact (Subgroup.mem_centralizer_iff.mp hzK x hx)
    have hcopZ : Nat.Coprime (Nat.card W) (Nat.card (B ⊔ Subgroup.zpowers t : Subgroup G)) := by
      rw [h.card_B_sup_t]
      exact hcop
    refine mem_of_pow_eq_one_of_mem_sup_of_coprime hZW hcopZ hmem hcopZ ?_
    rw [conj_pow, orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard W hw'), mul_one,
      mul_inv_cancel]
  · intro j hj
    have hjC : j ∈ C t := hL.J_le hj
    have hκj : κ ⟨j, hjC⟩ ∈ coordinateG F :=
      (h.mem_coordinateG_iff ⟨j, hjC⟩).mpr (Subgroup.mem_sup_left hj)
    exact h.mem_of_κ_mem_map (sup_le hBX (Subgroup.zpowers_le.mpr htX)) (hG hκj)

theorem layer_torus_element (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 1) {c : C t} (hcG : κ c ∉ coordinateG F)
    (hcord : orderOf (κ c) = p ^ f - 1) :
    (c : G) * c ∈ J ∧ (c : G) ^ (p ^ f - 1) = t ∧ orderOf (c : G) = 2 * (p ^ f - 1) ∧
      ∀ b ∈ (N t).map (C t).subtype, (c : G) * b * (c : G)⁻¹ = b⁻¹ := by
  have hL := h.localData
  obtain ⟨-, hb⟩ := h.card_W_B.1 he
  set B := (N t).map (C t).subtype with hBdef
  set n := p ^ f - 1 with hndef
  have hn : n = 4 * Nat.card B := by omega
  have hB1 : 0 < Nat.card B := Nat.card_pos
  have hcJB : (c : G) ∉ J ⊔ B := fun hc => hcG ((h.mem_coordinateG_iff c).mpr hc)
  have hinvB : ∀ b ∈ B, (c : G) * b * (c : G)⁻¹ = b⁻¹ := fun b hb =>
    h.conj_eq_inv_of_not_mem_sup c.2 hcJB hb
  have hc2 : (c : G) * c ∈ J := by
    have hκ2 : κ (c * c) ∈ coordinateG F := by
      rw [map_mul]
      apply CFSG.Semidihedral.Principal.mul_self_mem_coordinateG
      rw [← h.range_κ]
      exact ⟨c, rfl⟩
    have hmem : ((c * c : C t) : G) ∈ J ⊔ B := (h.mem_coordinateG_iff (c * c)).mp hκ2
    obtain ⟨j, hj, b, hb, hjb⟩ := exists_mul_of_mem_sup hL.JB_comm hmem
    have hjb' : (c : G) * c = j * b := hjb
    have hcj : (c : G) * j * (c : G)⁻¹ ∈ J := hL.J_conj c c.2 j hj
    have heq : (c : G) * (j * b) * (c : G)⁻¹ = j * b := by
      rw [← hjb']
      group
    have h1 : (c : G) * j * (c : G)⁻¹ * b⁻¹ = j * b := by
      calc (c : G) * j * (c : G)⁻¹ * b⁻¹ = (c : G) * j * (c : G)⁻¹ * ((c : G) * b * (c : G)⁻¹) := by
            rw [hinvB b hb]
        _ = (c : G) * (j * b) * (c : G)⁻¹ := by group
        _ = j * b := heq
    have h2 : j⁻¹ * ((c : G) * j * (c : G)⁻¹) = b * b := by
      calc j⁻¹ * ((c : G) * j * (c : G)⁻¹) = j⁻¹ * ((c : G) * j * (c : G)⁻¹ * b⁻¹) * b := by group
        _ = j⁻¹ * (j * b) * b := by rw [h1]
        _ = b * b := by group
    have hbb : b * b = 1 := by
      have hmem2 : b * b ∈ J ⊓ B := Subgroup.mem_inf.mpr
        ⟨h2 ▸ J.mul_mem (J.inv_mem hj) hcj, B.mul_mem hb hb⟩
      rwa [hL.JB_disj, Subgroup.mem_bot] at hmem2
    rw [hjb', eq_one_of_mul_self_eq_one_of_odd (hL.B_odd b hb) hbb, mul_one]
    exact hj
  have hcpow : ∀ k : ℕ, (c : G) ^ (2 * k) ∈ J := fun k => by
    rw [pow_mul, pow_two]
    exact J.pow_mem hc2 k
  have hcnJ : (c : G) ^ n ∈ J := by
    rw [show n = 2 * (2 * Nat.card B) by omega]
    exact hcpow _
  have hcnker : ((c ^ n : C t) : G) ∈ B ⊔ Subgroup.zpowers t := by
    apply (h.mem_ker_κ_iff (c ^ n)).mp
    rw [map_pow, ← hcord, pow_orderOf_eq_one]
  have hBt : ∀ x ∈ B, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.map_subtype_le _) hx)) k)
  have hcn : (c : G) ^ n = 1 ∨ (c : G) ^ n = t := by
    have hcnker' : (c : G) ^ n ∈ B ⊔ Subgroup.zpowers t := hcnker
    obtain ⟨b, hb, u, hu, hbu⟩ := exists_mul_of_mem_sup hBt hcnker'
    have hu' := zpowers_cases_of_mul_self hL.t_sq u hu
    have huJ : u ∈ J := by
      rcases hu' with rfl | rfl
      · exact J.one_mem
      · exact hL.t_mem
    have hbJ : b ∈ J := by
      have : b = (c : G) ^ n * u⁻¹ := by rw [hbu]; group
      rw [this]
      exact J.mul_mem hcnJ (J.inv_mem huJ)
    have hb1 : b = 1 := by
      have hmem2 : b ∈ J ⊓ B := Subgroup.mem_inf.mpr ⟨hbJ, hb⟩
      rwa [hL.JB_disj, Subgroup.mem_bot] at hmem2
    rw [hbu, hb1, one_mul]
    exact hu'
  have hcnt : (c : G) ^ n = t := by
    rcases hcn with h1 | h1
    · exfalso
      have hvJ : (c : G) ^ (2 * Nat.card B) ∈ J := hcpow _
      have hvv : (c : G) ^ (2 * Nat.card B) * (c : G) ^ (2 * Nat.card B) = 1 := by
        rw [← pow_add, show 2 * Nat.card B + 2 * Nat.card B = n by omega, h1]
      have hκv : κ (c ^ (2 * Nat.card B)) ≠ 1 := by
        rw [map_pow]
        exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hcord]; omega)
      rcases hL.J_inv _ hvJ hvv with hv1 | hvt
      · apply hκv
        have : c ^ (2 * Nat.card B) = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hv1)
        rw [this, map_one]
      · apply hκv
        apply (h.mem_ker_κ_iff _).mpr
        rw [SubgroupClass.coe_pow, hvt]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    · exact h1
  have hord : orderOf (c : G) = 2 * n := by
    have hdvd1 : orderOf (c : G) ∣ 2 * n := by
      apply orderOf_dvd_of_pow_eq_one
      rw [mul_comm, pow_mul, hcnt, pow_two, hL.t_sq]
    have hdvd2 : n ∣ orderOf (c : G) := by
      rw [← hcord, Subgroup.orderOf_coe]
      exact orderOf_map_dvd κ c
    obtain ⟨k, hk⟩ := hdvd2
    have hn0 : 0 < n := by omega
    have hk2 : k ∣ 2 := by
      rw [hk, mul_comm 2 n] at hdvd1
      exact (Nat.mul_dvd_mul_iff_left hn0).mp hdvd1
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with hk1 | hk2'
    · exfalso
      rw [hk1, mul_one] at hk
      have h1 : (c : G) ^ n = 1 := by
        rw [← hk]
        exact pow_orderOf_eq_one _
      rw [hcnt] at h1
      exact hL.t_ne_one h1
    · rw [hk, hk2', mul_comm]
  exact ⟨hc2, hcnt, hord, hinvB⟩

theorem exists_layer_torus (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 1) {Q₁ : Subgroup G} (hQ₁ : IsSylowOf p Q₁ (C t)) :
    ∃ Y O : Subgroup G, Y ≤ C t ⊓ Subgroup.normalizer (Q₁ : Set G) ∧ IsCyclic Y ∧
      Nat.card Y = 2 * (p ^ f - 1) ∧ t ∈ Y ∧ Disjoint Y ((N t).map (C t).subtype) ∧
      C t ⊓ Subgroup.normalizer (Q₁ : Set G) = Q₁ ⊔ Y ⊔ (N t).map (C t).subtype ∧
      O ≤ Y ∧ O ≤ J ∧ Nat.card O = Nat.card ((N t).map (C t).subtype) ∧
      (∀ y ∈ O, ∀ x ∈ (N t).map (C t).subtype, y * x = x * y) ∧
      Nat.card (O ⊔ (N t).map (C t).subtype : Subgroup G) =
        Nat.card ((N t).map (C t).subtype) ^ 2 ∧
      ∀ E : Subgroup G, E ≤ O ⊔ (N t).map (C t).subtype → ¬ E ≤ (N t).map (C t).subtype →
        ∀ c ∈ C t ⊓ Subgroup.normalizer (E : Set G), Odd (orderOf c) →
          c ∈ O ⊔ (N t).map (C t).subtype := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hL := h.localData
  obtain ⟨-, hb⟩ := h.card_W_B.1 he
  set B := (N t).map (C t).subtype with hBdef
  set n := p ^ f - 1 with hndef
  have hn : n = 4 * Nat.card B := by omega
  have hbodd : Odd (Nat.card B) := h.odd_card_B
  have hBC : B ≤ C t := Subgroup.map_subtype_le _
  have hBt : ∀ x ∈ B, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hBC hx)) k
  obtain ⟨hQ₁card, hQ₁J, -, -, -⟩ := h.sylow_C_facts hQ₁
  have hκD : ∀ X : Subgroup (C t), X.map κ ≤ coordinateD F := fun X => by
    rw [← h.range_κ]
    exact Subgroup.map_le_range κ X
  set Q₁' := (Q₁.subgroupOf (C t)).map κ with hQ₁'def
  have hQ₁'card : Nat.card Q₁' = p ^ f := by
    rw [h.card_map_κ_of_coprime hQ₁.le (h.coprime_of_isPGroup hQ₁.isPGroup), hQ₁card]
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
  have hQ₁'1 : Q₁' ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hQ₁'card]
    exact hq1
  obtain ⟨x₀, hx₀, -⟩ := existsUnique_fixed_of_isPGroup h.prime h.odd h.card_F (hκD _)
    ((hQ₁.isPGroup.comap_subtype (K := C t)).map κ) hQ₁'1
  have hFodd : Odd (Nat.card F) := by
    rw [h.card_F]
    exact h.odd.pow
  obtain ⟨y₀, τ, hxy, hτD, hτG, hτx, hτy, hτord, hτgen⟩ := exists_two_point_generator hFodd x₀
  obtain ⟨c, hc⟩ : ∃ c : C t, κ c = τ := by
    rw [← h.range_κ] at hτD
    exact hτD
  have hcord : orderOf (κ c) = n := by rw [hc, hτord, h.card_F]
  obtain ⟨hc2, hcn, hcorder, hcinv⟩ := h.layer_torus_element he (by rw [hc]; exact hτG) hcord
  set Y := Subgroup.zpowers (c : G) with hYdef
  set O := Subgroup.zpowers ((c : G) ^ 8) with hOdef
  have hYC : Y ≤ C t := Subgroup.zpowers_le.mpr c.2
  have hcN : (c : G) ∈ Subgroup.normalizer (Q₁ : Set G) :=
    (h.mem_normalizer_sylow_iff hQ₁ hx₀ c).mpr (by rw [hc]; exact hτx)
  have hYN : Y ≤ Subgroup.normalizer (Q₁ : Set G) := Subgroup.zpowers_le.mpr hcN
  have hYcard : Nat.card Y = 2 * n := by rw [Nat.card_zpowers, hcorder]
  have htY : t ∈ Y := by
    rw [← hcn]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n
  have hYB : Disjoint Y B := by
    rw [Subgroup.disjoint_def]
    intro x hxY hxB
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxY
    have h1 : (c : G) * (c : G) ^ k * (c : G)⁻¹ = (c : G) ^ k := by
      rw [(Commute.zpow_right (Commute.refl (c : G)) k).eq, mul_inv_cancel_right]
    have h2 := hcinv _ hxB
    rw [h1] at h2
    have h3 : (c : G) ^ k * (c : G) ^ k = 1 := by
      calc (c : G) ^ k * (c : G) ^ k = (c : G) ^ k * ((c : G) ^ k)⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel _
    exact eq_one_of_mul_self_eq_one_of_odd (hL.B_odd _ hxB) h3
  have hOY : O ≤ Y := Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 8)
  have hOJ : O ≤ J := by
    rw [Subgroup.zpowers_le, show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, pow_two]
    exact J.pow_mem hc2 4
  have hOcard : Nat.card O = Nat.card B := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num)
      (Dvd.intro (Nat.card B) (by rw [hcorder]; omega)), hcorder]
    omega
  have hOB : ∀ y ∈ O, ∀ x ∈ B, y * x = x * y := fun y hy x hx => hL.JB_comm y (hOJ hy) x hx
  have hYNB : Y ≤ Subgroup.normalizer (B : Set G) := fun y hy =>
    mem_normalizer_of_conj_mem (fun x hx => hL.B_conj y (hYC hy) x hx)
  have hXcard : Nat.card (O ⊔ B : Subgroup G) = Nat.card B ^ 2 := by
    rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B O
      (hOY.trans hYNB) (hYB.symm.mono_right hOY), hOcard, pow_two]
  have hBN₁ : B ≤ Subgroup.normalizer (Q₁ : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem (fun y hy => by
      rw [← hL.JB_comm y (hQ₁J hy) x hx, mul_inv_cancel_right]
      exact hy)
  have hYM : Y ≤ Q₁ ⊔ Y ⊔ B := (le_sup_right : Y ≤ Q₁ ⊔ Y).trans le_sup_left
  have hMle : Q₁ ⊔ Y ⊔ B ≤ C t ⊓ Subgroup.normalizer (Q₁ : Set G) :=
    sup_le (sup_le (le_inf hQ₁.le Subgroup.le_normalizer) (le_inf hYC hYN)) (le_inf hBC hBN₁)
  have hkerM : B ⊔ Subgroup.zpowers t ≤ Q₁ ⊔ Y ⊔ B :=
    sup_le le_sup_right (Subgroup.zpowers_le.mpr (hYM htY))
  have hNeq : C t ⊓ Subgroup.normalizer (Q₁ : Set G) = Q₁ ⊔ Y ⊔ B := by
    refine le_antisymm ?_ hMle
    rintro c' ⟨hc'C, hc'N⟩
    set M' := ((Q₁ ⊔ Y ⊔ B).subgroupOf (C t)).map κ with hM'def
    set St := coordinateD F ⊓ MulAction.stabilizer (Equiv.Perm (Omega F)) x₀ with hStdef
    have hM'St : M' ≤ St := by
      rintro _ ⟨m, hm, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hκD _ ⟨m, hm, rfl⟩, ?_⟩
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact (h.mem_normalizer_sylow_iff hQ₁ hx₀ m).mp (hMle hm).2
    have hStcard : Nat.card St = p ^ f * (p ^ f - 1) := by
      rw [card_coordinateD_inf_stabilizer, h.card_F]
    have hM'card : p ^ f * (p ^ f - 1) ≤ Nat.card M' := by
      have hQ₁M' : Q₁' ≤ M' :=
        Subgroup.map_mono (Subgroup.comap_mono (le_sup_left.trans le_sup_left))
      have hYM' : Subgroup.zpowers τ ≤ M' := by
        rw [Subgroup.zpowers_le, ← hc]
        exact ⟨c, hYM (Subgroup.mem_zpowers _), rfl⟩
      have h1 : p ^ f ∣ Nat.card M' := hQ₁'card ▸ Subgroup.card_dvd_of_le hQ₁M'
      have h2 : p ^ f - 1 ∣ Nat.card M' := by
        have := Subgroup.card_dvd_of_le hYM'
        rwa [Nat.card_zpowers, hτord, h.card_F] at this
      have hcop : Nat.Coprime (p ^ f) (p ^ f - 1) :=
        (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_one_right _)
      exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2)
    have hM'eq : M' = St := Subgroup.eq_of_le_of_card_ge hM'St (by rw [hStcard]; exact hM'card)
    have hκc' : κ ⟨c', hc'C⟩ ∈ M' := by
      rw [hM'eq]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← h.range_κ]
        exact ⟨_, rfl⟩
      · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
        exact (h.mem_normalizer_sylow_iff hQ₁ hx₀ ⟨c', hc'C⟩).mp hc'N
    exact h.mem_of_κ_mem_map hkerM hκc'
  refine ⟨Y, O, le_inf hYC hYN, inferInstance, hYcard, htY, hYB, hNeq, hOY, hOJ, hOcard, hOB,
    hXcard, ?_⟩
  intro E hEX hEB c' hc' hc'odd
  obtain ⟨hc'C, hc'N⟩ := Subgroup.mem_inf.mp hc'
  have hEC : E ≤ C t := hEX.trans (sup_le (hOY.trans hYC) hBC)
  set E' := (E.subgroupOf (C t)).map κ with hE'def
  have hfix : ∀ e : C t, (e : G) ∈ Y ⊔ B → κ e x₀ = x₀ ∧ κ e y₀ = y₀ := by
    intro e he
    have he' : (e : G) ∈ ((Y : Set G) * (B : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y B hYNB]
      exact he
    obtain ⟨y, hy, b, hb, hyb⟩ := he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hbker : κ ⟨b, hBC hb⟩ = 1 := (h.mem_ker_κ_iff _).mpr (Subgroup.mem_sup_left hb)
    have he_eq : e = c ^ k * ⟨b, hBC hb⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, SubgroupClass.coe_zpow]; exact hyb.symm)
    rw [he_eq, map_mul, hbker, mul_one, map_zpow, hc]
    exact ⟨Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hτx k,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hτy k⟩
  have hE'fix : ∀ g ∈ E', g x₀ = x₀ ∧ g y₀ = y₀ := by
    rintro _ ⟨e, he, rfl⟩
    exact hfix e (sup_le_sup_right hOY B (hEX he))
  have hXodd : Odd (Nat.card (O ⊔ B : Subgroup G)) := by
    rw [hXcard]
    exact hbodd.pow
  have hE'1 : E' ≠ ⊥ := by
    intro hbot
    apply hEB
    intro e he
    have hκe : κ ⟨e, hEC he⟩ = 1 := by
      have hmem : κ ⟨e, hEC he⟩ ∈ E' := ⟨⟨e, hEC he⟩, he, rfl⟩
      rw [hbot] at hmem
      exact hmem
    have hker := (h.mem_ker_κ_iff _).mp hκe
    have heodd : Odd (orderOf e) := odd_orderOf_of_mem hXodd (hEX he)
    have hcopBt : Nat.Coprime (Nat.card B) (Nat.card (Subgroup.zpowers t)) := by
      rw [Nat.card_zpowers, hL.t_orderOf]
      exact Nat.coprime_two_right.mpr hbodd
    exact mem_of_pow_eq_one_of_mem_sup_of_coprime hBt hcopBt hker
      (by rw [Nat.card_zpowers, hL.t_orderOf]; exact Nat.coprime_two_right.mpr heodd)
      (pow_orderOf_eq_one e)
  have hnorm : κ ⟨c', hc'C⟩ ∈ Subgroup.normalizer (E' : Set (Equiv.Perm (Omega F))) := by
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨e, he, rfl⟩
    refine ⟨⟨c', hc'C⟩ * e * ⟨c', hc'C⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp hc'N e).mp he
  have hpair := mem_pair_of_mem_normalizer hxy (hκD _) (fun g hg => (hE'fix g hg).1)
    (fun g hg => (hE'fix g hg).2) hE'1 hnorm
  have hκodd : Odd (orderOf (κ ⟨c', hc'C⟩)) :=
    Odd.of_dvd_nat (by rwa [Subgroup.orderOf_mk]) (orderOf_map_dvd κ _)
  obtain ⟨hκx, hκy⟩ := fixes_of_odd_of_pair hxy hκodd hpair
  have hκτ : κ ⟨c', hc'C⟩ ∈ Subgroup.zpowers τ :=
    hτgen _ (by rw [← h.range_κ]; exact ⟨_, rfl⟩) hκx hκy
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hκτ
  have hκY : κ ⟨c', hc'C⟩ ∈ (Y.subgroupOf (C t)).map κ := by
    refine ⟨c ^ i, ?_, by rw [map_zpow, hc, hi]⟩
    show ((c ^ i : C t) : G) ∈ Y
    rw [SubgroupClass.coe_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) i
  have hc'YB : c' ∈ Y ⊔ B :=
    (sup_le le_sup_left
      (sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left htY))) :
      Y ⊔ (B ⊔ Subgroup.zpowers t) ≤ Y ⊔ B) (h.mem_sup_ker_of_κ_mem hκY)
  have hc'YB' : c' ∈ ((Y : Set G) * (B : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y B hYNB]
    exact hc'YB
  obtain ⟨y, hy, b, hb, rfl⟩ := hc'YB'
  have hpow : ∀ k : ℕ, ∃ bk ∈ B, (y * b) ^ k = y ^ k * bk := by
    intro k
    induction k with
    | zero => exact ⟨1, B.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨bk, hbk, hk⟩ := ih
      refine ⟨y⁻¹ * bk * y * b, B.mul_mem ?_ hb, ?_⟩
      · have := hL.B_conj y⁻¹ ((C t).inv_mem (hYC hy)) bk hbk
        rwa [inv_inv] at this
      · rw [pow_succ, hk, pow_succ]
        group
  obtain ⟨bm, hbm, hm⟩ := hpow (orderOf (y * b))
  have hym : y ^ orderOf (y * b) = 1 := by
    have h1 : y ^ orderOf (y * b) * bm = 1 := by
      rw [← hm]
      exact pow_orderOf_eq_one _
    have h2 : y ^ orderOf (y * b) ∈ Y ⊓ B := Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ hy _,
      by rw [eq_inv_of_mul_eq_one_left h1]; exact B.inv_mem hbm⟩
    rwa [hYB.eq_bot, Subgroup.mem_bot] at h2
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat hc'odd (orderOf_dvd_of_pow_eq_one hym)
  have hyO : y ∈ O := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h8b : orderOf (c : G) = Nat.card B * 2 ^ 3 := by rw [hcorder]; omega
    have hdvd : orderOf ((c : G) ^ k) ∣ Nat.card B := by
      have h1 := orderOf_dvd_of_mem_zpowers hy
      rw [h8b] at h1
      exact Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hyodd)) h1
    have h1 : (c : G) ^ (k * (Nat.card B : ℤ)) = 1 := by
      rw [zpow_mul, zpow_natCast]
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    have hcast : ((Nat.card B * 2 ^ 3 : ℕ) : ℤ) = 8 * (Nat.card B : ℤ) := by
      push_cast
      ring
    rw [h8b, hcast] at h2
    have h3 : (8 : ℤ) ∣ k := by
      have hb0 : (Nat.card B : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
      exact (mul_dvd_mul_iff_right hb0).mp h2
    obtain ⟨j, rfl⟩ := h3
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  exact Subgroup.mul_mem_sup hyO hb

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
