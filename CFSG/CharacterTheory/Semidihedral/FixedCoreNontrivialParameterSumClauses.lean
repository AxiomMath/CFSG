module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumBasic
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialDGroup

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

@[expose] def torusPsi {G : Type} [Group G] {t s₀ : G} {F' : Type} [Field F'] [Finite F']
    (φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F') :
    torusH G t s₀ →* CFSG.GorensteinWalter.PGL2 F' :=
  φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 2 (torusH G t s₀)))

namespace CaseIData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {q : ℕ}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
  (h : CaseIData G t s₀ d d₁ J q F' φ)
include h

theorem W_cyclic : IsCyclic (torusW G t s₀) := by
  obtain ⟨h1, -⟩ := h.clauses
  exact h1

theorem card_W_int :
    (Nat.card (torusW G t s₀) : ℤ) = ((q : ℤ) + (if q % 4 = 1 then 1 else -1)) / 2 := by
  obtain ⟨-, h2, -⟩ := h.clauses
  exact h2

theorem V_sup_W :
    Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ⊔ torusW G t s₀ =
      Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) := by
  obtain ⟨-, -, h3, -⟩ := h.clauses
  exact h3

theorem B_le_K : (N t).map (C t).subtype ≤ torusK G t s₀ := by
  obtain ⟨-, -, -, -, h5, -⟩ := h.clauses
  exact h5

theorem relIndex_K_H : (torusK G t s₀).relIndex (torusH G t s₀) = 2 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := h.clauses
  exact h6

theorem inv_of_not_mem_K :
    ∀ x ∈ torusH G t s₀, x ∉ torusK G t s₀ → ∀ w ∈ torusW G t s₀, x * w * x⁻¹ = w⁻¹ := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := h.clauses
  exact h7

theorem oddCore_H :
    (CFSG.pPrimeCore 2 (torusH G t s₀)).map (torusH G t s₀).subtype = torusW G t s₀ := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := h.clauses
  exact h8

theorem sylow_K : ∃ P : Sylow 2 (torusK G t s₀),
    (P : Subgroup (torusK G t s₀)).map (torusK G t s₀).subtype =
      Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := h.clauses
  exact h10

theorem normalizer_eq : ∀ W₀ : Subgroup G, W₀ ≤ torusW G t s₀ → W₀ ≠ ⊥ →
    Subgroup.normalizer (W₀ : Set G) = torusH G t s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := h.clauses
  exact h11

theorem centralizer_eq : ∀ w ∈ torusW G t s₀, w ≠ 1 →
    Subgroup.centralizer {w} = torusK G t s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := h.clauses
  exact h12

theorem card_F'_mod : Nat.card F' % 8 = 3 ∨ Nat.card F' % 8 = 5 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h21, -⟩ := h.clauses
  exact h21

theorem image_K :
    (((torusK G t s₀).subgroupOf (torusH G t s₀)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 2 (torusH G t s₀)))).map φ.toMonoidHom =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h22, -⟩ := h.clauses
  exact h22

theorem card_B_int : 4 * (Nat.card ((N t).map (C t).subtype) : ℤ) =
    Nat.card F' - (if Nat.card F' % 4 = 1 then 1 else -1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h23, -⟩ :=
    h.clauses
  exact h23

theorem v_orderOf : orderOf (s₀ * d) = 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h24, -⟩ :=
    h.clauses
  exact h24

theorem v_mem_H : s₀ * d ∈ torusH G t s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h25, -⟩ :=
    h.clauses
  exact h25

theorem v_not_mem_K : s₀ * d ∉ torusK G t s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h26, -⟩ :=
    h.clauses
  exact h26

theorem U_cyclic : IsCyclic (torusU G t s₀ d) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h27,
    -⟩ := h.clauses
  exact h27

theorem two_mul_card_U_int : 2 * (Nat.card (torusU G t s₀ d) : ℤ) =
    Nat.card F' + (if Nat.card F' % 4 = 1 then 1 else -1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h28,
    -⟩ := h.clauses
  exact h28

theorem U_le_K : torusU G t s₀ d ≤ torusK G t s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h29, -⟩ := h.clauses
  exact h29

theorem coprime_U_B :
    Nat.Coprime (Nat.card (torusU G t s₀ d)) (Nat.card ((N t).map (C t).subtype)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, h31⟩ := h.clauses
  exact h31

theorem W_le_K : torusW G t s₀ ≤ torusK G t s₀ := by
  have := h.W_cyclic
  intro w hw
  rw [torusK, Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val
    ((IsCyclic.commGroup (α := torusW G t s₀)).mul_comm ⟨y, hy⟩ ⟨w, hw⟩)

omit [Finite G] h in
theorem K_le_H : torusK G t s₀ ≤ torusH G t s₀ :=
  Subgroup.centralizer_le_normalizer (torusW G t s₀ : Set G)

theorem W_le_H : torusW G t s₀ ≤ torusH G t s₀ := h.W_le_K.trans K_le_H

omit [Finite G] h in
theorem U_le_X : torusU G t s₀ d ≤ torusX G t s₀ d := Subgroup.map_subtype_le _

omit [Finite G] h in
theorem X_le_H : torusX G t s₀ d ≤ torusH G t s₀ := inf_le_left

omit [Finite G] h in
theorem X_le_centralizer : torusX G t s₀ d ≤ Subgroup.centralizer {s₀ * d} := inf_le_right

omit [Finite G] h in
theorem U_le_H : torusU G t s₀ d ≤ torusH G t s₀ := U_le_X.trans X_le_H

omit [Finite G] h in
theorem U_le_centralizer : torusU G t s₀ d ≤ Subgroup.centralizer {s₀ * d} :=
  U_le_X.trans X_le_centralizer

omit h in
theorem odd_card_U : Odd (Nat.card (torusU G t s₀ d)) := by
  rw [torusU, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact odd_card_pPrimeCore

omit [Field F'] [Finite F'] h in
theorem odd_card_W : Odd (Nat.card (torusW G t s₀)) := by
  rw [torusW, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact odd_card_pPrimeCore

omit [Field F'] [Finite F'] h in
theorem odd_orderOf_of_mem_W {w : G} (hw : w ∈ torusW G t s₀) : Odd (orderOf w) := by
  have h1 := Subgroup.orderOf_dvd_natCard (torusW G t s₀) hw
  exact (odd_card_W (G := G) (t := t) (s₀ := s₀)).of_dvd_nat h1

omit h in
theorem odd_orderOf_of_mem_U {u : G} (hu : u ∈ torusU G t s₀ d) : Odd (orderOf u) := by
  have h1 := Subgroup.orderOf_dvd_natCard (torusU G t s₀ d) hu
  exact odd_card_U.of_dvd_nat h1

omit [Field F'] [Finite F'] h in
theorem odd_card_B : Odd (Nat.card ((N t).map (C t).subtype)) := by
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact odd_card_pPrimeCore

theorem eq_one_of_mem_W_of_commute {w : G} (hw : w ∈ torusW G t s₀)
    (hc : w * (s₀ * d) = s₀ * d * w) : w = 1 := by
  have hinv := h.inv_of_not_mem_K _ h.v_mem_H h.v_not_mem_K w hw
  have h1 : s₀ * d * w * (s₀ * d)⁻¹ = w := by rw [← hc]; group
  rw [h1] at hinv
  apply eq_one_of_mul_self_eq_one_of_odd (odd_orderOf_of_mem_W hw)
  calc w * w = w * w⁻¹ := by rw [← hinv]
    _ = 1 := mul_inv_cancel w

theorem eq_one_of_mem_U_of_mem_W {u : G} (hu : u ∈ torusU G t s₀ d)
    (hw : u ∈ torusW G t s₀) : u = 1 :=
  h.eq_one_of_mem_W_of_commute hw
    (Subgroup.mem_centralizer_singleton_iff.mp (U_le_centralizer hu))

theorem q_odd : Odd q := by
  obtain ⟨p, f, -, hpodd, -, rfl⟩ := h.oddPrimePower
  exact hpodd.pow

theorem two_mul_card_W_int :
    2 * (Nat.card (torusW G t s₀) : ℤ) = (q : ℤ) + (if q % 4 = 1 then 1 else -1) := by
  have h2 := h.card_W_int
  obtain ⟨k, hk⟩ := h.q_odd
  have hq : (q : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  split_ifs at h2 ⊢ with h4 <;> omega

theorem card_F'_odd : Odd (Nat.card F') := by
  rcases h.card_F'_mod with h8 | h8 <;> exact Nat.odd_iff.mpr (by omega)

theorem three_le_card_B : 3 ≤ Nat.card ((N t).map (C t).subtype) := by
  have hodd := odd_card_B (G := G) (t := t)
  have h1 : Nat.card ((N t).map (C t).subtype) ≠ 1 := by
    intro h1
    exact h.B_ne_bot (Subgroup.card_eq_one.mp h1)
  obtain ⟨k, hk⟩ := hodd
  omega

theorem five_le_card_U : 5 ≤ Nat.card (torusU G t s₀ d) := by
  have hB := h.three_le_card_B
  have h4 := h.card_B_int
  have h2 := h.two_mul_card_U_int
  have hB' : (3 : ℤ) ≤ Nat.card ((N t).map (C t).subtype) := by exact_mod_cast hB
  split_ifs at h4 h2 <;> omega

theorem five_le_card_W : 5 ≤ Nat.card (torusW G t s₀) := by
  have h2 := h.two_mul_card_W_int
  have hq := h.q_gt
  have hq' : (9 : ℤ) < q := by exact_mod_cast hq
  split_ifs at h2 <;> omega

theorem eleven_le_card_F' : 11 ≤ Nat.card F' := by
  have hB := h.three_le_card_B
  have h4 := h.card_B_int
  have hB' : (3 : ℤ) ≤ Nat.card ((N t).map (C t).subtype) := by exact_mod_cast hB
  split_ifs at h4 <;> omega

theorem U_ne_bot : torusU G t s₀ d ≠ ⊥ := by
  intro hbot
  have h5 := h.five_le_card_U
  rw [hbot, Subgroup.card_bot] at h5
  omega

theorem W_ne_bot : torusW G t s₀ ≠ ⊥ := by
  intro hbot
  have h5 := h.five_le_card_W
  rw [hbot, Subgroup.card_bot] at h5
  omega

omit [Finite G] h in
theorem torusPsi_apply (x : torusH G t s₀) :
    torusPsi φ x = φ (QuotientGroup.mk' (CFSG.pPrimeCore 2 (torusH G t s₀)) x) := rfl

theorem torusPsi_eq_one_iff (x : torusH G t s₀) :
    torusPsi φ x = 1 ↔ (x : G) ∈ torusW G t s₀ := by
  rw [torusPsi_apply, map_eq_one_iff _ φ.injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, ← h.oddCore_H]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem torusPsi_mem_range_iff (x : torusH G t s₀) :
    torusPsi φ x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range ↔
      (x : G) ∈ torusK G t s₀ := by
  rw [← h.image_K]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, hkx⟩
    have hkx' : torusPsi φ k = torusPsi φ x := hkx
    have h1 : torusPsi φ (k⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hkx', inv_mul_cancel]
    rw [h.torusPsi_eq_one_iff] at h1
    have h2 : (x : G) = k * (k⁻¹ * x : torusH G t s₀) := by simp
    rw [h2]
    exact (torusK G t s₀).mul_mem (Subgroup.mem_subgroupOf.mp hk) (h.W_le_K h1)
  · intro hx
    exact ⟨_, ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩

theorem eq_of_torusPsi_eq {x y : torusH G t s₀}
    (hx : (x : G) * (s₀ * d) = s₀ * d * x) (hy : (y : G) * (s₀ * d) = s₀ * d * y)
    (hxy : torusPsi φ x = torusPsi φ y) : x = y := by
  have h1 : torusPsi φ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  rw [h.torusPsi_eq_one_iff] at h1
  have hc : ((x⁻¹ * y : torusH G t s₀) : G) * (s₀ * d) = s₀ * d * (x⁻¹ * y : torusH G t s₀) := by
    have hx' : (x : G)⁻¹ * (s₀ * d) = s₀ * d * (x : G)⁻¹ := by
      calc (x : G)⁻¹ * (s₀ * d) = (x : G)⁻¹ * (s₀ * d * x) * (x : G)⁻¹ := by group
        _ = (x : G)⁻¹ * ((x : G) * (s₀ * d)) * (x : G)⁻¹ := by rw [hx]
        _ = s₀ * d * (x : G)⁻¹ := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (x : G)⁻¹ * y * (s₀ * d) = (x : G)⁻¹ * (y * (s₀ * d)) := by group
      _ = (x : G)⁻¹ * (s₀ * d * y) := by rw [hy]
      _ = (x : G)⁻¹ * (s₀ * d) * y := by group
      _ = s₀ * d * (x : G)⁻¹ * y := by rw [hx']
      _ = s₀ * d * ((x : G)⁻¹ * y) := by group
  have h2 := h.eq_one_of_mem_W_of_commute h1 hc
  have h3 : x⁻¹ * y = 1 := Subtype.ext h2
  exact (inv_mul_eq_one.mp h3)

theorem isOddPrimePower_card_F' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F') := by
  classical
  let : Fintype F' := Fintype.ofFinite F'
  obtain ⟨n, hp, hn⟩ := FiniteField.card F' (ringChar F')
  refine ⟨ringChar F', n, hp, ?_, n.2, ?_⟩
  · rcases hp.eq_two_or_odd' with h2 | h2
    · exfalso
      have hodd := h.card_F'_odd
      rw [Nat.card_eq_fintype_card, hn, h2] at hodd
      exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)) hodd
    · exact h2
  · rw [Nat.card_eq_fintype_card, hn]

theorem mem_torusU_of_odd {y : G} (hy : y ∈ torusX G t s₀ d) (hodd : Odd (orderOf y)) :
    y ∈ torusU G t s₀ d := by
  classical
  have : Finite (CFSG.GorensteinWalter.PGL2 F') :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hvH : s₀ * d ∈ torusH G t s₀ := h.v_mem_H
  have hv2 : torusPsi φ ⟨s₀ * d, hvH⟩ * torusPsi φ ⟨s₀ * d, hvH⟩ = 1 := by
    rw [← map_mul]
    have : (⟨s₀ * d, hvH⟩ : torusH G t s₀) * ⟨s₀ * d, hvH⟩ = 1 := by
      apply Subtype.ext
      change s₀ * d * (s₀ * d) = 1
      rw [← pow_two, ← h.v_orderOf, pow_orderOf_eq_one]
    rw [this, map_one]
  have hv1 : torusPsi φ ⟨s₀ * d, hvH⟩ ≠ 1 := by
    rw [ne_eq, h.torusPsi_eq_one_iff]
    intro hvW
    have := odd_orderOf_of_mem_W hvW
    rw [h.v_orderOf] at this
    exact absurd this (by decide)
  have hvR : torusPsi φ ⟨s₀ * d, hvH⟩ ∉
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range := by
    rw [h.torusPsi_mem_range_iff]
    exact h.v_not_mem_K
  have hK := h.isOddPrimePower_card_F'
  have hq3 : 3 < Nat.card F' := by have := h.eleven_le_card_F'; omega
  obtain ⟨U₁, w, -, hU₁card, -, hwU₁, hw2, hwinv, hC⟩ :=
    centralizer_of_involution_not_mem F' hK hq3 hv2 hv1 hvR
  have hmapU₁ : ∀ x : torusH G t s₀, (x : G) * (s₀ * d) = s₀ * d * x →
      Odd (orderOf (x : G)) → torusPsi φ x ∈ U₁ := by
    intro x hxv hxodd
    apply mem_of_odd_of_mem_sup_zpowers hwU₁ hw2 hwinv
    · rw [← hC, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxv
    · have h1 : orderOf (torusPsi φ x) ∣ orderOf x := orderOf_map_dvd _ x
      rw [← Subgroup.orderOf_coe] at h1
      exact hxodd.of_dvd_nat h1
  let Uh : Subgroup (torusH G t s₀) := (torusU G t s₀ d).subgroupOf (torusH G t s₀)
  have hUhv : ∀ x ∈ Uh, (x : G) * (s₀ * d) = s₀ * d * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (U_le_centralizer (Subgroup.mem_subgroupOf.mp hx))
  let f : Uh →* CFSG.GorensteinWalter.PGL2 F' := (torusPsi φ).comp Uh.subtype
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (h.eq_of_torusPsi_eq (hUhv a a.2) (hUhv b b.2) hab)
  have hfU₁ : f.range ≤ U₁ := by
    rintro _ ⟨a, rfl⟩
    exact hmapU₁ a (hUhv a a.2)
      (odd_orderOf_of_mem_U (Subgroup.mem_subgroupOf.mp a.2))
  have hcardf : Nat.card f.range = Nat.card (torusU G t s₀ d) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe U_le_H).toEquiv]
  have hcardU₁ : Nat.card U₁ = 2 * Nat.card (torusU G t s₀ d) := by
    have h1 := h.two_mul_card_U_int
    have h2 : (Nat.card U₁ : ℤ) = 2 * (Nat.card (torusU G t s₀ d) : ℤ) := by
      rw [hU₁card, h1]
    exact_mod_cast h2
  have hidx : (f.range.subgroupOf U₁).index = 2 := by
    have h1 := Subgroup.card_mul_index (f.range.subgroupOf U₁)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hfU₁).toEquiv, hcardf, hcardU₁] at h1
    have hU : 0 < Nat.card (torusU G t s₀ d) := Nat.card_pos
    have : Nat.card (torusU G t s₀ d) * (f.range.subgroupOf U₁).index =
        Nat.card (torusU G t s₀ d) * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hU this
  have hyH : y ∈ torusH G t s₀ := X_le_H hy
  have hyv : y * (s₀ * d) = s₀ * d * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (X_le_centralizer hy)
  have hψy : torusPsi φ ⟨y, hyH⟩ ∈ U₁ := hmapU₁ ⟨y, hyH⟩ hyv hodd
  have hodd' : Odd (orderOf (⟨torusPsi φ ⟨y, hyH⟩, hψy⟩ : U₁)) := by
    rw [Subgroup.orderOf_mk]
    have h1 : orderOf (torusPsi φ ⟨y, hyH⟩) ∣ orderOf (⟨y, hyH⟩ : torusH G t s₀) :=
      orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  have hmem := Subgroup.mem_subgroupOf.mp (mem_of_index_two_of_odd hidx hodd')
  obtain ⟨a, ha⟩ := hmem
  have hay : (a : torusH G t s₀) = ⟨y, hyH⟩ := h.eq_of_torusPsi_eq (hUhv a a.2) hyv ha
  have : y = ((a : torusH G t s₀) : G) := by rw [hay]
  rw [this]
  exact Subgroup.mem_subgroupOf.mp a.2

end CaseIData

end CFSG.Semidihedral.FixedCoreNontrivial
