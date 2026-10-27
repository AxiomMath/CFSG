module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterLocal
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusDickson

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem map_subgroupOf_le_normalizer {G : Type*} [Group G] {K : Subgroup G} {H : Type*}
    [Group H] [Finite H] (ψ : K →* H) {X Y : Subgroup G}
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) :
    (Y.subgroupOf K).map ψ ≤
      Subgroup.normalizer (((X.subgroupOf K).map ψ : Subgroup H) : Set H) := by
  rintro _ ⟨c, hc, rfl⟩
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨c * u * c⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp (hYX hc) (u : G)).mp hu

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem mem_B_of_mem_ker_of_odd (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {x : G}
    (hx : x ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers t) (hodd : Odd (orderOf x)) :
    x ∈ (N t).map (C t).subtype := by
  have hL := h.localData
  have hBt : ∀ b ∈ (N t).map (C t).subtype, ∀ k ∈ Subgroup.zpowers t, b * k = k * b :=
    fun b hb k hk => by
      rcases hL.zpowers_t_cases k hk with hk1 | hkt
      · rw [hk1, mul_one, one_mul]
      · rw [hkt]; exact Subgroup.mem_centralizer_singleton_iff.mp (hL.B_le hb)
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_mul_of_mem_sup hBt hx
  rcases hL.zpowers_t_cases k hk with hk1 | hkt
  · rw [hk1, mul_one]
    exact hb
  · exfalso
    rw [hkt] at hodd hk
    have hc : Commute t b := (hBt b hb t hk).symm
    have hodd' : Odd (orderOf (t * b)) := by rw [hc.eq]; exact hodd
    exact hL.not_odd_t (odd_orderOf_of_mul hc hodd' (hL.B_odd b hb))

theorem coprime_card_W (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Nat.Coprime (Nat.card (torusW G t s₀)) (Nat.card ((N t).map (C t).subtype) * 2) :=
  Nat.Coprime.mul_right h.card_W_B_arith.2.2 (Nat.coprime_two_right.mpr h.odd_card_W)

theorem κ_ne_one_of_mem_W (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {c : C t}
    (hc : (c : G) ∈ torusW G t s₀) (hc1 : c ≠ 1) : κ c ≠ 1 := by
  intro h1
  apply hc1
  have hmem := (h.mem_ker_κ_iff c).mp h1
  have h2 : orderOf (c : G) ∣ Nat.card (torusW G t s₀) := Subgroup.orderOf_dvd_natCard _ hc
  have h3 : orderOf (c : G) ∣ Nat.card ((N t).map (C t).subtype) * 2 := by
    rw [← h.card_B_sup_t]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 h.coprime_card_W) h3
  rw [orderOf_eq_one_iff] at this
  exact Subtype.ext this

theorem κ_apply_ne_of_mem_W (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 1) {c : C t} (hc : (c : G) ∈ torusW G t s₀) (hc1 : c ≠ 1)
    (x : Omega F) : κ c x ≠ x := by
  have hW := ((h.card_W_B).1 he).1
  have hκ1 := h.κ_ne_one_of_mem_W hc hc1
  have hord : orderOf (κ c) ∣ Nat.card (torusW G t s₀) := by
    refine (orderOf_map_dvd κ c).trans ?_
    rw [← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard _ hc
  refine UnitaryBranch.fixedPointFree_of_coprime F (h.range_κ ▸ ⟨c, rfl⟩) hκ1
    (Nat.Coprime.coprime_dvd_left hord ?_) x
  have hm := h.odd_card_W
  rw [h.card_F, show p ^ f = 2 * Nat.card (torusW G t s₀) - 1 by omega]
  set m := Nat.card (torusW G t s₀)
  have hm1 : 1 ≤ m := hm.pos
  have hc1' : Nat.Coprime m (m - 1) :=
    (Nat.coprime_self_sub_right hm1).mpr (Nat.coprime_one_right m)
  have hc2 : Nat.Coprime m (2 * m - 1) := by
    rw [show 2 * m - 1 = m + (m - 1) by omega]
    exact Nat.coprime_self_add_right.mpr hc1'
  have hc3 : Nat.Coprime m (2 * m - 1 - 1) := by
    rw [show 2 * m - 1 - 1 = 2 * (m - 1) by omega]
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hm) hc1'
  exact Nat.Coprime.mul_right hc2 hc3

theorem eq_bot_of_mod_four_eq_one
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 1) :
    (∀ X : Subgroup G, X ≤ C t → IsPGroup p X →
      torusW G t s₀ ≤ Subgroup.normalizer (X : Set G) → X = ⊥) ∧
    (∀ X : Subgroup G, X ≤ C t → IsPGroup p X → s₀ ∈ Subgroup.normalizer (X : Set G) →
      X = ⊥) ∧
    ∀ X : Subgroup G, X ≤ C t → Odd (Nat.card X) →
      Nat.Coprime (Nat.card X) (Nat.card (torusW G t s₀)) →
      torusW G t s₀ ≤ Subgroup.normalizer (X : Set G) → X ≤ (N t).map (C t).subtype := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hL := h.localData
  have hWC : torusW G t s₀ ≤ C t := hL.W_le_J.trans hL.J_le
  have hW1 : torusW G t s₀ ≠ ⊥ := by
    intro hb
    have h1 := ((h.card_W_B).1 he).1
    rw [hb, Subgroup.card_bot] at h1
    have := h.q_gt
    omega
  obtain ⟨⟨w, hwW⟩, hw1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
  have hw1 : w ≠ 1 := fun h1 => hw1' (Subtype.ext h1)
  have hκW : Nat.card (((torusW G t s₀).subgroupOf (C t)).map κ) = Nat.card (torusW G t s₀) :=
    h.card_map_κ_of_coprime hWC h.coprime_card_W
  have key : ∀ X : Subgroup G, X ≤ C t → Odd (Nat.card X) →
      Nat.Coprime (Nat.card X) (Nat.card (torusW G t s₀)) →
      torusW G t s₀ ≤ Subgroup.normalizer (X : Set G) → X ≤ (N t).map (C t).subtype := by
    intro X hXC hXodd hXW hWX
    set X₁ := (X.subgroupOf (C t)).map κ with hX₁
    set W₁ := ((torusW G t s₀).subgroupOf (C t)).map κ with hW₁
    have hX₁dvd : Nat.card X₁ ∣ Nat.card X := by
      rw [hX₁, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv]
      exact Subgroup.card_map_dvd _ _
    have hnorm : W₁ ≤ Subgroup.normalizer (X₁ : Set (Equiv.Perm (Omega F))) :=
      map_subgroupOf_le_normalizer κ hWX
    have hcop : Nat.Coprime (Nat.card X₁) (Nat.card W₁) := by
      rw [hκW]
      exact Nat.Coprime.coprime_dvd_left hX₁dvd hXW
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X₁ W₁ hnorm
      (Subgroup.disjoint_of_coprime_natCard hcop)
    have hD : X₁ ⊔ W₁ ≤ coordinateD F :=
      h.range_κ ▸ sup_le (Subgroup.map_le_range κ _) (Subgroup.map_le_range κ _)
    have hodd : Odd (Nat.card (X₁ ⊔ W₁ : Subgroup (Equiv.Perm (Omega F)))) := by
      rw [hcard, hκW]
      exact (hXodd.of_dvd_nat hX₁dvd).mul h.odd_card_W
    rcases odd_subgroup_fixes_point_or_cyclic hp h.odd h.card_F _ hD hodd with
      ⟨z, hz⟩ | ⟨-, hdvd⟩
    · exfalso
      have hwC := hWC hwW
      exact h.κ_apply_ne_of_mem_W he (c := ⟨w, hwC⟩) hwW
        (fun h1 => hw1 (congrArg Subtype.val h1)) z
        (hz _ (Subgroup.mem_sup_right ⟨⟨w, hwC⟩, hwW, rfl⟩))
    · have h2 : (Nat.card F + 1) / 2 = Nat.card (torusW G t s₀) := by
        have := ((h.card_W_B).1 he).1
        rw [h.card_F]
        omega
      rw [hcard, hκW, h2] at hdvd
      have hX₁1 : Nat.card X₁ = 1 := by
        have hpos : 0 < Nat.card (torusW G t s₀) := Nat.card_pos
        have := Nat.le_of_dvd hpos hdvd
        have hX₁pos : 0 < Nat.card X₁ := Nat.card_pos
        nlinarith
      intro x hx
      have hxC := hXC hx
      have hκx : κ ⟨x, hxC⟩ = 1 := by
        have hmem : κ ⟨x, hxC⟩ ∈ X₁ := ⟨⟨x, hxC⟩, hx, rfl⟩
        rw [Subgroup.card_eq_one.mp hX₁1] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact h.mem_B_of_mem_ker_of_odd ((h.mem_ker_κ_iff _).mp hκx)
        (hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx))
  refine ⟨fun X hXC hXp hWX => ?_, fun X hXC hXp hsX => ?_, key⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
    have hXodd : Odd (Nat.card X) := by
      rw [hk]
      exact h.odd.pow
    have hXW : Nat.Coprime (Nat.card X) (Nat.card (torusW G t s₀)) := by
      rw [hk]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr h.card_W_B_arith.1)
    have hXB := key X hXC hXodd hXW hWX
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hXp ⟨x, hx⟩
    have hxj : x ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 : orderOf x ∣ p ^ j := orderOf_dvd_of_pow_eq_one hxj
    have h2 : orderOf x ∣ Nat.card ((N t).map (C t).subtype) :=
      Subgroup.orderOf_dvd_natCard _ (hXB hx)
    have h3 : Nat.Coprime (p ^ j) (Nat.card ((N t).map (C t).subtype)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr h.card_W_B_arith.2.1)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2))
  · by_contra hX1
    have hcop := h.coprime_of_isPGroup hXp
    set X₁ := (X.subgroupOf (C t)).map κ with hX₁
    have hX₁D : X₁ ≤ coordinateD F := h.range_κ ▸ Subgroup.map_le_range κ _
    have hX₁p : IsPGroup p X₁ := (hXp.comap_subtype (K := C t)).map κ
    have hX₁1 : X₁ ≠ ⊥ := by
      intro hb
      apply hX1
      have := h.card_map_κ_of_coprime hXC hcop
      rw [← hX₁, hb, Subgroup.card_bot] at this
      exact Subgroup.card_eq_one.mp this.symm
    obtain ⟨z, hz, -⟩ := existsUnique_fixed_of_isPGroup hp h.odd h.card_F hX₁D hX₁p hX₁1
    have hsN : κ ⟨s₀, hL.s_mem_C⟩ ∈ Subgroup.normalizer (X₁ : Set (Equiv.Perm (Omega F))) :=
      map_subgroupOf_le_normalizer κ (Y := Subgroup.zpowers s₀) (Subgroup.zpowers_le.mpr hsX)
        ⟨⟨s₀, hL.s_mem_C⟩, Subgroup.mem_zpowers s₀, rfl⟩
    have hsz := fixed_of_mem_normalizer_of_isPGroup hp h.odd h.card_F hX₁D hX₁p hX₁1 hz hsN
    obtain ⟨hsG, hs2⟩ := h.κ_s₀
    exact hsG ((mem_coordinateG_iff_of_involution_fixed hp h.odd h.card_F
      (h.range_κ ▸ ⟨_, rfl⟩) hs2 hsz).mpr he)

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
