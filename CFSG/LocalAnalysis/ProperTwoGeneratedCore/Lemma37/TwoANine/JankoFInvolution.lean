module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoF
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFPermInvolution

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace JankoF

theorem conj_eq_mul_zbar_of_proj_eq_ybar {J : Type*} [Group J] (hJ : IsTwoANine J)
    (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {u v : J} (hu : proj e u = Janko.ybar)
    (hv : proj e v = Janko.tbar) : u * v * u⁻¹ = v * zbar J := by
  set h := someLift e hbar
  have hu' : proj e (h * u * h⁻¹) = aNineSylowGenB := by
    rw [map_mul, map_mul, map_inv, proj_someLift, hu, hbar_conj_ybar]
  have hv' : proj e (h * v * h⁻¹) = aNineSylowGenA * aNineSylowGenC := by
    rw [map_mul, map_mul, map_inv, proj_someLift, hv, hbar_conj_tbar]
  have key := hJ.conj_eq_mul_zbar_of_genB_of_genAC e hu' hv'
  have hc : h * v * h⁻¹ * zbar J = h * (v * zbar J) * h⁻¹ := by
    rw [mul_assoc h v, mul_assoc h (v * zbar J), mul_assoc v, (hJ.commute_zbar h⁻¹).eq.symm,
      ← mul_assoc v, mul_assoc]
  have h2 : h * (u * v * u⁻¹) * h⁻¹ = h * (v * zbar J) * h⁻¹ := by
    rw [← hc, ← key]
    group
  simpa using h2

end JankoF

namespace Janko

variable {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
  (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))
include hH

omit hH in
theorem ℓ_mem_F : ℓ e ∈ F e :=
  (JankoF.coe_mem_map_comap_iff e _).mpr (by rw [proj_someLift]; exact JankoF.ℓbar_mem_Fbar)

include hz in
theorem ℓ_pow_four : ℓ e ^ 4 = z := by
  have hsq := hH.sq_eq_zbar_of_cycleType_two_two e (x := someLift e ℓbar ^ 2)
    (by rw [map_pow, proj_someLift, ℓbar_sq]; exact JankoF.cycleType_ybar)
  have h4 : someLift e ℓbar ^ 4 = ⟨z, JankoF.self_mem_centralizer⟩ := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hsq, JankoF.zbar_eq hz hH]
  rw [ℓ, ← Subgroup.coe_pow, h4]

include hz in
theorem orderOf_ℓ : orderOf (ℓ e) = 8 := by
  have h4 := ℓ_pow_four hz hH e
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hne : ¬ ℓ e ^ 2 ^ 2 = 1 := by
    rw [show 2 ^ 2 = 4 from rfl, h4]
    exact hz1
  have heq : ℓ e ^ 2 ^ (2 + 1) = 1 := by
    rw [show 2 ^ (2 + 1) = 4 * 2 from rfl, pow_mul, h4, ← hz, pow_orderOf_eq_one]
  rw [orderOf_eq_prime_pow hne heq]
  norm_num

theorem t_mul_ℓ : t e * ℓ e * (t e)⁻¹ = ℓ e ^ 3 := by
  have htl := hH.sq_eq_zbar_of_cycleType_two_two e (x := someLift e tbar * someLift e ℓbar)
    (by rw [map_mul, proj_someLift, proj_someLift]; exact JankoF.cycleType_tbar_mul_ℓbar)
  have ht2 := hH.sq_eq_one_of_cycleType_two_two_two_two e (x := someLift e tbar)
    (by rw [proj_someLift]; exact cycleType_tbar)
  have hl4 : someLift e ℓbar ^ 4 = zbar (centralizer ({z} : Set G)) := by
    have hsq := hH.sq_eq_zbar_of_cycleType_two_two e (x := someLift e ℓbar ^ 2)
      (by rw [map_pow, proj_someLift, ℓbar_sq]; exact JankoF.cycleType_ybar)
    rw [show 4 = 2 * 2 from rfl, pow_mul, hsq]
  have htinv : (someLift e tbar)⁻¹ = someLift e tbar :=
    inv_eq_of_mul_eq_one_left (by rw [← sq, ht2])
  have key : someLift e tbar * someLift e ℓbar * (someLift e tbar)⁻¹ = someLift e ℓbar ^ 3 := by
    calc someLift e tbar * someLift e ℓbar * (someLift e tbar)⁻¹
        = (someLift e tbar * someLift e ℓbar) ^ 2 * (someLift e ℓbar)⁻¹ := by
          rw [htinv, sq]
          group
      _ = someLift e ℓbar ^ 4 * (someLift e ℓbar)⁻¹ := by rw [htl, hl4]
      _ = someLift e ℓbar ^ 3 := by group
  rw [t, ℓ, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, key, Subgroup.coe_pow]

omit hH in
theorem t_mem_normalizer_F : t e ∈ normalizer (F e : Set G) := by
  have h : someLift e tbar ∈ normalizer ((Fbar.comap (proj e) : Subgroup _) :
      Set (centralizer ({z} : Set G))) :=
    le_normalizer_comap (proj e) (by
      rw [mem_comap, proj_someLift]
      exact JankoF.tbar_mem_normalizer_Fbar)
  have hmem : ((someLift e tbar : centralizer ({z} : Set G)) : G) ∈
      (normalizer ((Fbar.comap (proj e) : Subgroup _) :
        Set (centralizer ({z} : Set G)))).map (centralizer ({z} : Set G)).subtype := ⟨_, h, rfl⟩
  rw [← normalizer_map_inf_eq_map_subtype] at hmem
  exact hmem.1

theorem conj_t_eq_or {u : centralizer ({z} : Set G)} (hu : Commute (proj e u) tbar) :
    u * someLift e tbar * u⁻¹ = someLift e tbar ∨
      u * someLift e tbar * u⁻¹ = someLift e tbar * zbar (centralizer ({z} : Set G)) :=
  (hH.proj_eq_proj_iff' e).mp (by
    rw [map_mul, map_mul, map_inv, proj_someLift, hu.eq, mul_inv_cancel_right])

theorem mul_zbar_ne :
    someLift e tbar * zbar (centralizer ({z} : Set G)) ≠ someLift e tbar := fun h =>
  hH.zbar_ne_one (mul_eq_left.mp h)

omit hH in
theorem coe_mem_F₁_iff {u : centralizer ({z} : Set G)} (huF : proj e u ∈ Fbar) :
    (u : G) ∈ F e ⊓ centralizer ({t e} : Set G) ↔
      u * someLift e tbar * u⁻¹ = someLift e tbar := by
  constructor
  · rintro ⟨-, hut⟩
    have hc : u * someLift e tbar = someLift e tbar * u :=
      Subtype.ext (mem_centralizer_singleton_iff.mp hut)
    rw [hc, mul_inv_cancel_right]
  · intro h
    refine ⟨(JankoF.coe_mem_map_comap_iff e u).mpr huF, ?_⟩
    have hc : u * someLift e tbar = someLift e tbar * u := by
      calc u * someLift e tbar = u * someLift e tbar * u⁻¹ * u := by group
        _ = someLift e tbar * u := by rw [h]
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)

omit hH in
theorem F₁_le_comap :
    F e ⊓ centralizer ({t e} : Set G) ≤ ((Fbar ⊓ centralizer ({tbar} : Set
      (alternatingGroup (Fin 9)))).comap (proj e)).map (centralizer ({z} : Set G)).subtype := by
  rintro _ ⟨⟨u, huF, rfl⟩, hut⟩
  refine ⟨u, ⟨huF, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
  have hc : u * someLift e tbar = someLift e tbar * u :=
    Subtype.ext (mem_centralizer_singleton_iff.mp hut)
  rw [← proj_someLift e tbar, ← map_mul, hc, map_mul]

theorem card_F₁ : Nat.card (F e ⊓ centralizer ({t e} : Set G) : Subgroup G) = 24 := by
  set W : Subgroup G := ((Fbar ⊓ centralizer ({tbar} : Set (alternatingGroup (Fin 9)))).comap
    (proj e)).map (centralizer ({z} : Set G)).subtype with hWdef
  have hW : Nat.card W = 48 := by
    rw [hWdef, card_map_of_injective (centralizer _).subtype_injective, hH.card_comap_proj e,
      JankoF.card_Fbar_inf_centralizer_tbar]
  have hy : proj e (someLift e ybar) ∈
      Fbar ⊓ centralizer ({tbar} : Set (alternatingGroup (Fin 9))) := by
    rw [proj_someLift]
    exact ⟨JankoF.ybar_mem_Fbar, mem_centralizer_singleton_iff.mpr JankoF.commute_tbar_ybar.eq.symm⟩
  have hyt := JankoF.conj_eq_mul_zbar_of_proj_eq_ybar hH e (proj_someLift e ybar)
    (proj_someLift e tbar)
  set K := (F e ⊓ centralizer ({t e} : Set G)).subgroupOf W with hKdef
  have hK : K.index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨_, ⟨someLift e ybar, hy, rfl⟩⟩, fun b => ?_⟩
    obtain ⟨u, ⟨huF, huC⟩, hub⟩ := b.2
    have huc : Commute (proj e u) tbar := mem_centralizer_singleton_iff.mp huC
    have huyF : proj e (u * someLift e ybar) ∈ Fbar := by
      rw [map_mul]
      exact mul_mem huF hy.1
    have e1 : b * ⟨_, ⟨someLift e ybar, hy, rfl⟩⟩ ∈ K ↔
        u * someLift e ybar * someLift e tbar * (u * someLift e ybar)⁻¹ = someLift e tbar := by
      rw [hKdef, mem_subgroupOf, Subgroup.coe_mul, ← hub]
      exact coe_mem_F₁_iff e huyF
    have e2 : b ∈ K ↔ u * someLift e tbar * u⁻¹ = someLift e tbar := by
      rw [hKdef, mem_subgroupOf, ← hub]
      exact coe_mem_F₁_iff e huF
    have hconj : u * someLift e ybar * someLift e tbar * (u * someLift e ybar)⁻¹ =
        u * someLift e tbar * u⁻¹ * zbar (centralizer ({z} : Set G)) := by
      calc u * someLift e ybar * someLift e tbar * (u * someLift e ybar)⁻¹
          = u * (someLift e ybar * someLift e tbar * (someLift e ybar)⁻¹) * u⁻¹ := by group
        _ = u * (someLift e tbar * zbar (centralizer ({z} : Set G))) * u⁻¹ := by rw [hyt]
        _ = u * someLift e tbar * u⁻¹ * zbar (centralizer ({z} : Set G)) := by
          rw [mul_assoc u, mul_assoc, (hH.commute_zbar u⁻¹).eq.symm]
          group
    rw [e1, e2, hconj]
    rcases conj_t_eq_or hH e huc with h | h
    · rw [h]
      exact Or.inr ⟨rfl, mul_zbar_ne hH e⟩
    · rw [h, mul_assoc, hH.zbar_mul_zbar, mul_one]
      exact Or.inl ⟨rfl, mul_zbar_ne hH e⟩
  have hcard := K.card_mul_index
  rw [hK, hW] at hcard
  rw [← Nat.card_congr (subgroupOfEquivOfLe (F₁_le_comap e)).toEquiv]
  change Nat.card K = 24
  omega

theorem s₂_mem_F₁ : s₂ e ∈ F e ⊓ centralizer ({t e} : Set G) := by
  have hodd : Odd (orderOf sbar₂) := by rw [orderOf_sbar₂]; exact ⟨1, rfl⟩
  refine ⟨(JankoF.coe_mem_map_comap_iff e _).mpr (by
    rw [hH.proj_liftOdd e hodd]; exact JankoF.sbar₂_mem_Fbar), ?_⟩
  have hc : Commute (someLift e tbar) (liftOdd e sbar₂) := hH.commute_of_odd_orderOf e
    (hH.odd_orderOf_liftOdd e hodd)
    (by rw [proj_someLift, hH.proj_liftOdd e hodd]; exact JankoF.commute_tbar_sbar₂)
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc.eq).symm

theorem P₂_le_F₁ : zpowers (s₂ e) ≤ F e ⊓ centralizer ({t e} : Set G) :=
  zpowers_le.mpr (s₂_mem_F₁ hH e)

theorem not_le_normalizer_P₂ :
    ¬ F e ⊓ centralizer ({t e} : Set G) ≤ normalizer ((zpowers (s₂ e) : Subgroup G) : Set G) := by
  have hodd : Odd (orderOf JankoF.wbar) := by rw [JankoF.orderOf_wbar]; exact ⟨1, rfl⟩
  have hodd₂ : Odd (orderOf sbar₂) := by rw [orderOf_sbar₂]; exact ⟨1, rfl⟩
  intro hle
  have hwF : ((liftOdd e JankoF.wbar : centralizer ({z} : Set G)) : G) ∈ F e :=
    (JankoF.coe_mem_map_comap_iff e _).mpr (by
      rw [hH.proj_liftOdd e hodd]; exact JankoF.wbar_mem_Fbar)
  have hc : Commute (someLift e tbar) (liftOdd e JankoF.wbar) := hH.commute_of_odd_orderOf e
    (hH.odd_orderOf_liftOdd e hodd)
    (by rw [proj_someLift, hH.proj_liftOdd e hodd]; exact JankoF.commute_tbar_wbar)
  have hwt : ((liftOdd e JankoF.wbar : centralizer ({z} : Set G)) : G) ∈
      centralizer ({t e} : Set G) :=
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc.eq).symm
  have hN := (mem_normalizer_iff.mp (hle ⟨hwF, hwt⟩) (s₂ e)).mp (mem_zpowers _)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hN
  have hk' : liftOdd e sbar₂ ^ k =
      liftOdd e JankoF.wbar * liftOdd e sbar₂ * (liftOdd e JankoF.wbar)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hk
  have hp := congrArg (proj e) hk'
  rw [map_zpow, map_mul, map_mul, map_inv, hH.proj_liftOdd e hodd₂, hH.proj_liftOdd e hodd] at hp
  exact JankoF.conj_wbar_sbar₂_notMem ⟨k, hp⟩

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
