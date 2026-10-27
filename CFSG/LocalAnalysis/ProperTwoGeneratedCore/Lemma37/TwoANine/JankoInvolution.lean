module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThreeLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypes
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoInvolutionPerm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThreePerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace JankoInvolution

open Janko JankoPTwoThree

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem conj_eq_mul_zbar_of_proj_eq_ybar {u v : J} (hu : proj e u = ybar)
    (hv : proj e v = tbar) : u * v * u⁻¹ = v * zbar J := by
  set k := someLift e κbar
  have hku : proj e (k * u * k⁻¹) = aNineSylowGenB := by
    rw [map_mul, map_mul, map_inv, proj_someLift, hu, κbar_conj_ybar]
  have hkv : proj e (k * v * k⁻¹) = aNineSylowGenA * aNineSylowGenC := by
    rw [map_mul, map_mul, map_inv, proj_someLift, hv, κbar_conj_tbar]
  have h := hJ.conj_eq_mul_zbar_of_genB_of_genAC e hku hkv
  have hz : k⁻¹ * zbar J = zbar J * k⁻¹ := (hJ.commute_zbar k⁻¹).eq
  have h' : k * (u * v * u⁻¹) * k⁻¹ = k * (v * zbar J) * k⁻¹ := by
    calc k * (u * v * u⁻¹) * k⁻¹ = k * u * k⁻¹ * (k * v * k⁻¹) * (k * u * k⁻¹)⁻¹ := by group
      _ = k * v * k⁻¹ * zbar J := h
      _ = k * v * (k⁻¹ * zbar J) := by group
      _ = k * (v * zbar J) * k⁻¹ := by rw [hz]; group
  simpa using h'

theorem card_centralizer_of_proj_eq_tbar {v : J} (hv : proj e v = tbar) :
    Nat.card (centralizer ({v} : Set J)) = 192 := by
  set N := (centralizer ({tbar} : Set (alternatingGroup (Fin 9)))).comap (proj e)
  have hN : Nat.card N = 384 := by rw [hJ.card_comap_proj e, card_centralizer_tbar]
  have hCN : centralizer ({v} : Set J) ≤ N := fun g hg => by
    rw [mem_comap, mem_centralizer_singleton_iff, ← hv, ← map_mul,
      mem_centralizer_singleton_iff.mp hg, map_mul]
  obtain ⟨u, hu⟩ := proj_surjective e ybar
  have huN : u ∈ N := by
    rw [mem_comap, hu, mem_centralizer_singleton_iff]
    exact tbar_mul_ybar.symm
  have hne : v * zbar J ≠ v := fun h => hJ.zbar_ne_one (mul_eq_left.mp h)
  have h : ∀ b ∈ N, b * v * b⁻¹ = v ∨ b * v * b⁻¹ = v * zbar J := fun b hb => by
    refine (hJ.proj_eq_proj_iff' e).mp ?_
    rw [mem_comap, mem_centralizer_singleton_iff, ← hv] at hb
    rw [map_mul, map_mul, map_inv, hb, mul_inv_cancel_right]
  have h2 := card_eq_two_mul_card_inf_centralizer hne h huN
    (conj_eq_mul_zbar_of_proj_eq_ybar hJ e hu hv)
  rw [inf_eq_right.mpr hCN, hN] at h2
  omega

theorem liftOdd_sbar₂_mem_centralizer {v : J} (hv : proj e v = tbar) :
    liftOdd e sbar₂ ∈ centralizer ({v} : Set J) := by
  have ho : Odd (orderOf sbar₂) := by rw [orderOf_sbar₂]; exact ⟨1, rfl⟩
  rw [mem_centralizer_singleton_iff]
  refine (hJ.commute_of_odd_orderOf e (hJ.odd_orderOf_liftOdd e ho) ?_).eq.symm
  rw [hv, hJ.proj_liftOdd e ho]
  exact (mem_centralizer_singleton_iff.mp sbar₂_mem_centralizer_tbar).symm

theorem card_centralizer_eq_of_mem {v : J} (hv : proj e v = tbar) {x : J}
    (hx : x ∈ centralizer ({v} : Set J)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card (centralizer ({x} : Set J)) = 108 := by
  have := hJ.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨d, -, hd⟩ := exists_conj_mem_zpowers (centralizer ({v} : Set J)) (m := 64)
    (by rw [card_centralizer_of_proj_eq_tbar hJ e hv]; norm_num) (by norm_num) hx
    (liftOdd_sbar₂_mem_centralizer hJ e hv) hox (hJ.orderOf_liftOdd_sbar₂ e)
  have hd1 : d * x * d⁻¹ ≠ 1 := fun h => hx1 (by
    rw [← mul_inv_eq_one, mul_inv_eq_iff_eq_mul, one_mul] at h
    simpa using h)
  rw [← card_centralizer_conj_eq d x]
  rcases eq_or_eq_inv_of_mem_zpowers (hJ.orderOf_liftOdd_sbar₂ e) hd hd1 with h | h <;>
    rw [h]
  · exact hJ.card_centralizer_liftOdd_sbar₂ e
  · rw [centralizer_inv_eq]
    exact hJ.card_centralizer_liftOdd_sbar₂ e

end JankoInvolution

namespace Janko

open JankoInvolution JankoPTwoThree

variable {G : Type*} [Group G] {z : G} (hH : IsTwoANine (centralizer ({z} : Set G)))
include hH

private theorem exists_conj_eq_someLift_tbar (hz : orderOf z = 2)
    (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃*
      alternatingGroup (Fin 9))
    {u : G} (hu : u ∈ centralizer ({z} : Set G)) (hu2 : orderOf u = 2) (huz : u ≠ z) :
    ∃ c : centralizer ({z} : Set G), c * ⟨u, hu⟩ * c⁻¹ = someLift e tbar := by
  have hu2' : orderOf (⟨u, hu⟩ : centralizer ({z} : Set G)) = 2 := by
    rwa [← Subgroup.orderOf_coe]
  have huz' : (⟨u, hu⟩ : centralizer ({z} : Set G)) ≠ zbar (centralizer ({z} : Set G)) :=
    fun h => huz (by rw [← coe_zbar_eq hz hH, ← h])
  have hv := hH.orderOf_eq_two_of_cycleType_two_two_two_two e
    (x := someLift e tbar) (by rw [proj_someLift]; exact cycleType_tbar)
  have hvz : someLift e tbar ≠ zbar (centralizer ({z} : Set G)) := fun h =>
    hv.2 (h ▸ hH.zbar_mem_center)
  exact isConj_iff.mp (hH.isConj_of_orderOf_eq_two hu2' hv.1 huz' hvz)

theorem card_centralizer_involution (hz : orderOf z = 2) :
    ∀ u ∈ centralizer ({z} : Set G), orderOf u = 2 → u ≠ z →
      Nat.card (centralizer ({u} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 192 := by
  intro u hu hu2 huz
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  obtain ⟨c, hc⟩ := exists_conj_eq_someLift_tbar hH hz e hu hu2 huz
  rw [show u = ((⟨u, hu⟩ : centralizer ({z} : Set G)) : G) from rfl, card_centralizer_inf_eq,
    ← card_centralizer_conj_eq c, hc]
  exact card_centralizer_of_proj_eq_tbar hH e (proj_someLift e tbar)

theorem type_s₂_of_involution (hz : orderOf z = 2) :
    ∀ u ∈ centralizer ({z} : Set G), orderOf u = 2 → u ≠ z →
      ∀ x ∈ centralizer ({u} : Set G) ⊓ centralizer ({z} : Set G), x ^ 3 = 1 → x ≠ 1 →
        Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 108 := by
  intro u hu hu2 huz x hx hx3 hx1
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  obtain ⟨c, hc⟩ := exists_conj_eq_someLift_tbar hH hz e hu hu2 huz
  set x' : centralizer ({z} : Set G) := ⟨x, hx.2⟩
  have hxu : x' ∈ centralizer ({(⟨u, hu⟩ : centralizer ({z} : Set G))} : Set _) :=
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hx.1))
  have hcx : c * x' * c⁻¹ ∈ centralizer ({someLift e tbar} : Set _) := by
    rw [← hc, mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.mp hxu
    calc c * x' * c⁻¹ * (c * ⟨u, hu⟩ * c⁻¹) = c * (x' * ⟨u, hu⟩) * c⁻¹ := by group
      _ = c * (⟨u, hu⟩ * x') * c⁻¹ := by rw [h]
      _ = c * ⟨u, hu⟩ * c⁻¹ * (c * x' * c⁻¹) := by group
  have hx3' : (c * x' * c⁻¹) ^ 3 = 1 := by
    rw [conj_pow, show x' ^ 3 = 1 from Subtype.ext hx3, mul_one, mul_inv_cancel]
  have hx1' : c * x' * c⁻¹ ≠ 1 := fun h => hx1 (by
    have : x' = 1 := by simpa using h
    exact congrArg Subtype.val this)
  rw [show x = (x' : G) from rfl, card_centralizer_inf_eq, ← card_centralizer_conj_eq c]
  exact card_centralizer_eq_of_mem hH e (proj_someLift e tbar) hcx hx3' hx1'

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
