module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
import CFSG.LocalAnalysis.SeitzReduction.Inheritance
import CFSG.LocalAnalysis.EvenSmallLie.Setup
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

theorem standardComponentIsStandard_of_card_le_two {Y : Type*} [Group Y] [Finite Y] {t : Y}
    (ht : orderOf t = 2) {D : Subgroup Y} (hDt : D ≤ centralizer ({t} : Set Y))
    (hDn : (D.subgroupOf (centralizer ({t} : Set Y))).Normal)
    (hDq : CFSG.Open.IsQuasisimple D)
    (hK2 : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2) :
    standardComponentIsStandard D := by
  set K := centralizer (D : Set Y) with hK
  have htK : t ∈ K :=
    mem_centralizer_iff.2 fun x hx => mem_centralizer_singleton_iff.1 (hDt hx)
  have hCtN : centralizer ({t} : Set Y) ≤ normalizer (D : Set Y) :=
    le_normalizer_of_normal_subgroupOf hDt
  have hKN : K ≤ normalizer (D : Set Y) := centralizer_le_normalizer _
  have hNDK : normalizer (D : Set Y) ≤ normalizer (K : Set Y) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer hh hx
    · intro hx
      have h1 := CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer (inv_mem hh) hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at h1
  have hNKD : normalizer (K : Set Y) ≤ normalizer (D : Set Y) := by
    intro h hh
    have hu : h * t * h⁻¹ ∈ K := (mem_normalizer_iff.1 hh t).1 htK
    have hu2 : orderOf (h * t * h⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
    obtain ⟨k, hk, hkt⟩ :=
      SeitzReduction.exists_conj_eq_of_forall_card_le_two hK2 htK ht hu hu2
    have hy : k⁻¹ * h ∈ centralizer ({t} : Set Y) := by
      rw [mem_centralizer_singleton_iff]
      calc k⁻¹ * h * t = k⁻¹ * (h * t * h⁻¹) * h := by group
        _ = k⁻¹ * (k * t * k⁻¹) * h := by rw [hkt]
        _ = t * (k⁻¹ * h) := by group
    rw [show h = k * (k⁻¹ * h) by group]
    exact mul_mem (hKN hk) (hCtN hy)
  refine ⟨hDq, ?_, ?_, le_antisymm hNKD hNDK, ?_⟩
  · have h2 : orderOf (⟨t, htK⟩ : K) = 2 := by rw [orderOf_mk, ht]
    exact even_iff_two_dvd.2 (h2 ▸ orderOf_dvd_natCard _)
  · intro h hh
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
    have hu2 : orderOf (u : Y) = 2 := by rw [orderOf_coe, hu]
    have huK : (u : Y) ∈ K := u.2.1
    obtain ⟨v, hvK, hvu⟩ := u.2.2
    have e : h * v * h⁻¹ = u := by simpa [MulAut.conj_apply] using hvu
    have hv2 : orderOf v = 2 := by
      rw [← hu2, ← e, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    obtain ⟨k, hk, hkt⟩ :=
      SeitzReduction.exists_conj_eq_of_forall_card_le_two hK2 htK ht huK hu2
    obtain ⟨k', hk', hk't⟩ :=
      SeitzReduction.exists_conj_eq_of_forall_card_le_two hK2 htK ht hvK hv2
    have hy : k⁻¹ * h * k' ∈ centralizer ({t} : Set Y) := by
      rw [mem_centralizer_singleton_iff]
      calc k⁻¹ * h * k' * t = k⁻¹ * (h * (k' * t * k'⁻¹) * h⁻¹) * (h * k') := by group
        _ = k⁻¹ * (u : Y) * (h * k') := by rw [hk't, e]
        _ = k⁻¹ * (k * t * k⁻¹) * (h * k') := by rw [hkt]
        _ = t * (k⁻¹ * h * k') := by group
    apply hh
    rw [show h = k * (k⁻¹ * h * k') * k'⁻¹ by group]
    exact mul_mem (mul_mem (le_normalizer hk) (hNDK (hCtN hy))) (inv_mem (le_normalizer hk'))
  · intro h hcomm
    have hle' : D.map (MulAut.conj h).toMonoidHom ≤ K := by
      rw [commutator_comm] at hcomm
      exact commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hperf : ⁅D.map (MulAut.conj h).toMonoidHom, D.map (MulAut.conj h).toMonoidHom⁆ =
        D.map (MulAut.conj h).toMonoidHom := by
      rw [← map_commutator, isPerfect_iff.mp ⟨hDq.1⟩]
    have hbot := SeitzReduction.perfect_eq_bot_of_forall_card_le_two hK2 hle' hperf
    rw [map_eq_bot_iff_of_injective _ (MulAut.conj h).injective] at hbot
    exact SeitzReduction.ne_bot_of_isQuasisimple hDq hbot

theorem isQuasisimple_center_eq_bot_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q ∧ center Q = ⊥ := by
  obtain ⟨h, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hQ
  exact ⟨⟨h.1.commutator_eq_top, h.2.1⟩, hZ⟩

theorem subgroupOf_normal_of_centralizer_eq {Y : Type*} [Group Y] {z : Y} {H : Subgroup Y}
    (hC : centralizer ({z} : Set Y) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set Y)) :
    (H.subgroupOf (centralizer ({z} : Set Y))).Normal := by
  refine (normal_subgroupOf_iff_le_normalizer
    (SeitzReduction.le_centralizer_of_mem_centralizer hz')).2 ?_
  rw [hC]
  exact sup_le le_normalizer (zpowers_le.2 (centralizer_le_normalizer _ hz'))

theorem centralizer_inf_centralizer_le_zpowers {Y : Type*} [Group Y] {z : Y} {H : Subgroup Y}
    (hZ : center H = ⊥) (hC : centralizer ({z} : Set Y) = H ⊔ zpowers z)
    (hz' : z ∈ centralizer (H : Set Y)) :
    centralizer (H : Set Y) ⊓ centralizer ({z} : Set Y) ≤ zpowers z := by
  intro x hx
  obtain ⟨hxH, hxz⟩ := mem_inf.1 hx
  have hle : zpowers z ≤ normalizer (H : Set Y) :=
    zpowers_le.2 (centralizer_le_normalizer _ hz')
  rw [hC] at hxz
  have hxz' : x ∈ ((H ⊔ zpowers z : Subgroup Y) : Set Y) := hxz
  rw [coe_mul_of_right_le_normalizer_left H (zpowers z) hle] at hxz'
  obtain ⟨h, hh, w, hw, rfl⟩ := Set.mem_mul.1 hxz'
  have hwC : w ∈ centralizer (H : Set Y) := zpowers_le.2 hz' hw
  have hhC : h ∈ centralizer (H : Set Y) := by
    have h1 := mul_mem hxH (inv_mem hwC)
    rwa [mul_inv_cancel_right] at h1
  have hhZ : (⟨h, hh⟩ : H) ∈ center H := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hhC g g.2)
  rw [hZ, mem_bot] at hhZ
  have h1 : h = 1 := congrArg Subtype.val hhZ
  rw [h1, one_mul]
  exact hw

theorem card_le_two_of_centralizer_eq {Y : Type*} [Group Y] [Finite Y] {z : Y} {H : Subgroup Y}
    (hz : orderOf z = 2) (hZ : center H = ⊥) (hC : centralizer ({z} : Set Y) = H ⊔ zpowers z)
    (hz' : z ∈ centralizer (H : Set Y)) (U : Subgroup Y) (hU : IsPGroup 2 U)
    (hUH : U ≤ centralizer (H : Set Y)) : Nat.card U ≤ 2 :=
  SeitzReduction.card_le_two_of_forall_le_inf_centralizer hz' hz (fun V _ hV => by
    calc Nat.card V ≤ Nat.card (zpowers z) :=
          card_le_of_le (hV.trans (centralizer_inf_centralizer_le_zpowers hZ hC hz'))
      _ = 2 := by rw [Nat.card_zpowers, hz]) hU hUH

theorem exists_isCyclic_sylow_of_card_le_two {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (h : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ K → Nat.card U ≤ 2) :
    ∃ S : Sylow 2 K, IsCyclic S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
  refine ⟨S, isCyclic_of_card_dvd_prime (p := 2) ?_⟩
  have hS : Nat.card S ≤ 2 := by
    rw [← card_map_of_injective K.subtype_injective]
    exact h _ (S.isPGroup'.map _) (map_subtype_le _)
  have h0 : 0 < Nat.card S := Nat.card_pos
  rcases Nat.lt_or_ge (Nat.card S) 2 with h1 | h1
  · rw [show Nat.card S = 1 by omega]
    exact one_dvd 2
  · rw [show Nat.card S = 2 by omega]

theorem standardComponentIsStandard_of_normal {Y : Type*} [Group Y] [Finite Y] {z : Y}
    {H : Subgroup Y} (hz : orderOf z = 2) (hHq : CFSG.Open.IsQuasisimple H)
    (hHt : H ≤ centralizer ({z} : Set Y))
    (hHn : (H.subgroupOf (centralizer ({z} : Set Y))).Normal)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U →
      U ≤ centralizer ({z} : Set Y) ⊓ centralizer (H : Set Y) → Nat.card U ≤ 2) :
    standardComponentIsStandard H ∧ ∃ S : Sylow 2 (centralizer (H : Set Y)), IsCyclic S := by
  have hK2 : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (H : Set Y) → Nat.card U ≤ 2 :=
    fun U hU hUH => SeitzReduction.card_le_two_of_forall_le_inf_centralizer
      (SeitzReduction.mem_centralizer_of_le_centralizer_singleton hHt) hz
      (fun V hV hVle => hsyl V hV (le_inf (hVle.trans inf_le_right) (hVle.trans inf_le_left)))
      hU hUH
  exact ⟨standardComponentIsStandard_of_card_le_two hz hHt hHn hHq hK2,
    exists_isCyclic_sylow_of_card_le_two hK2⟩

end CFSG.EvenSporadicStandard.M24Std
