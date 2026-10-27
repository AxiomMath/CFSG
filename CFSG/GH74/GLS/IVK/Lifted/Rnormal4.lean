module

public import CFSG.GH74.GLS.IVK.Lifted.DSDGroup
public import CFSG.GH74.GLS.IVK.Lifted.Quat44
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue1
public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

section Abstract

variable {M : Type} [Group M] [Finite M]

theorem dsd_cent_eq {A : Subgroup M} (hM2 : IsPGroup 2 M) (hA : IsCyclic ↥A) {u : M} (hu : u ∈ A)
    (hu4 : orderOf u = 4) (hinv : ∀ x : M, x ∉ A → x * u * x⁻¹ = u⁻¹) {y : M} (hy : y ∉ A) {a : M}
    (ha : a ∈ A) (hya : y * a = a * y) : a = 1 ∨ a = u * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu4' := pow_four_aux hu4
  have huu2 : (u * u) * (u * u) = 1 := by
    calc (u * u) * (u * u) = u * (u * (u * u)) := by group
      _ = 1 := hu4'
  have huu1 : u * u ≠ 1 := by
    intro h
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hu4] at this
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hM2) a
  rcases Nat.lt_or_ge k 2 with hlt | hge
  · interval_cases k
    · exact hcon.1 (orderOf_eq_one_iff.1 (by simpa using hk))
    · have ha2 : a * a = 1 := by
        have := pow_orderOf_eq_one a
        rw [hk] at this
        simpa [pow_two] using this
      exact hcon.2 (B.cyclic_invol_unique hA ha (A.mul_mem hu hu) ha2 huu2 hcon.1 huu1)
  · have ha₄o : orderOf (a ^ (2 ^ (k - 2))) = 4 := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk]
      have : (2 : ℕ) ^ k = 4 * 2 ^ (k - 2) := by
        rw [show k = (k - 2) + 2 by omega, pow_add]
        simp
        ring
      rw [this]
      exact Nat.mul_div_cancel _ (by positivity)
    have ha₄A : a ^ (2 ^ (k - 2)) ∈ A := A.pow_mem ha _
    have hyc : y * a ^ (2 ^ (k - 2)) = a ^ (2 ^ (k - 2)) * y :=
      (Commute.pow_right (show Commute y a from hya) _).eq
    have hyu : y * u * y⁻¹ = u := by
      rcases eq_or_inv_of_orderOf_four hA hu ha₄A hu4 ha₄o with h | h
      · rw [h] at hyc
        exact mul_inv_eq_iff_eq_mul.2 hyc
      · rw [h] at hyc
        have h1 : y * u⁻¹ * y⁻¹ = u⁻¹ := mul_inv_eq_iff_eq_mul.2 hyc
        calc y * u * y⁻¹ = (y * u⁻¹ * y⁻¹)⁻¹ := by group
          _ = u := by rw [h1, inv_inv]
    have := hinv y hy
    rw [hyu] at this
    apply huu1
    calc u * u = u⁻¹ * u := by rw [← this]
      _ = 1 := inv_mul_cancel u

theorem no_dsd_central_prod (hM2 : IsPGroup 2 M) (hD : DSDData M) {P : Subgroup M} {z q : M}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ g : M, g * z = z * g)
    (hP : ∃ n, IVK.IsQuaternionTwoGroup ↥P n) (hq1 : q ≠ 1) (hqz : q ≠ z)
    (hqc : ∀ p ∈ P, p * q = q * p) : False := by
  classical
  obtain ⟨A, u, hA, hu, hu4, hout, hinv⟩ := hD
  obtain ⟨huz, -, -⟩ := dsd_core hA hu hu4 hout hinv hz2 hz1 hzc
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((hA.isMulCommutative).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨n, hn3, ⟨ι⟩⟩ := hP
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hN2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hxa_ord : ∀ i : ZMod (2 * 2 ^ (n - 2)),
      orderOf ((ι.symm (QuaternionGroup.xa i) : ↥P) : M) = 4 := by
    intro i
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa i
  have hgo : orderOf ((ι.symm (QuaternionGroup.a 1) : ↥P) : M) = 2 * 2 ^ (n - 2) := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_a_one
  set g : M := ((ι.symm (QuaternionGroup.a 1) : ↥P) : M) with hg
  set x : M := ((ι.symm (QuaternionGroup.xa 0) : ↥P) : M) with hx
  have hgP : g ∈ P := (ι.symm (QuaternionGroup.a 1)).2
  have hxP : x ∈ P := (ι.symm (QuaternionGroup.xa 0)).2
  have hgx : g * x ≠ x * g := by
    intro h
    apply quat_mul_ne hN2
    have h1 : ι.symm (QuaternionGroup.a 1) * ι.symm (QuaternionGroup.xa 0) =
        ι.symm (QuaternionGroup.xa 0) * ι.symm (QuaternionGroup.a 1) := Subtype.ext h
    have h2 := congrArg ι h1
    simpa using h2
  have hprod : ∀ y₁ y₂ : M, y₁ ∉ A → y₂ ∉ A → y₁ * y₂ ∈ A := by
    intro y₁ y₂ h1 h2
    by_contra h12
    have e1 := hinv (y₁ * y₂) h12
    have e2 : y₁ * y₂ * u * (y₁ * y₂)⁻¹ = u := by
      calc y₁ * y₂ * u * (y₁ * y₂)⁻¹ = y₁ * (y₂ * u * y₂⁻¹) * y₁⁻¹ := by group
        _ = y₁ * u⁻¹ * y₁⁻¹ := by rw [hinv y₂ h2]
        _ = (y₁ * u * y₁⁻¹)⁻¹ := by group
        _ = u := by rw [hinv y₁ h1, inv_inv]
    rw [e2] at e1
    have hu1 : u * u ≠ 1 := by
      intro h
      have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hu4] at this
      omega
    apply hu1
    calc u * u = u⁻¹ * u := by rw [← e1]
      _ = 1 := inv_mul_cancel u
  have hex : (∃ p₀ ∈ P, p₀ ∉ A) ∧ ∃ a₀ ∈ P, a₀ ∈ A ∧ 4 ≤ orderOf a₀ := by
    by_cases hgA : g ∈ A
    · by_cases hxA : x ∈ A
      · exact absurd (hAcomm g hgA x hxA) hgx
      · exact ⟨⟨x, hxP, hxA⟩, g, hgP, hgA, by rw [hgo]; omega⟩
    · by_cases hxA : x ∈ A
      · exact ⟨⟨g, hgP, hgA⟩, x, hxP, hxA, by rw [hxa_ord]⟩
      · refine ⟨⟨g, hgP, hgA⟩, g * x, P.mul_mem hgP hxP, hprod g x hgA hxA, ?_⟩
        have e : g * x = ((ι.symm (QuaternionGroup.xa (0 - 1)) : ↥P) : M) := by
          have : ι.symm (QuaternionGroup.a 1) * ι.symm (QuaternionGroup.xa 0) =
              ι.symm (QuaternionGroup.xa (0 - 1)) := by
            rw [← map_mul, QuaternionGroup.a_mul_xa]
          exact congrArg Subtype.val this
        rw [e, hxa_ord]
  by_cases hqA : q ∈ A
  · obtain ⟨p₀, hp₀P, hp₀A⟩ := hex.1
    rcases dsd_cent_eq hM2 hA hu hu4 hinv hp₀A hqA (hqc p₀ hp₀P) with h | h
    · exact hq1 h
    · exact hqz (h.trans huz)
  · obtain ⟨a₀, ha₀P, ha₀A, ha₀o⟩ := hex.2
    rcases dsd_cent_eq hM2 hA hu hu4 hinv hqA ha₀A (hqc a₀ ha₀P).symm with h | h
    · rw [h, orderOf_one] at ha₀o
      omega
    · rw [h, huz, hzo] at ha₀o
      omega

end Abstract

section Four

theorem isFourSubgroup_map {X Y : Type} [Group X] [Group Y] (f : X →* Y) (hf : Function.Injective f)
    {E : Subgroup X} (hE : IsElementaryAbelian 2 ↥E) (hc : Nat.card ↥E = 2 ^ 2) :
    IVK.IsFourSubgroup (E.map f) := by
  refine ⟨?_, ?_⟩
  · have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b =>
      hE.toIsMulCommutative.is_comm.comm a b
    have hexp : ∀ a : ↥E, a ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 2 ↥E)
    refine
      { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun a => ?_) }
    · obtain ⟨a', ha', ha''⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb', hb''⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      show (a : Y) * b = b * a
      rw [← ha'', ← hb'', ← map_mul, ← map_mul]
      exact congrArg f (congrArg Subtype.val (hcomm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · obtain ⟨a', ha', ha''⟩ := Subgroup.mem_map.1 a.2
      apply Subtype.ext
      show (a : Y) ^ 2 = 1
      rw [← ha'', ← map_pow]
      have h2 : a' ^ 2 = 1 := by simpa using congrArg Subtype.val (hexp ⟨a', ha'⟩)
      rw [h2, map_one]
  · rw [Nat.card_congr (E.equivMapOfInjective f hf).toEquiv.symm, hc]
    norm_num

end Four

section Main

open CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G]

theorem rnormal4 (hII : II4_4_4_center) : Rnormal4 := by
  intro G _ _ z S K F h hQne
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPq := ii4_4_quat G h.simple z h.orderOf_z S K h.sylow h.comp_isPCompIn h.comp_pRank
  rw [h.Qz_eq] at hQne
  rw [h.Rz_eq]
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have hzP := h.z_mem_P hII
  have hzQ := h.z_mem_Q hII
  have hcomm : ∀ p ∈ S ⊓ K, ∀ q ∈ S ⊓ cSec K, p * q = q * p := fun p hp q hq => h.comm_PQ hp hq
  have hS2 : IsPGroup 2 ↥S := h.S_pgroup
  have hRS : (S ⊓ K) ⊔ (S ⊓ cSec K) ≤ S := sup_le inf_le_left inf_le_left
  have hRn : ∀ s ∈ S, ∀ r ∈ (S ⊓ K) ⊔ (S ⊓ cSec K), s * r * s⁻¹ ∈ (S ⊓ K) ⊔ (S ⊓ cSec K) := by
    intro s hs r hr
    obtain ⟨p, hp, q, hq, rfl⟩ := M.mem_sup_of_commute hcomm hr
    have e : s * (p * q) * s⁻¹ = (s * p * s⁻¹) * (s * q * s⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left (h.P_norm hs hp)) (mem_sup_right (h.Q_norm hs hq))
  obtain ⟨q, hqQ, hqz'⟩ :=
    IsConcreteLE.exists_of_lt (lt_of_le_of_ne (zpowers_le.2 hzQ) (Ne.symm hQne))
  have hq1 : q ≠ 1 := fun h1 => hqz' (h1 ▸ one_mem _)
  have hqz : q ≠ z := fun h1 => hqz' (h1 ▸ mem_zpowers z)
  have hqS : q ∈ S := hqQ.1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨q, hqS⟩
  have hqo : orderOf q = 2 ^ k := (Subgroup.orderOf_mk q hqS).symm.trans hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (orderOf_eq_one_iff.1 (by rw [hqo, h0]; rfl)) hq1
    · exact h0
  set t : G := q ^ (2 ^ (k - 1)) with ht
  have hto : orderOf t = 2 := by
    rw [ht, orderOf_pow_of_dvd (by positivity) (by rw [hqo]; exact pow_dvd_pow 2 (by omega)), hqo]
    have : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    exact Nat.mul_div_cancel _ (by positivity)
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hto
  have ht1 : t ≠ 1 := ne_one_of_orderOf_eq_two hto
  have htQ : t ∈ S ⊓ cSec K := (S ⊓ cSec K).pow_mem hqQ _
  have hex : ∃ v ∈ (S ⊓ K) ⊔ (S ⊓ cSec K), v * v = 1 ∧ v ≠ 1 ∧ v ≠ z := by
    by_cases htz : t = z
    · have hk2 : 2 ≤ k := by
        by_contra hlt
        have h1k : k = 1 := by omega
        apply hqz
        rw [← htz, ht, h1k]
        simp
      set q₄ : G := q ^ (2 ^ (k - 2)) with hq₄
      have hq₄Q : q₄ ∈ S ⊓ cSec K := (S ⊓ cSec K).pow_mem hqQ _
      have hq₄sq : q₄ * q₄ = z := by
        rw [← htz, ht, hq₄, ← pow_add]
        congr 1
        rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
        ring
      obtain ⟨n, hn3, ⟨ι⟩⟩ := hPq
      have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
      set u₁ : G := ((ι.symm (QuaternionGroup.xa 0) : ↥(S ⊓ K)) : G) with hu₁
      have hu₁P : u₁ ∈ S ⊓ K := (ι.symm (QuaternionGroup.xa 0)).2
      have hu₁o : orderOf u₁ = 4 := by
        rw [hu₁, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
        exact QuaternionGroup.orderOf_xa 0
      have hu₁sqo : orderOf (u₁ * u₁) = 2 := by
        rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hu₁o]; norm_num), hu₁o]
      have hu₁sq : u₁ * u₁ = z := by
        have hmem : u₁ * u₁ ∈ S ⊓ K := (S ⊓ K).mul_mem hu₁P hu₁P
        rcases h.P_inv hII hmem (mul_self_eq_one_of_orderOf_eq_two hu₁sqo) with h1 | h1
        · exact absurd h1 (ne_one_of_orderOf_eq_two hu₁sqo)
        · exact h1
      have hq₄notP : q₄ ∉ S ⊓ K := by
        intro hq₄P
        rcases h.PQ_inf hII hq₄P hq₄Q with h1 | h1
        · rw [h1, one_mul] at hq₄sq
          exact hz1 hq₄sq.symm
        · rw [h1, hz2] at hq₄sq
          exact hz1 hq₄sq.symm
      have hcom := hcomm u₁ hu₁P q₄ hq₄Q
      refine ⟨u₁ * q₄, mul_mem (mem_sup_left hu₁P) (mem_sup_right hq₄Q), ?_, ?_, ?_⟩
      · calc (u₁ * q₄) * (u₁ * q₄) = u₁ * (q₄ * u₁) * q₄ := by group
          _ = u₁ * (u₁ * q₄) * q₄ := by rw [← hcom]
          _ = (u₁ * u₁) * (q₄ * q₄) := by group
          _ = 1 := by rw [hu₁sq, hq₄sq, hz2]
      · intro h1
        apply hq₄notP
        have : q₄ = u₁⁻¹ := by
          have := congrArg (fun w => u₁⁻¹ * w) h1
          simpa using this
        rw [this]
        exact (S ⊓ K).inv_mem hu₁P
      · intro h1
        apply hq₄notP
        have : q₄ = u₁⁻¹ * z := by
          have := congrArg (fun w => u₁⁻¹ * w) h1
          simpa using this
        rw [this]
        exact (S ⊓ K).mul_mem ((S ⊓ K).inv_mem hu₁P) hzP
    · exact ⟨t, mem_sup_right htQ, ht2, ht1, htz⟩
  obtain ⟨v, hvR, hv2, hv1, hvz⟩ := hex
  have hzR : z ∈ (S ⊓ K) ⊔ (S ⊓ cSec K) := mem_sup_left hzP
  have hrankR : 2 ≤ CFSG.Open.pRank 2 ((S ⊓ K) ⊔ (S ⊓ cSec K)) :=
    two_le_pRank_of_pair hz2 hv2 (h.z_cent (hRS hvR)) hz1 hv1 (Ne.symm hvz) hzR hvR
  have hrank : 2 ≤ pRank 2 ↥(((S ⊓ K) ⊔ (S ⊓ cSec K)).subgroupOf S) := by
    rw [pRank_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hRS),
      TwoThin.pRank_two_subgroup_eq_open]
    exact hrankR
  have hnormal : (((S ⊓ K) ⊔ (S ⊓ cSec K)).subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hRn (g : G) g.2 (n : G) hn
  rcases CFSG.GH74.Uniqueness.SU.SU1.b_normal_Ep2 2 Nat.prime_two ↥S hS2 _ hnormal hrank with
    ⟨E, hEn, hER, hEel, hE4⟩ | ⟨-, hD | hSD⟩
  · refine ⟨E.map S.subtype, ?_, isFourSubgroup_map S.subtype S.subtype_injective hEel hE4, ?_⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_subgroupOf.1 (hER he)
    · intro s hs x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_map.2 ⟨⟨s, hs⟩ * e * ⟨s, hs⟩⁻¹, hEn.conj_mem e he ⟨s, hs⟩, rfl⟩
  all_goals
    exfalso
    have hqR : q ∈ (S ⊓ K) ⊔ (S ⊓ cSec K) := mem_sup_right hqQ
    have hfinal : DSDData ↥((S ⊓ K) ⊔ (S ⊓ cSec K)) → False := by
      intro hD
      refine no_dsd_central_prod (M := ↥((S ⊓ K) ⊔ (S ⊓ cSec K))) (hS2.to_le hRS) hD
        (P := (S ⊓ K).subgroupOf ((S ⊓ K) ⊔ (S ⊓ cSec K))) (z := ⟨z, hzR⟩) (q := ⟨q, hqR⟩)
        (Subtype.ext hz2) (fun h1 => hz1 (congrArg Subtype.val h1)) ?_ ?_
        (fun h1 => hq1 (congrArg Subtype.val h1)) (fun h1 => hqz (congrArg Subtype.val h1)) ?_
      · intro g
        exact Subtype.ext (h.z_cent (hRS g.2)).symm
      · obtain ⟨n, hn3, ⟨ι⟩⟩ := hPq
        exact ⟨n, hn3, ⟨(Subgroup.subgroupOfEquivOfLe le_sup_left).trans ι⟩⟩
      · intro p hp
        exact Subtype.ext (hcomm (p : G) hp q hqQ)
    have hψ := Subgroup.subgroupOfEquivOfLe hRS
    have hPcard : 8 ≤ Nat.card ↥(S ⊓ K) := by
      obtain ⟨n, hn3, ⟨ι⟩⟩ := hPq
      have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
      rw [Nat.card_congr ι.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      have : 2 ≤ 2 ^ (n - 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hPle : Nat.card ↥(S ⊓ K) ≤ Nat.card ↥((S ⊓ K) ⊔ (S ⊓ cSec K)) :=
      Subgroup.card_le_of_le le_sup_left
    rw [← Nat.card_congr hψ.toEquiv] at hPle
  · obtain ⟨m, hm1, ⟨e⟩⟩ := hD
    have : NeZero (2 ^ m) := ⟨by positivity⟩
    have hcardR : Nat.card ↥(((S ⊓ K) ⊔ (S ⊓ cSec K)).subgroupOf S) = 2 * 2 ^ m := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    rw [hcardR] at hPle
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have : m = 1 := by omega
      subst this
      omega
    exact hfinal (DSDData.congr hψ (DSDData.congr e.symm
      (dsdData_dihedral (2 ^ m) (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ m := pow_dvd_pow 2 hm2))))
  · obtain ⟨n', hn4, ⟨e⟩⟩ := hSD
    exact hfinal (DSDData.congr hψ (DSDData.congr e.symm (dsdData_semidihedral n' hn4)))

end Main

end CFSG.GH74.GLS.IVK.Lifted
