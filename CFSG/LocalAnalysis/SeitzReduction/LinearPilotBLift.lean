module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.Inheritance
import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftF4
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)
open CFSG.ComponentClassification.M12Cover.CyclicKernel
  (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)

variable {G : Type*} [Group G]

section OddOrder

private theorem odd_card_of_forall_odd_orderOf [Finite G] {H : Subgroup G}
    (h : ∀ x ∈ H, Odd (orderOf x)) : Odd (Nat.card H) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have h1 := h g g.2
  rw [orderOf_submonoid, hg] at h1
  exact (Nat.not_even_iff_odd.2 h1) even_two

theorem sup_zpowers_odd_abelian [Finite G] {Y : Subgroup G} (hYc : Y ≤ centralizer (Y : Set G))
    (hYo : Odd (Nat.card Y)) {c : G} (hcY : c ∈ centralizer (Y : Set G))
    (hco : Odd (orderOf c)) :
    Y ⊔ zpowers c ≤ centralizer ((Y ⊔ zpowers c : Subgroup G) : Set G) ∧
      Odd (Nat.card (Y ⊔ zpowers c : Subgroup G)) := by
  have hcz : zpowers c ≤ centralizer (Y : Set G) := zpowers_le.2 hcY
  have hzz : zpowers c ≤ centralizer ((zpowers c : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (Commute.refl c) k).eq
  have hYz : Y ≤ centralizer ((zpowers c : Subgroup G) : Set G) := le_centralizer_iff.1 hcz
  refine ⟨sup_le (le_centralizer_iff.1 (sup_le hYc hcz))
    (le_centralizer_iff.1 (sup_le hYz hzz)), ?_⟩
  refine odd_card_of_forall_odd_orderOf fun x hx => ?_
  have hYN : Y ≤ normalizer ((zpowers c : Subgroup G) : Set G) :=
    hYz.trans (centralizer_le_normalizer _)
  have hx' : x ∈ ((Y ⊔ zpowers c : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hYN] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx'
  have hyz : Commute y z := (mem_centralizer_iff.1 (hcz hz) y hy)
  have hy1 : y ^ Nat.card Y = 1 := by
    have h1 : (⟨y, hy⟩ : Y) ^ Nat.card Y = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [coe_pow, coe_one] at h2
  have hz1 : z ^ orderOf c = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]
  have hpow : (y * z) ^ (Nat.card Y * orderOf c) = 1 := by
    rw [hyz.mul_pow, pow_mul, hy1, one_pow, one_mul, mul_comm, pow_mul, hz1, one_pow]
  exact (hYo.mul hco).of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)

theorem exists_odd_abelian_forall_odd_mem [Finite G] {Q X₀ : Subgroup G} (hX₀Q : X₀ ≤ Q)
    (hX₀c : X₀ ≤ centralizer (X₀ : Set G)) (hX₀o : Odd (Nat.card X₀)) :
    ∃ X : Subgroup G, X₀ ≤ X ∧ X ≤ Q ∧ X ≤ centralizer (X : Set G) ∧ Odd (Nat.card X) ∧
      ∀ c ∈ Q ⊓ centralizer (X : Set G), Odd (orderOf c) → c ∈ X := by
  suffices h : ∀ m : ℕ, ∀ Y : Subgroup G, Nat.card G - Nat.card Y = m → X₀ ≤ Y → Y ≤ Q →
      Y ≤ centralizer (Y : Set G) → Odd (Nat.card Y) →
      ∃ X : Subgroup G, X₀ ≤ X ∧ X ≤ Q ∧ X ≤ centralizer (X : Set G) ∧ Odd (Nat.card X) ∧
        ∀ c ∈ Q ⊓ centralizer (X : Set G), Odd (orderOf c) → c ∈ X from
    h _ X₀ rfl le_rfl hX₀Q hX₀c hX₀o
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Y hm hX₀Y hYQ hYc hYo
    by_cases hmax : ∀ c ∈ Q ⊓ centralizer (Y : Set G), Odd (orderOf c) → c ∈ Y
    · exact ⟨Y, hX₀Y, hYQ, hYc, hYo, hmax⟩
    · push Not at hmax
      obtain ⟨c, ⟨hcQ, hcY⟩, hco, hcn⟩ := hmax
      obtain ⟨hY'c, hY'o⟩ := sup_zpowers_odd_abelian hYc hYo hcY hco
      have hlt : Y < Y ⊔ zpowers c :=
        lt_of_le_of_ne le_sup_left fun h => hcn (h ▸ mem_sup_right (mem_zpowers c))
      have h1 : Nat.card Y < Nat.card (Y ⊔ zpowers c : Subgroup G) := card_lt_of_lt hlt
      have h2 : Nat.card (Y ⊔ zpowers c : Subgroup G) ≤ Nat.card G := card_le_card_group _
      exact ih _ (by omega) _ rfl (hX₀Y.trans le_sup_left) (sup_le hYQ (zpowers_le.2 hcQ))
        hY'c hY'o

end OddOrder

section Center

variable [Finite G]

theorem mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G))
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hX : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  intro c hc hct
  have hDLX : D ≤ L ⊓ centralizer (X : Set G) := hD ▸ map_subtype_le _
  have hcD : (c : G) ∈ centralizer (D : Set G) := by
    refine F4Pilot.mem_centralizer_of_mem_oddCore_of_commute htX (hDLX.trans inf_le_right)
      (fun d hd => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDLX hd).1))
      hDq (fun m hm d hd => ?_) hc hct
    have hd' : d ∈ inSubgroup layer (L ⊓ centralizer (X : Set G)) := hD ▸ hd
    have := layer_centralizer_normalized hLt hm hd'
    rwa [← hD] at this
  have hcodd : Odd (orderOf (c : G)) := by
    rw [orderOf_submonoid]
    exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd.of_dvd_nat
      ((oddCore (centralizer (X : Set G))).orderOf_dvd_natCard hc)
  have hct' : (c : G) * t = t * c := congrArg Subtype.val hct
  have hcX : (c : G) ∈ X :=
    hX _ ⟨⟨c.2, mem_centralizer_singleton_iff.2 hct'⟩, hcD⟩ hcodd
  rw [mem_center_iff]
  intro h
  exact Subtype.ext (mem_centralizer_iff.1 h.2 _ hcX).symm

omit [Finite G] in
theorem mk_mul_mk_eq_one {X : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htX : t ∈ centralizer (X : Set G)) :
    (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 :=
  Subtype.ext (by rw [coe_mul, ← sq, ← ht, pow_orderOf_eq_one, coe_one])

theorem hasBLift_of_forall_odd_mem {L : Subgroup G} {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hX : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X)
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E :=
  F4Pilot.hasBLift_of_le_center (mk_mul_mk_eq_one ht htX) hE htE hEt
    (mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hX)

theorem isComponent_oddCoreLift_of_forall_odd_mem {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hX : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X)
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : CFSG.IsComponent E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (htE' : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) :
    HasBLift E ∧ CFSG.IsComponent (oddCoreLift E) ∧
      (oddCoreLift E).map (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = E ∧
      (oddCore (centralizer (X : Set G))).subgroupOf (oddCoreLift E) ≤ center (oddCoreLift E) :=
  F4Pilot.isComponent_oddCoreLift_of_le_center (mk_mul_mk_eq_one ht htX) hE htE htE'
    (mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hX)

theorem hasBLift_sup_conj_of_forall_odd_mem {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hX : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X)
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : ⁅Kb, Kb⁆ = Kb)
    (hcomm : ⁅Kb, Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥) :
    HasBLift (Kb ⊔ Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) ∧
      HasBLift Kb :=
  F4Pilot.hasBLift_sup_conj_of_le_center (mk_mul_mk_eq_one ht htX) hKb hcomm
    (mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hX)

end Center

section Automizer

theorem mem_of_forall_fix_eq_conj {L : Subgroup G} {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {D Y : Subgroup G} (hYo : Odd (Nat.card Y))
    (hAut : ∀ β : MulAut L, (∀ x : L, (x : G) ∈ D → β x = x) →
      ∃ y : L, (y : G) ∈ Y ∧ β = MulAut.conj y)
    {c : G} (hct : c ∈ centralizer ({t} : Set G)) (hcD : c ∈ centralizer (D : Set G))
    (hco : Odd (orderOf c)) : c ∈ Y := by
  have hcN : c ∈ normalizer (L : Set G) := hLt hct
  set β := L.normalizerMonoidHom ⟨c, hcN⟩ with hβ
  have hβapp : ∀ a : L, ((β a : L) : G) = c * a * c⁻¹ := fun a => by
    simp [hβ, normalizerMonoidHom_apply_apply_coe]
  have hβD : ∀ x : L, (x : G) ∈ D → β x = x := fun x hx => by
    apply Subtype.ext
    rw [hβapp, ← mem_centralizer_iff.1 hcD _ hx, mul_inv_cancel_right]
  obtain ⟨y, hyY, hβy⟩ := hAut β hβD
  have hyt : (y : G) * t = t * y := mem_centralizer_iff.1 htC _ y.2
  have hcen : (y : G)⁻¹ * c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun l hl => ?_, ?_⟩
    · have h1 := congrArg Subtype.val (show β ⟨l, hl⟩ = y * ⟨l, hl⟩ * y⁻¹ by
        rw [hβy, MulAut.conj_apply])
      rw [hβapp] at h1
      simp only [coe_mul, coe_inv] at h1
      calc l * ((y : G)⁻¹ * c) = (y : G)⁻¹ * ((y : G) * l * (y : G)⁻¹) * c := by group
        _ = (y : G)⁻¹ * (c * l * c⁻¹) * c := by rw [h1]
        _ = (y : G)⁻¹ * c * l := by group
    · rw [mem_centralizer_singleton_iff]
      have hct' : c * t = t * c := mem_centralizer_singleton_iff.1 hct
      have hyt' : (y : G)⁻¹ * t = t * (y : G)⁻¹ := by
        calc (y : G)⁻¹ * t = (y : G)⁻¹ * (t * y) * (y : G)⁻¹ := by group
          _ = (y : G)⁻¹ * ((y : G) * t) * (y : G)⁻¹ := by rw [hyt]
          _ = t * (y : G)⁻¹ := by group
      calc (y : G)⁻¹ * c * t = (y : G)⁻¹ * (c * t) := by group
        _ = (y : G)⁻¹ * (t * c) := by rw [hct']
        _ = ((y : G)⁻¹ * t) * c := by group
        _ = (t * (y : G)⁻¹) * c := by rw [hyt']
        _ = t * ((y : G)⁻¹ * c) := by group
  rw [hK] at hcen
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hcen with h1 | h1
  · have hcy : c = y := by
      calc c = (y : G) * ((y : G)⁻¹ * c) := by group
        _ = y := by rw [h1, mul_one]
    rw [hcy]
    exact hyY
  · exfalso
    have hcy : c = y * t := by
      calc c = (y : G) * ((y : G)⁻¹ * c) := by group
        _ = y * t := by rw [h1]
    obtain ⟨j, hj⟩ := hco
    have hpow : c ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have htt : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [hcy, (show Commute (y : G) t from hyt).mul_pow, pow_succ t, pow_mul, htt, one_pow,
      one_mul] at hpow
    have htY : t ∈ Y := by
      have : t = ((y : G) ^ (2 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [this]
      exact Y.inv_mem (Y.pow_mem hyY _)
    have h2 := Y.orderOf_dvd_natCard htY
    rw [ht] at h2
    exact (Nat.not_even_iff_odd.2 hYo) (even_iff_two_dvd.2 h2)

end Automizer

section Layer

theorem inSubgroup_layer_inf_centralizer_eq_of_le {L X₀ X D : Subgroup G} (hX₀X : X₀ ≤ X)
    (hDX : D ≤ L ⊓ centralizer (X : Set G))
    (hcomm : ∀ g ∈ L ⊓ centralizer (X₀ : Set G), ∀ h ∈ L ⊓ centralizer (X₀ : Set G),
      g * h * g⁻¹ * h⁻¹ ∈ D) (hD : CFSG.IsQuasisimple D) :
    inSubgroup layer (L ⊓ centralizer (X : Set G)) = D := by
  have hle : L ⊓ centralizer (X : Set G) ≤ L ⊓ centralizer (X₀ : Set G) :=
    inf_le_inf_left _ (centralizer_le hX₀X)
  exact (inSubgroup_layer_eq_of_commutator_mem hDX
    (fun g hg h hh => hcomm g (hle hg) h (hle hh)) hD)

theorem commutator_mem_map_symm_of_mem_inf_centralizer {C : Type*} [Group C] {L : Subgroup G}
    (e : L ≃* C) {A D : Subgroup C}
    (hcomm : ∀ g ∈ centralizer (A : Set C), ∀ h ∈ centralizer (A : Set C),
      g * h * g⁻¹ * h⁻¹ ∈ D) :
    ∀ g ∈ L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G),
      ∀ h ∈ L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G),
        g * h * g⁻¹ * h⁻¹ ∈ (D.map e.symm.toMonoidHom).map L.subtype := by
  rw [F4Pilot.inf_centralizer_map_symm]
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩ _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
  refine ⟨e.symm.toMonoidHom (g * h * g⁻¹ * h⁻¹), ⟨_, hcomm g hg h hh, rfl⟩, ?_⟩
  simp

end Layer

end CFSG.SeitzReduction.LinearPilot
