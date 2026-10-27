module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftF4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainRows
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.M12Cover.CyclicKernel
  (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)
open CFSG.SeitzReduction.F4Pilot (F4Work HasBLift)

section Generic

variable {G : Type*} [Group G] {L : Subgroup G} {C : Type*} [Group C]

theorem exists_mem_inv_mul_mem_zpowers_of_fix [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* C) {DC : Subgroup C}
    (hfix : ∀ β : MulAut C, (∀ x ∈ DC, β x = x) →
      ∃ g : C, β = MulAut.conj g ∧ g ∈ centralizer (DC : Set C))
    (hZ : center DC = ⊥) {X : Subgroup G} {Y : Subgroup C}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup C) : Set C) ≤ Y ⊔ DC)
    (hYD : Y ≤ centralizer (DC : Set C))
    {D : Subgroup G} (hDe : D = (DC.map e.symm.toMonoidHom).map L.subtype) {c : G}
    (hcX : c ∈ centralizer (X : Set G)) (hct : c * t = t * c)
    (hcD : c ∈ centralizer (D : Set G)) :
    ∃ y ∈ (Y.map e.symm.toMonoidHom).map L.subtype, y⁻¹ * c ∈ zpowers t := by
  set XC : Subgroup C := (X.subgroupOf L).map e.toMonoidHom with hXCdef
  have hcN : c ∈ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
      (mem_centralizer_singleton_iff.2 hct)
  set β := L.normalizerMonoidHom ⟨c, hcN⟩ with hβ
  have hβapp : ∀ a : L, ((β a : L) : G) = c * a * c⁻¹ := fun a => by
    simp [hβ, normalizerMonoidHom_apply_apply_coe]
  have hβ'app : ∀ x, MulAut.congr e β x = e (β (e.symm x)) := fun x => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hfixD : ∀ x ∈ DC, MulAut.congr e β x = x := by
    intro x hxD
    have hmem : ((e.symm x : L) : G) ∈ D := by
      rw [hDe]
      exact ⟨e.symm x, ⟨x, hxD, rfl⟩, rfl⟩
    have h1 : β (e.symm x) = e.symm x := by
      apply Subtype.ext
      rw [hβapp, ← mem_centralizer_iff.1 hcD _ hmem, mul_inv_cancel_right]
    rw [hβ'app, h1, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg, hgD⟩ := hfix _ hfixD
  have hgX : g ∈ centralizer (XC : Set C) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 : β a = a := by
      apply Subtype.ext
      rw [hβapp, ← mem_centralizer_iff.1 hcX _ (mem_subgroupOf.1 ha), mul_inv_cancel_right]
    have h2 : MulAut.congr e β (e a) = e a := by
      rw [hβ'app, MulEquiv.symm_apply_apply, h1]
    rw [hg, MulAut.conj_apply] at h2
    calc e.toMonoidHom a * g = g * e a * g⁻¹ * g := by rw [h2]; rfl
      _ = g * e.toMonoidHom a := by simp
  have hgY : g ∈ Y := F4Pilot.mem_of_mem_sup_of_mem_centralizer hYD hZ (hXc hgX) hgD
  set a₀ : L := e.symm g with ha₀
  have hga₀ : e a₀ = g := by rw [ha₀, MulEquiv.apply_symm_apply]
  have hβa : ∀ l : L, β l = a₀ * l * a₀⁻¹ := by
    intro l
    have h1 : MulAut.congr e β (e l) = g * e l * g⁻¹ := by rw [hg, MulAut.conj_apply]
    rw [hβ'app, MulEquiv.symm_apply_apply, ← hga₀] at h1
    apply e.injective
    rw [h1]
    simp
  have hcen : (a₀ : G)⁻¹ * c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun l hl => ?_, ?_⟩
    · have h1 := congrArg Subtype.val (hβa ⟨l, hl⟩)
      rw [hβapp] at h1
      simp only [coe_mul, coe_inv] at h1
      calc l * ((a₀ : G)⁻¹ * c) = (a₀ : G)⁻¹ * ((a₀ : G) * l * (a₀ : G)⁻¹) * c := by group
        _ = (a₀ : G)⁻¹ * (c * l * c⁻¹) * c := by rw [h1]
        _ = (a₀ : G)⁻¹ * c * l := by group
    · rw [mem_centralizer_singleton_iff]
      have hta : (a₀ : G) * t = t * a₀ := mem_centralizer_iff.1 htC _ a₀.2
      have hta' : (a₀ : G)⁻¹ * t = t * (a₀ : G)⁻¹ := by
        calc (a₀ : G)⁻¹ * t = (a₀ : G)⁻¹ * (t * a₀) * (a₀ : G)⁻¹ := by group
          _ = (a₀ : G)⁻¹ * ((a₀ : G) * t) * (a₀ : G)⁻¹ := by rw [hta]
          _ = t * (a₀ : G)⁻¹ := by group
      calc (a₀ : G)⁻¹ * c * t = (a₀ : G)⁻¹ * (c * t) := by group
        _ = (a₀ : G)⁻¹ * (t * c) := by rw [hct]
        _ = ((a₀ : G)⁻¹ * t) * c := by group
        _ = (t * (a₀ : G)⁻¹) * c := by rw [hta']
        _ = t * ((a₀ : G)⁻¹ * c) := by group
  rw [hK] at hcen
  exact ⟨a₀, ⟨a₀, ⟨g, hgY, rfl⟩, rfl⟩, hcen⟩

theorem mem_map_of_mem_oddCore_of_commute_of_fix [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* C) {DC : Subgroup C}
    (hfix : ∀ β : MulAut C, (∀ x ∈ DC, β x = x) →
      ∃ g : C, β = MulAut.conj g ∧ g ∈ centralizer (DC : Set C))
    (hZ : center DC = ⊥) {X : Subgroup G} {Y : Subgroup C}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup C) : Set C) ≤ Y ⊔ DC)
    (hYD : Y ≤ centralizer (DC : Set C)) (hYodd : Odd (Nat.card Y))
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = (DC.map e.symm.toMonoidHom).map L.subtype)
    (hDq : CFSG.IsQuasisimple D) (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    {c : centralizer (X : Set G)} (hc : c ∈ oddCore (centralizer (X : Set G)))
    (hct : c * ⟨t, htX⟩ = ⟨t, htX⟩ * c) :
    (c : G) ∈ (Y.map e.symm.toMonoidHom).map L.subtype := by
  have hOodd : Odd (Nat.card (oddCore (centralizer (X : Set G)))) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  have hDLX : D ≤ L ⊓ centralizer (X : Set G) := hD ▸ map_subtype_le _
  have hcD : (c : G) ∈ centralizer (D : Set G) := by
    refine F4Pilot.mem_centralizer_of_mem_oddCore_of_commute htX (hDLX.trans inf_le_right)
      (fun d hd => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDLX hd).1))
      hDq (fun m hm d hd => ?_) hc hct
    have hd' : d ∈ inSubgroup layer (L ⊓ centralizer (X : Set G)) := hD ▸ hd
    have := layer_centralizer_normalized hLt hm hd'
    rwa [← hD] at this
  obtain ⟨y, hy, hyc⟩ := exists_mem_inv_mul_mem_zpowers_of_fix hL htC ht hK e hfix hZ hXc hYD
    hDe c.2 (congrArg Subtype.val hct) hcD
  set Y' : Subgroup G := (Y.map e.symm.toMonoidHom).map L.subtype with hY'
  have hY'L : Y' ≤ L := map_subtype_le _
  have hY'odd : Odd (Nat.card Y') := by
    rw [hY', card_map_of_injective L.subtype_injective,
      card_map_of_injective e.symm.injective]
    exact hYodd
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hyc with h1 | h1
  · have hcy : (c : G) = y := by
      calc (c : G) = y * (y⁻¹ * c) := by group
        _ = y := by rw [h1, mul_one]
    rw [hcy]
    exact hy
  · exfalso
    have hcodd : Odd (orderOf (c : G)) := by
      rw [orderOf_submonoid]
      exact hOodd.of_dvd_nat ((oddCore (centralizer (X : Set G))).orderOf_dvd_natCard hc)
    have hyt : y * t = t * y := mem_centralizer_iff.1 htC y (hY'L hy)
    have hcy : (c : G) = y * t := by
      calc (c : G) = y * (y⁻¹ * c) := by group
        _ = y * t := by rw [h1]
    obtain ⟨j, hj⟩ := hcodd
    have hpow : (c : G) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have htt : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [hcy, (show Commute y t from hyt).mul_pow, pow_succ t, pow_mul, htt, one_pow,
      one_mul] at hpow
    have htY : t ∈ Y' := by
      have : t = (y ^ (2 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [this]
      exact Y'.inv_mem (Y'.pow_mem hy _)
    have h2 := Y'.orderOf_dvd_natCard htY
    rw [ht] at h2
    exact (Nat.not_even_iff_odd.2 hY'odd) (even_iff_two_dvd.2 h2)

theorem mem_center_of_mem_oddCore_of_commute_sup_of_fix [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* C) {DC : Subgroup C}
    (hfix : ∀ β : MulAut C, (∀ x ∈ DC, β x = x) →
      ∃ g : C, β = MulAut.conj g ∧ g ∈ centralizer (DC : Set C))
    (hZ : center DC = ⊥) (hDCq : CFSG.IsQuasisimple DC) {A Y : Subgroup C}
    (hA : centralizer (A : Set C) = Y ⊔ DC) (hYD : Y ≤ centralizer (DC : Set C))
    (hYc : Y ≤ centralizer (Y : Set C)) (hYodd : Odd (Nat.card Y)) (hYA : Y ≤ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  set D : Subgroup G := (DC.map e.symm.toMonoidHom).map L.subtype with hDe
  have hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup C) : Set C) ≤
      Y ⊔ DC := by
    rw [hX, F4Pilot.map_subgroupOf_map_symm]
    exact hA.le
  have hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) := by
    rw [hX, F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hA hYD hYc hDCq]
  have hDq : CFSG.IsQuasisimple D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((DC.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
        ((DC.map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)) hDCq
  intro c hc hct
  have hcY := mem_map_of_mem_oddCore_of_commute_of_fix hL htC ht hK e hfix hZ hXc hYD hYodd htX
    rfl hDq hD hc hct
  have hAX : ∀ y : G, y ∈ (A.map e.symm.toMonoidHom).map L.subtype → y ∈ X := fun y hy => by
    rw [hX]
    exact hy
  have hcX : (c : G) ∈ X := hAX _ (map_mono (map_mono hYA) hcY)
  rw [mem_center_iff]
  intro h
  exact Subtype.ext (mem_centralizer_iff.1 h.2 _ hcX).symm

end Generic

section E6


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem mem_center_of_mem_oddCore_of_commute_rootTorusG {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .E6 K)
    (htX : t ∈ centralizer (rootTorusG e : Set G)) :
    ∀ c ∈ oddCore (centralizer (rootTorusG e : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (rootTorusG e : Set G)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hTodd : Odd (Nat.card ((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (highTorusLine_le_adjointGroup (Or.inl rfl))).toEquiv]
    exact odd_card_highTorusLine hw.one_le hw.card_eq
  exact mem_center_of_mem_oddCore_of_commute_sup_of_fix hw.standard.standard hw.mem_centralizer
    hw.orderOf_eq hw.inf_eq e (exists_eq_conj_of_fix_a5Levi hq) center_a5Levi_eq_bot
    isQuasisimple_a5Levi (centralizer_highTorusLine_eq (Or.inl rfl) hq)
    highTorusLine_subgroupOf_le_centralizer_perpLevi highTorusLine_subgroupOf_le_centralizer_self
    hTodd le_rfl rfl htX

theorem hasBLift_rootTorusG {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .E6 K) (htX : t ∈ centralizer (rootTorusG e : Set G))
    {E : Subgroup (centralizer (rootTorusG e : Set G) ⧸
      oddCore (centralizer (rootTorusG e : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (rootTorusG e : Set G) ⧸
        oddCore (centralizer (rootTorusG e : Set G)))))
    (hEt : E ≤ ⁅E, zpowers
      (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E := by
  have htt : (⟨t, htX⟩ : centralizer (rootTorusG e : Set G)) * ⟨t, htX⟩ = 1 :=
    Subtype.ext (by rw [coe_mul, ← sq, ← hw.orderOf_eq, pow_orderOf_eq_one, coe_one])
  exact F4Pilot.hasBLift_of_le_center htt hE htE hEt
    (mem_center_of_mem_oddCore_of_commute_rootTorusG hw hf e htX)

end E6

end CFSG.SeitzReduction.E6Pilot
