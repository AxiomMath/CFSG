module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersTwoTuple
public import CFSG.LocalAnalysis.EvenBN.U4.LayersGMS
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_map_subtype_iff)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem nonempty_mulEquiv_N2G (_hS : Setting h L η t Q T) :
    Nonempty (miyamotoN2G h L η ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  have : CharP K 2 := h.charP
  refine ⟨((Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm.trans
    ((Subgroup.equivMapOfInjective _ η.symm.toMonoidHom η.symm.injective).symm.trans
      ((subgroupOfEquivOfLe (miyamotoN2_le_gramSU h)).trans (miyamotoN2Equiv h).symm)))⟩

theorem isQuasisimple_sl2_fixedField (hS : Setting h L η t Q T) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  have : CharP K 2 := h.charP
  have := h.finite
  have : Finite h.fixedField := Subtype.finite
  let := Fintype.ofFinite h.fixedField
  have h4 : 4 ≤ Fintype.card h.fixedField := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField]
    exact hS.four_le
  have h2 : (2 : h.fixedField) = 0 := by
    apply Subtype.coe_injective
    change h.fixedField.subtype 2 = h.fixedField.subtype 0
    rw [map_ofNat, map_zero]
    exact CharTwo.two_eq_zero
  have := GMSK.sl2_isSimpleGroup h2 h4
  exact isQuasisimple_of_isSimpleGroup GMSK.sl2_exists_mul_ne

theorem mem_normalizer_N2_subgroupOf (hS : Setting h L η t Q T) {x : miyamotoH2G h L η t Q}
    (hx : (x : G) * t = t * x) :
    x ∈ normalizer (((miyamotoN2G h L η).subgroupOf (miyamotoH2G h L η t Q) :
      Subgroup (miyamotoH2G h L η t Q)) : Set (miyamotoH2G h L η t Q)) := by
  rw [normalizer_subgroupOf' hS.N2G_le_H2, mem_subgroupOf]
  exact hS.mem_normalizer_N2_of_mem_C_I2 (mem_centralizer_singleton_iff.2 hx) x.2.2

theorem gmsLinearLocalApplication_tupleTwo (hS : Setting h L η t Q T) :
    GMSLinearLocalApplication ((miyamotoN2G h L η).subgroupOf (miyamotoH2G h L η t Q))
      (⟨t, hS.t_mem_H2⟩ : miyamotoH2G h L η t Q)
      ((miyamotoPull h L η (miyamotoRootB h)).subgroupOf (miyamotoH2G h L η t Q))
      ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)).subgroupOf
        (miyamotoH2G h L η t Q))
      ((miyamotoIN2G h L η).subgroupOf (miyamotoH2G h L η t Q)) f := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := miyamotoH2G h L η t Q with hHdef
  set W := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) with hWdef
  set U := miyamotoPull h L η (miyamotoRootB h) with hUdef
  set tH : H := ⟨t, hS.t_mem_H2⟩ with htHdef
  have hNH : miyamotoN2G h L η ≤ H := hS.N2G_le_H2
  have hUH : U ≤ H := hS.rootB_le_N2G.trans hNH
  have hWH : W ≤ H := hS.V2_le_H2
  have hDH : miyamotoIN2G h L η ≤ H := hS.IN2G_le_N2G.trans hNH
  have hCt : centralizer ({tH} : Set H) = (centralizer ({t} : Set G)).subgroupOf H :=
    centralizer_singleton_subgroupOf hS.t_mem_H2
  have hCA : centralizer (((miyamotoN2G h L η).subgroupOf H : Subgroup H) : Set H) =
      (H ⊓ centralizer (miyamotoN2G h L η : Set G)).subgroupOf H := by
    rw [centralizer_subgroupOf hNH, inf_subgroupOf_left]
  have hzt : zpowers tH = (zpowers t).subgroupOf H := zpowers_mk_eq hS.t_mem_H2
  have htH2 : orderOf tH = 2 := by rw [htHdef, Subgroup.orderOf_mk, hS.t_two]
  have hsyl : IsSylowOf 2 (zpowers tH)
      (centralizer (((miyamotoN2G h L η).subgroupOf H : Subgroup H) : Set H)) := by
    rw [hzt, hCA]
    exact isSylowOf_subgroupOf (zpowers_le.2 hS.t_mem_H2) inf_le_left hS.isSylowOf_zpowers_H2
  have htC : tH ∈ centralizer (((miyamotoN2G h L η).subgroupOf H : Subgroup H) : Set H) := by
    rw [hCA, mem_subgroupOf]
    exact mem_inf.2 ⟨hS.t_mem_H2, hS.t_mem_centralizer_N2⟩
  have he : ∀ S : Sylow 2 H, ∃ x ∈ (S : Subgroup H), x * tH ≠ tH * x := by
    intro S
    obtain ⟨y, ⟨x, hxS, rfl⟩, hy⟩ := hS.exists_not_commute_of_isSylowOf_H2
      (S := (S : Subgroup H).map H.subtype) ⟨S, rfl⟩
    exact ⟨x, hxS, fun e => hy (by simpa using congrArg Subtype.val e)⟩
  have hnorm : centralizer ({tH} : Set H) ≤
      normalizer (((miyamotoN2G h L η).subgroupOf H : Subgroup H) : Set H) := fun x hx =>
    hS.mem_normalizer_N2_subgroupOf
      (by simpa using congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx))
  have hAC : (miyamotoN2G h L η).subgroupOf H ≤ centralizer ({tH} : Set H) := by
    rw [hCt]
    exact subgroupOf_mono _ hS.N2G_le_C
  have hr1 : ∀ r ∈ zpowers tH, r ≠ 1 → r = tH := by
    intro r hr hr1
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
    have hk2 : tH ^ k = tH ^ (k % 2) := by
      rw [← zpow_mod_orderOf, htH2]
      norm_cast
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [hk2, h0, zpow_zero] at hr1 ⊢
      exact absurd rfl hr1
    · rw [hk2, h1, zpow_one]
  obtain ⟨e⟩ := hS.nonempty_mulEquiv_N2G
  have := h.finite
  have : Finite h.fixedField := Subtype.finite
  let := Fintype.ofFinite h.fixedField
  refine ⟨hS.two_le, htH2, ⟨?_, ?_, ?_⟩, ⟨htC, ?_, hAC, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun S _ => he S⟩
  ·
    refine CFSG.ComponentClassification.AS81.Sec2Quot.standardComponentIsStandard_of_sylow
      (M := (miyamotoN2G h L η).subgroupOf H) (R := zpowers tH)
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv
        ((subgroupOfEquivOfLe hNH).trans e) hS.isQuasisimple_sl2_fixedField) hsyl
      (fun hb => by
        have := mem_zpowers tH
        rw [hb, mem_bot] at this
        rw [this, orderOf_one] at htH2
        exact absurd htH2 (by norm_num))
      (fun x r hr hr1' hxr => ?_) (fun x r hr hr1' hxr => ?_) ?_
    ·
      obtain rfl := hr1 r hr hr1'
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hxr
      have hk2 : tH ^ k = tH ^ (k % 2) := by
        rw [← zpow_mod_orderOf, htH2]
        norm_cast
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exfalso
        rw [hk2, h0, zpow_zero] at hk
        apply hr1'
        calc tH = x⁻¹ * (x * tH * x⁻¹) * x := by group
          _ = 1 := by rw [← hk]; group
      · rw [hk2, h1, zpow_one] at hk
        refine hnorm (mem_centralizer_singleton_iff.2 ?_)
        calc x * tH = x * tH * x⁻¹ * x := by group
          _ = tH * x := by rw [← hk]
    ·
      obtain rfl := hr1 r hr hr1'
      apply hS.conj_not_mem_L (x : G)⁻¹
      rw [mem_subgroupOf] at hxr
      rw [inv_inv]
      exact miyamotoPull_le h L η _ (by simpa using hxr)
    ·
      refine ⟨⟨hS.rootEltB 1, hUH (hS.rootEltB_mem 1)⟩,
        mem_subgroupOf.2 (hS.rootB_le_N2G (hS.rootEltB_mem 1)), fun e1 => ?_, ?_⟩
      · have h1 : hS.rootEltB 1 = 1 := by simpa using congrArg Subtype.val e1
        rw [← hS.rootEltB_zero] at h1
        exact one_ne_zero (hS.rootEltB_injective h1)
      · apply Subtype.ext
        simp [sq, hS.rootEltB_mul_self]
  ·
    exact not_normal_of_isSylowOf_zpowers htH2 htC hsyl he
  ·
    refine ⟨h.fixedField, inferInstance, inferInstance, ?_, ⟨(subgroupOfEquivOfLe hNH).trans e⟩⟩
    rw [← Nat.card_eq_fintype_card, h.card_fixedField]
  ·
    obtain ⟨S, hS'⟩ := hsyl.exists_sylow_eq_subgroupOf
    exact ⟨S, hS'⟩
  ·
    exact (normal_subgroupOf_iff_le_normalizer hAC).2 hnorm
  ·
    exact subgroupOf_mono _ hS.rootB_le_N2G
  ·
    exact (isSylowOf_subgroupOf hUH hNH hS.isSylowOf_rootB_N2).exists_sylow_eq_subgroupOf
  ·
    have : CFSG.IsElementaryAbelian 2 W :=
      isElementaryAbelian_two_of_forall (fun x hx y hy => hS.V2_comm hx hy)
        fun x hx => hS.F1_mul_self x (hS.V2_le_F1 hx)
    exact CFSG.IsElementaryAbelian.subgroupOf hWH
  ·
    rw [card_subgroupOf_of_le hWH, hS.card_V2]
  ·
    rw [normalizer_subgroupOf' hWH, mem_subgroupOf]
    exact hS.t_mem_normalizer_V2
  ·
    rw [inf_subgroupOf', hS.V2_inf_N2]
  ·
    rw [hCt, inf_subgroupOf', hS.V2_inf_C]
  ·
    apply map_injective H.subtype_injective
    rw [map_closure_commutator_subgroupOf hWH hS.t_mem_H2, map_subtype_subgroupOf hUH]
    exact hS.closure_commutator_V2.1
  ·
    rw [normalizer_subgroupOf' hUH, inf_subgroupOf']
    exact subgroupOf_mono _ (le_inf hS.IN2G_le_N2G hS.IN2G_le_normalizer_rootB)
  ·
    have := isCyclic_miyamotoIN2G h L η
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hDH).symm.toMonoidHom
      (subgroupOfEquivOfLe hDH).symm.surjective
  ·
    rw [card_subgroupOf_of_le hDH, card_miyamotoIN2G]
  ·
    rw [inf_subgroupOf', hS.IN2G_inf_rootB, bot_subgroupOf]
  ·
    rw [← subgroupOf_sup hUH hDH, normalizer_subgroupOf' hUH, inf_subgroupOf',
      hS.rootB_sup_IN2G]
  ·
    rw [normalizer_subgroupOf' hWH]
    exact subgroupOf_mono _ hS.IN2G_le_normalizer_V2
  ·
    rw [hCt]
    exact subgroupOf_mono _ hS.IN2G_le_C
  ·
    intro u hu hu1 w hw hw1
    have hu1' : (u : G) ≠ 1 := fun e1 => hu1 (Subtype.ext e1)
    have hw1' : (w : G) ≠ 1 := fun e1 => hw1 (Subtype.ext e1)
    refine (existsUnique_congr fun d => ?_).2 ((existsUnique_subgroupOf_iff hDH
      (fun g => g * (u : G) * g⁻¹ = w)).2 (hS.IN2G_regular_rootB _ hu hu1' _ hw hw1'))
    rw [Subtype.ext_iff]
    simp
  ·
    intro v hv hvU w hw hwU
    refine (existsUnique_congr fun d => ?_).2 ((existsUnique_subgroupOf_iff hDH
      (fun g => (g * (v : G) * g⁻¹)⁻¹ * w ∈ U)).2
        (hS.IN2G_regular_V2 _ hv (fun h1 => hvU (mem_subgroupOf.2 h1)) _ hw
          (fun h1 => hwU (mem_subgroupOf.2 h1))))
    rw [mem_subgroupOf]
    simp

theorem localFieldBound_tupleTwo (hS : Setting h L η t Q T) :
    GMS.LocalFieldBound ((miyamotoN2G h L η).subgroupOf (miyamotoH2G h L η t Q))
      (⟨t, hS.t_mem_H2⟩ : miyamotoH2G h L η t Q) f := by
  set H := miyamotoH2G h L η t Q with hHdef
  have key : centralizer ({(⟨t, hS.t_mem_H2⟩ : H)} : Set H) ≤
      (miyamotoN2G h L η).subgroupOf H ⊔
        centralizer (((miyamotoN2G h L η).subgroupOf H : Subgroup H) : Set H) := by
    intro x hx
    rw [centralizer_singleton_subgroupOf hS.t_mem_H2, mem_subgroupOf] at hx
    obtain ⟨a, ha, c, hc, hac⟩ := hS.exists_eq_mul_of_mem_H2 hx x.2
    have hcN : (⟨c, (mem_inf.1 hc).1⟩ : H) ∈
        centralizer (((miyamotoN2G h L η).subgroupOf H : Subgroup H) : Set H) := by
      rw [centralizer_subgroupOf hS.N2G_le_H2, mem_subgroupOf]
      exact (mem_inf.1 hc).2
    have e : x = ⟨a, hS.N2G_le_H2 ha⟩ * ⟨c, (mem_inf.1 hc).1⟩ := Subtype.ext hac
    rw [e]
    exact mul_mem (mem_sup_left (mem_subgroupOf.2 ha)) (mem_sup_right hcN)
  exact ⟨fun x hx => pow_mem (key hx) 2, fun _ => key⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
