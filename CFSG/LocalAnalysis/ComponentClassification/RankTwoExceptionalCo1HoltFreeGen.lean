module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeFusion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoB
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1TwoCDefs
public import CFSG.Sporadic.Co1Patterson.AmalgamIn
public import CFSG.Sporadic.Co1Patterson.AmalgamInnerMain
public import CFSG.Sporadic.Co1Patterson.AmalgamRigidEdge

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup CFSG.Sporadic.Co1Patterson
open CFSG.LargeExtraspecial.S14 (PattersonCo1Hyp)

theorem card_centralizer_apply {U V : Type*} [Group U] [Group V] (e : U ≃* V) (a : U) :
    Nat.card (centralizer ({e a} : Set V)) = Nat.card (centralizer ({a} : Set U)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)).symm
  simp only [mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem card_centralizer_subtype {X : Type*} [Group X] (Y : Subgroup X) (y : Y) :
    Nat.card (centralizer ({y} : Set Y)) = Nat.card ↥(Y ⊓ centralizer ({(y : X)} : Set X)) := by
  rw [← CFSG.Sporadic.Co1Patterson.map_centralizer_subtype,
    card_map_of_injective Y.subtype_injective]

theorem center_eq_bot_of_mulEquiv {Y : Type*} [Group Y]
    (e : Y ≃* Blueprint.NativeSporadic.Co1) : center Y = ⊥ := by
  have : IsSimpleGroup Blueprint.NativeSporadic.Co1 := CFSG.Sporadic.Co1.isSimpleGroup_Co1
  have hZ : center Blueprint.NativeSporadic.Co1 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Blueprint.NativeSporadic.Co1)
      with h0 | h0
    · exact h0
    · exfalso
      have : IsMulCommutative Blueprint.NativeSporadic.Co1 := ⟨⟨fun a b => by
        have hb : b ∈ center Blueprint.NativeSporadic.Co1 := h0 ▸ mem_top b
        exact mem_center_iff.mp hb a⟩⟩
      have hp := Group.is_simple_iff_prime_card.mp ‹IsSimpleGroup Blueprint.NativeSporadic.Co1›
      rw [CFSG.Sporadic.Co1.card_Co1] at hp
      norm_num at hp
  rw [eq_bot_iff]
  intro y hy
  have h1 : e y ∈ center Blueprint.NativeSporadic.Co1 := mem_center_iff.mpr fun g => by
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hy g]
  rw [hZ, mem_bot] at h1
  exact mem_bot.mpr (e.injective (h1.trans (map_one e).symm))

section Generation

variable {X : Type} [Group X] [Finite X] {t : X}

theorem mem_of_conj_mem (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* Blueprint.NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y) {g : X}
    (hg : g * t * g⁻¹ ∈ Y) : g ∈ Y := by
  have htY : t ∈ Y := hCY (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_isConj_of_mem h e htY (y := ⟨_, hg⟩)
    (isConj_iff.mpr ⟨g, rfl⟩))
  have hc' : (c : X) * t * (c : X)⁻¹ = g * t * g⁻¹ := congrArg Subtype.val hc
  have hk : g⁻¹ * c ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * c * t = g⁻¹ * ((c : X) * t * (c : X)⁻¹) * c := by group
      _ = t * (g⁻¹ * c) := by rw [hc']; group
  have := Y.mul_mem (hCY hk) (Y.inv_mem c.2)
  rwa [mul_inv_cancel_right, Y.inv_mem_iff] at this

theorem normalizer_le (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* Blueprint.NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y) :
    normalizer (Y : Set X) ≤ Y := fun _ hn =>
  mem_of_conj_mem h e hCY
    ((mem_normalizer_iff.mp hn t).mp (hCY (mem_centralizer_singleton_iff.mpr rfl)))

theorem exists_co1TwoCSetting (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* Blueprint.NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y) :
    ∃ ψ : normalizer (Y : Set X) →* Blueprint.NativeSporadic.Co1, Co1TwoCSetting Y ψ t ∧
      Odd (Nat.card (center Y)) ∧
      ∀ (u : X) (hu : u ∈ Y), ψ ⟨u, le_normalizer hu⟩ = e ⟨u, hu⟩ := by
  have htY : t ∈ Y := hCY (mem_centralizer_singleton_iff.mpr rfl)
  have hN := normalizer_le h e hCY
  have hZ := center_eq_bot_of_mulEquiv e
  have hC : centralizer (Y : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hcY : c ∈ Y :=
      hCY (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc t htY).symm)
    have hcZ : (⟨c, hcY⟩ : Y) ∈ center Y :=
      mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hc y y.2)
    rw [hZ, mem_bot] at hcZ
    exact mem_bot.mpr (congrArg Subtype.val hcZ)
  have hct : Nat.card (centralizer ({e ⟨t, htY⟩} : Set Blueprint.NativeSporadic.Co1)) =
      89181388800 := by
    rw [card_centralizer_apply, card_centralizer_subtype, inf_of_le_right hCY,
      card_centralizer h]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : normalizer (Y : Set X) →* Blueprint.NativeSporadic.Co1,
      ∀ (u : X) (hu : u ∈ normalizer (Y : Set X)), ψ ⟨u, hu⟩ = e ⟨u, hN hu⟩ := by
    refine ⟨MonoidHom.mk' (fun n => e (Subgroup.inclusion hN n)) fun a b => ?_, fun u hu => ?_⟩
    · rw [map_mul, map_mul]
    · rw [MonoidHom.mk'_apply]
      exact congrArg e (Subtype.ext rfl)
  have hψt : ψ ⟨t, le_normalizer htY⟩ = e ⟨t, htY⟩ := hψ _ _
  refine ⟨ψ, ⟨⟨fun _ _ => mem_top _, fun x _ => ⟨_, (e.symm x).2, ?_⟩, fun n => ?_⟩, ?_, htY,
    h.orderOf_eq, ?_, fun g hg => le_normalizer (mem_of_conj_mem h e hCY hg)⟩, ?_,
    fun u hu => hψ u (le_normalizer hu)⟩
  · rw [hψ, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  · obtain ⟨n, hn⟩ := n
    rw [hψ n hn]
    constructor
    · intro h1
      have h3 : n = 1 := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
      show n ∈ _
      rw [h3]
      exact one_mem _
    · intro hc
      have hcZ : (⟨n, hN hn⟩ : Y) ∈ center Y :=
        mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hc y y.2)
      rw [hZ, mem_bot] at hcZ
      rw [hcZ, map_one]
  · rw [hC, card_bot]
    exact odd_one
  · rw [hψt]
    have hidx := (centralizer ({e ⟨t, htY⟩} : Set Blueprint.NativeSporadic.Co1)).index_mul_card
    rw [hct, CFSG.Sporadic.Co1.card_Co1] at hidx
    rw [show (centralizer ({e ⟨t, htY⟩} : Set Blueprint.NativeSporadic.Co1)).index = 46621575 by
      omega]
    norm_num
  · rw [hZ, card_bot]
    exact odd_one

theorem centralizer_le (h2C : Co1TwoCControl) (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* Blueprint.NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y)
    (h2B : ∀ r ∈ Y, orderOf r = 2 → Nat.card ↥(Y ⊓ centralizer ({r} : Set X)) = 2012774400 →
      centralizer ({r} : Set X) ≤ Y) {u : X} (hu : u ∈ Y) (hu2 : orderOf u = 2) :
    centralizer ({u} : Set X) ≤ Y := by
  have htY : t ∈ Y := hCY (mem_centralizer_singleton_iff.mpr rfl)
  have hN := normalizer_le h e hCY
  obtain ⟨ψ, hS, hZ, hψ⟩ := exists_co1TwoCSetting h e hCY
  obtain ⟨a, b, c, hcls, -, -, -, -, -, -, -, hCb, hCc⟩ := exists_involution_classes e
  have h2 : ∀ {v : X} (hv : v ∈ Y), orderOf v = 2 → orderOf (⟨v, hv⟩ : Y) = 2 :=
    fun hv hv2 => (Subgroup.orderOf_mk _ hv).trans hv2
  have hct : Nat.card (centralizer ({(⟨t, htY⟩ : Y)} : Set Y)) = 89181388800 := by
    rw [card_centralizer_subtype, inf_of_le_right hCY, card_centralizer h]
  rcases hcls ⟨u, hu⟩ (h2 hu hu2) with hr | hr | hr
  · have hta : IsConj a ⟨t, htY⟩ := by
      rcases hcls ⟨t, htY⟩ (h2 htY h.orderOf_eq) with ht | ht | ht
      · exact ht
      · have := Subgroup.card_centralizer_of_isConj ht
        rw [hCb, hct] at this
        norm_num at this
      · have := Subgroup.card_centralizer_of_isConj ht
        rw [hCc, hct] at this
        norm_num at this
    obtain ⟨y, hy⟩ := isConj_iff.mp (hta.symm.trans hr)
    have hyu : (y : X) * t * (y : X)⁻¹ = u := congrArg Subtype.val hy
    have hle := hS.centralizer_conj_le (g := y) (by rw [hyu]; exact hu)
    rw [hyu] at hle
    exact hle.trans hN
  · refine h2B u hu hu2 ?_
    rw [← card_centralizer_subtype Y ⟨u, hu⟩, ← Subgroup.card_centralizer_of_isConj hr, hCb]
  · refine (h2C X Y ψ hS.act hZ hS.oddCent t htY h.orderOf_eq hS.central hS.unique u hu hu2
      ?_).trans hN
    rw [hψ u hu, card_centralizer_apply, ← Subgroup.card_centralizer_of_isConj hr, hCc]

theorem eq_top_of_co1_le_holtFree (h2C : Co1TwoCControl) (h : PattersonCo1Hyp X t)
    {Y : Subgroup X} (e : Y ≃* Blueprint.NativeSporadic.Co1)
    (hCY : centralizer ({t} : Set X) ≤ Y)
    (h2B : ∀ r ∈ Y, orderOf r = 2 → Nat.card ↥(Y ⊓ centralizer ({r} : Set X)) = 2012774400 →
      centralizer ({r} : Set X) ≤ Y) :
    Y = ⊤ := by
  by_contra hY
  have htY : t ∈ Y := hCY (mem_centralizer_singleton_iff.mpr rfl)
  have hN := normalizer_le h e hCY
  obtain ⟨ψ, hS, -, -⟩ := exists_co1TwoCSetting h e hCY
  refine not_isStronglyEmbedded_of_mem h e htY Y (AS81.HeSE.isStronglyEmbedded_of_fusion Y hY
    ?_ ?_ fun u hu hu2 => centralizer_le h2C h e hCY h2B hu hu2)
  · rw [card_eq_of_mulEquiv_co1 e]
    exact even_iff_two_dvd.mpr (by norm_num)
  · intro u hu hu2 g hg
    have hP : IsPGroup 2 (zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
    have hPg : (zpowers u).map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ Y := by
      rw [MonoidHom.map_zpowers, zpowers_le, inv_inv, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      exact hg
    obtain ⟨c, hcN, hc⟩ := hS.exists_realize (zpowers_le.mpr hu) hP hPg
    refine ⟨c⁻¹, Y.inv_mem (hN hcN), ?_⟩
    rw [inv_inv, hc u (mem_zpowers u), inv_inv]

theorem co1_of_notWeaklyClosed_holtFree
    (h2C : Co1TwoCControl) (h : PattersonCo1Hyp X t) (hw : NotWeaklyClosed h)
    (hB : Co1TwoBData X t) : Nonempty (X ≃* Blueprint.NativeSporadic.Co1) := by
  obtain ⟨Φ, hinj, hle⟩ :=
    exists_hom_of_rigid h hw InnerNative.autInnerModAt_native autRigidAt_native
  have htop := eq_top_of_co1_le_holtFree h2C h (MonoidHom.ofInjective hinj).symm hle
    (twoB_centralizer_le h (MonoidHom.ofInjective hinj).symm hle hB)
  exact ⟨(MulEquiv.ofBijective Φ ⟨hinj, MonoidHom.range_eq_top.1 htop⟩).symm⟩

end Generation

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
