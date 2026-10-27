module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersTuple
public import CFSG.LocalAnalysis.EvenBN.GMS.StrongClosure
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_map_subtype_iff)

section SubgroupOf

variable {G : Type*} [Group G] {H A B : Subgroup G}

theorem centralizer_subgroupOf (hA : A ≤ H) :
    centralizer (A.subgroupOf H : Set H) = (centralizer (A : Set G)).subgroupOf H := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx a ha
    exact congrArg Subtype.val (hx ⟨a, hA ha⟩ (mem_subgroupOf.2 ha))
  · intro hx a ha
    exact Subtype.ext (hx a (mem_subgroupOf.1 ha))

theorem centralizer_singleton_subgroupOf {t : G} (ht : t ∈ H) :
    centralizer ({⟨t, ht⟩} : Set H) = (centralizer ({t} : Set G)).subgroupOf H := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    Subtype.ext_iff]
  rfl

theorem normalizer_subgroupOf' (hA : A ≤ H) :
    normalizer (A.subgroupOf H : Set H) = (normalizer (A : Set G)).subgroupOf H :=
  (subgroupOf_normalizer_eq hA).symm

theorem inf_subgroupOf' : A.subgroupOf H ⊓ B.subgroupOf H = (A ⊓ B).subgroupOf H :=
  (comap_inf _ _ _).symm

theorem map_subtype_subgroupOf (hA : A ≤ H) : (A.subgroupOf H).map H.subtype = A := by
  rw [subgroupOf_map_subtype, inf_eq_left.2 hA]

theorem card_subgroupOf_of_le (hA : A ≤ H) : Nat.card (A.subgroupOf H) = Nat.card A :=
  Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv

theorem zpowers_mk_eq {t : G} (ht : t ∈ H) :
    zpowers (⟨t, ht⟩ : H) = (zpowers t).subgroupOf H := by
  ext x
  rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem isSylowOf_subgroupOf [Finite G] {p : ℕ} [Fact p.Prime] (hA : A ≤ H) (hB : B ≤ H)
    (h : IsSylowOf p A B) : IsSylowOf p (A.subgroupOf H) (B.subgroupOf H) :=
  (isSylowOf_map_subtype_iff H).1 (by rwa [map_subtype_subgroupOf hA, map_subtype_subgroupOf hB])

theorem existsUnique_subgroupOf_iff {D : Subgroup G} (hD : D ≤ H) (P : G → Prop) :
    (∃! d : D.subgroupOf H, P ((d : H) : G)) ↔ ∃! d : D, P d := by
  constructor
  · rintro ⟨d, hd, huniq⟩
    refine ⟨⟨(d : H), d.2⟩, hd, fun d' hd' => ?_⟩
    have := huniq ⟨⟨d', hD d'.2⟩, d'.2⟩ hd'
    exact Subtype.ext (congrArg (fun x : D.subgroupOf H => ((x : H) : G)) this)
  · rintro ⟨d, hd, huniq⟩
    refine ⟨⟨⟨d, hD d.2⟩, d.2⟩, hd, fun d' hd' => ?_⟩
    have h2 : ((d' : H) : G) = d := congrArg Subtype.val (huniq ⟨(d' : H), d'.2⟩ hd')
    apply Subtype.ext
    apply Subtype.ext
    exact h2

theorem map_closure_commutator_subgroupOf {V : Subgroup G} (hV : V ≤ H) {t : G} (ht : t ∈ H) :
    (closure {x : H | ∃ v ∈ V.subgroupOf H,
      x = v⁻¹ * ((⟨t, ht⟩ : H)⁻¹ * v * ⟨t, ht⟩)}).map H.subtype =
        closure {x : G | ∃ v ∈ V, x = v⁻¹ * (t⁻¹ * v * t)} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, mem_subgroupOf, coe_subtype]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hV hv⟩⁻¹ * ((⟨t, ht⟩ : H)⁻¹ * ⟨v, hV hv⟩ * ⟨t, ht⟩), ⟨⟨v, hV hv⟩, hv, rfl⟩,
      by simp⟩

end SubgroupOf

theorem isQuasisimple_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  refine ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top X hnab, ?_⟩
  exact ((QuotientGroup.congr (center X) ⊥ (MulEquiv.refl X) (by
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot X hnab]
    exact map_bot _)).trans (QuotientGroup.quotientBot (G := X))).isSimpleGroup

theorem not_normal_of_isSylowOf_zpowers {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    {t : X} (ht2 : orderOf t = 2) (ht : t ∈ centralizer (A : Set X))
    (hsyl : IsSylowOf 2 (zpowers t) (centralizer (A : Set X)))
    (he : ∀ T : Sylow 2 X, ∃ x ∈ (T : Subgroup X), x * t ≠ t * x) : ¬ A.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hA
  obtain ⟨T, hT⟩ := hsyl.isPGroup.exists_le_sylow
  obtain ⟨x, hxT, hx⟩ := he T
  have h1 : (T : Subgroup X) ⊓ centralizer (A : Set X) = zpowers t :=
    hsyl.eq_of_le (le_inf hT hsyl.le) inf_le_right T.isPGroup'.to_inf_left
  have h2 : x * t * x⁻¹ ∈ (T : Subgroup X) ⊓ centralizer (A : Set X) :=
    mem_inf.2 ⟨mul_mem (mul_mem hxT (hT (mem_zpowers t))) (inv_mem hxT),
      (inferInstance : (centralizer (A : Set X)).Normal).conj_mem t ht x⟩
  rw [h1] at h2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
  have hk2 : t ^ k = t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, ht2]
    norm_cast
  apply hx
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    rw [hk2, h0, zpow_zero] at hk
    have : t = 1 := by
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = 1 := by rw [← hk]; group
    rw [this, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  · rw [hk2, h1, zpow_one] at hk
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [← hk]

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem nonempty_mulEquiv_N1G (_hS : Setting h L η t Q T) :
    Nonempty (miyamotoN1G h L η ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : CharP K 2 := h.charP
  refine ⟨((Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm.trans
    ((Subgroup.equivMapOfInjective _ η.symm.toMonoidHom η.symm.injective).symm.trans
      ((subgroupOfEquivOfLe (miyamotoN1_le_gramSU h)).trans (miyamotoN1Equiv h).symm)))⟩

theorem isQuasisimple_sl2 (hS : Setting h L η t Q T) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : CharP K 2 := h.charP
  have := h.finite
  let := Fintype.ofFinite K
  have h4 : 4 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, h.card_eq_sq]
    have := hS.four_le
    nlinarith
  have := GMSK.sl2_isSimpleGroup (CharTwo.two_eq_zero (R := K)) h4
  exact isQuasisimple_of_isSimpleGroup GMSK.sl2_exists_mul_ne

theorem mem_normalizer_N1_subgroupOf (hS : Setting h L η t Q T) {x : miyamotoH1G h L η t}
    (hx : (x : G) * t = t * x) :
    x ∈ normalizer (((miyamotoN1G h L η).subgroupOf (miyamotoH1G h L η t) :
      Subgroup (miyamotoH1G h L η t)) : Set (miyamotoH1G h L η t)) := by
  rw [normalizer_subgroupOf' hS.N1G_le_H1, mem_subgroupOf]
  exact hS.mem_normalizer_N1_of_mem_H1 (mem_centralizer_singleton_iff.2 hx) x.2

theorem gmsLinearLocalApplication_tupleOne (hS : Setting h L η t Q T) :
    GMSLinearLocalApplication ((miyamotoN1G h L η).subgroupOf (miyamotoH1G h L η t))
      (⟨t, hS.t_mem_H1⟩ : miyamotoH1G h L η t)
      ((miyamotoPull h L η (miyamotoRootA h)).subgroupOf (miyamotoH1G h L η t))
      ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)).subgroupOf
        (miyamotoH1G h L η t))
      ((miyamotoDG h L η).subgroupOf (miyamotoH1G h L η t)) (2 * f) := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := miyamotoH1G h L η t with hHdef
  set W := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) with hWdef
  set U := miyamotoPull h L η (miyamotoRootA h) with hUdef
  set tH : H := ⟨t, hS.t_mem_H1⟩ with htHdef
  have hNH : miyamotoN1G h L η ≤ H := hS.N1G_le_H1
  have hUH : U ≤ H := hS.rootA_le_N1G.trans hNH
  have hWH : W ≤ H := hS.W_le_H1
  have hDH : miyamotoDG h L η ≤ H := hS.DG_le_N1G.trans hNH
  have hCt : centralizer ({tH} : Set H) = (centralizer ({t} : Set G)).subgroupOf H :=
    centralizer_singleton_subgroupOf hS.t_mem_H1
  have hCA : centralizer (((miyamotoN1G h L η).subgroupOf H : Subgroup H) : Set H) =
      (H ⊓ centralizer (miyamotoN1G h L η : Set G)).subgroupOf H := by
    rw [centralizer_subgroupOf hNH, inf_subgroupOf_left]
  have hzt : zpowers tH = (zpowers t).subgroupOf H := zpowers_mk_eq hS.t_mem_H1
  have htH2 : orderOf tH = 2 := by rw [htHdef, Subgroup.orderOf_mk, hS.t_two]
  have hsyl : IsSylowOf 2 (zpowers tH)
      (centralizer (((miyamotoN1G h L η).subgroupOf H : Subgroup H) : Set H)) := by
    rw [hzt, hCA]
    exact isSylowOf_subgroupOf (zpowers_le.2 hS.t_mem_H1) inf_le_left hS.isSylowOf_zpowers_H1
  have htC : tH ∈ centralizer (((miyamotoN1G h L η).subgroupOf H : Subgroup H) : Set H) := by
    rw [hCA, mem_subgroupOf]
    exact mem_inf.2 ⟨hS.t_mem_H1, hS.t_mem_centralizer_N1⟩
  have he : ∀ S : Sylow 2 H, ∃ x ∈ (S : Subgroup H), x * tH ≠ tH * x := by
    intro S
    obtain ⟨y, ⟨x, hxS, rfl⟩, hy⟩ := hS.exists_not_commute_of_isSylowOf
      (S := (S : Subgroup H).map H.subtype) ⟨S, rfl⟩
    exact ⟨x, hxS, fun e => hy (by simpa using congrArg Subtype.val e)⟩
  have hnorm : centralizer ({tH} : Set H) ≤
      normalizer (((miyamotoN1G h L η).subgroupOf H : Subgroup H) : Set H) := fun x hx =>
    hS.mem_normalizer_N1_subgroupOf
      (by simpa using congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx))
  have hAC : (miyamotoN1G h L η).subgroupOf H ≤ centralizer ({tH} : Set H) := by
    rw [hCt]
    exact subgroupOf_mono _ hS.N1G_le_C
  obtain ⟨e⟩ := hS.nonempty_mulEquiv_N1G
  have := h.finite
  let := Fintype.ofFinite K
  refine ⟨by have := hS.two_le; omega, htH2, ⟨?_, ?_, ?_⟩, ⟨htC, ?_, hAC, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun S _ => he S⟩
  ·
    have hstd := CFSG.ComponentClassification.AS81.Sec2Quot.standardComponentIsStandard_of_sylow
      (M := (miyamotoN1G h L η).subgroupOf H) (R := zpowers tH)
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv
        ((subgroupOfEquivOfLe hNH).trans e) hS.isQuasisimple_sl2) hsyl
      (fun hb => by
        have := mem_zpowers tH
        rw [hb, mem_bot] at this
        rw [this, orderOf_one] at htH2
        exact absurd htH2 (by norm_num))
      (fun x r hr hr1 hxr => ?_) (fun x r hr hr1 hxr => ?_) ?_
    · exact hstd
    ·
      have hr' : r = tH := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
        have hk2 : tH ^ k = tH ^ (k % 2) := by
          rw [← zpow_mod_orderOf, htH2]
          norm_cast
        rcases Int.emod_two_eq_zero_or_one k with h0 | h1
        · rw [hk2, h0, zpow_zero] at hr1 ⊢
          exact absurd rfl hr1
        · rw [hk2, h1, zpow_one]
      subst hr'
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hxr
      have hk2 : tH ^ k = tH ^ (k % 2) := by
        rw [← zpow_mod_orderOf, htH2]
        norm_cast
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exfalso
        rw [hk2, h0, zpow_zero] at hk
        apply hr1
        calc tH = x⁻¹ * (x * tH * x⁻¹) * x := by group
          _ = 1 := by rw [← hk]; group
      · rw [hk2, h1, zpow_one] at hk
        refine hnorm (mem_centralizer_singleton_iff.2 ?_)
        calc x * tH = x * tH * x⁻¹ * x := by group
          _ = tH * x := by rw [← hk]
    ·
      have hr' : r = tH := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
        have hk2 : tH ^ k = tH ^ (k % 2) := by
          rw [← zpow_mod_orderOf, htH2]
          norm_cast
        rcases Int.emod_two_eq_zero_or_one k with h0 | h1
        · rw [hk2, h0, zpow_zero] at hr1 ⊢
          exact absurd rfl hr1
        · rw [hk2, h1, zpow_one]
      subst hr'
      apply hS.conj_not_mem_L (x : G)⁻¹
      rw [mem_subgroupOf] at hxr
      rw [inv_inv]
      exact miyamotoPull_le h L η _ (by simpa using hxr)
    ·
      refine ⟨⟨hS.rootElt 1, hUH (hS.rootElt_mem_rootA 1)⟩,
        mem_subgroupOf.2 (hS.rootA_le_N1G (hS.rootElt_mem_rootA 1)), fun e1 => ?_, ?_⟩
      · have h1 : hS.rootElt 1 = 1 := by simpa using congrArg Subtype.val e1
        have h2 := (hS.rootElt_mem_F1_iff (a := 1)).1 (by rw [h1]; exact one_mem _)
        exact one_ne_zero h2
      · apply Subtype.ext
        simp [sq, hS.rootElt_mul_self]
  ·
    exact not_normal_of_isSylowOf_zpowers htH2 htC hsyl he
  ·
    refine ⟨K, inferInstance, inferInstance, ?_, ⟨(subgroupOfEquivOfLe hNH).trans e⟩⟩
    rw [← Nat.card_eq_fintype_card, h.card_eq_sq, ← pow_mul, mul_comm]
  ·
    obtain ⟨S, hS'⟩ := hsyl.exists_sylow_eq_subgroupOf
    exact ⟨S, hS'⟩
  ·
    exact (normal_subgroupOf_iff_le_normalizer hAC).2 hnorm
  ·
    exact subgroupOf_mono _ hS.rootA_le_N1G
  ·
    exact (isSylowOf_subgroupOf hUH hNH hS.isSylowOf_rootA_N1).exists_sylow_eq_subgroupOf
  ·
    have : CFSG.IsElementaryAbelian 2 W :=
      isElementaryAbelian_two_of_forall (fun x hx y hy => hS.W_comm hx hy)
        fun x hx => hS.W_mul_self hx
    exact CFSG.IsElementaryAbelian.subgroupOf hWH
  ·
    rw [card_subgroupOf_of_le hWH, hS.card_W]
    ring
  ·
    rw [normalizer_subgroupOf' hWH, mem_subgroupOf]
    exact hS.t_mem_normalizer_W
  ·
    rw [inf_subgroupOf', hS.W_inf_N1]
  ·
    rw [hCt, inf_subgroupOf', hS.W_inf_C]
  ·
    apply map_injective H.subtype_injective
    rw [map_closure_commutator_subgroupOf hWH hS.t_mem_H1, map_subtype_subgroupOf hUH]
    exact hS.closure_commutator_W
  ·
    rw [normalizer_subgroupOf' hUH, inf_subgroupOf']
    exact subgroupOf_mono _ (le_inf hS.DG_le_N1G hS.DG_le_normalizer_rootA)
  ·
    have := isCyclic_miyamotoDG h L η
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hDH).symm.toMonoidHom
      (subgroupOfEquivOfLe hDH).symm.surjective
  ·
    rw [card_subgroupOf_of_le hDH, card_miyamotoDG, ← pow_mul, mul_comm]
  ·
    rw [inf_subgroupOf', hS.DG_inf_rootA, bot_subgroupOf]
  ·
    rw [← subgroupOf_sup hUH hDH, normalizer_subgroupOf' hUH, inf_subgroupOf', hS.rootA_sup_DG]
  ·
    rw [normalizer_subgroupOf' hWH]
    exact subgroupOf_mono _ hS.DG_le_normalizer_W
  ·
    rw [hCt]
    exact subgroupOf_mono _ hS.DG_le_C
  ·
    intro u hu hu1 w hw hw1
    have hu1' : (u : G) ≠ 1 := fun e1 => hu1 (Subtype.ext e1)
    have hw1' : (w : G) ≠ 1 := fun e1 => hw1 (Subtype.ext e1)
    refine (existsUnique_congr fun d => ?_).2 ((existsUnique_subgroupOf_iff hDH
      (fun g => g * (u : G) * g⁻¹ = w)).2 (hS.DG_regular_rootA _ hu hu1' _ hw hw1'))
    rw [Subtype.ext_iff]
    simp
  ·
    intro v hv hvU w hw hwU
    refine (existsUnique_congr fun d => ?_).2 ((existsUnique_subgroupOf_iff hDH
      (fun g => (g * (v : G) * g⁻¹)⁻¹ * w ∈ U)).2
        (hS.DG_regular_W _ hv (fun h1 => hvU (mem_subgroupOf.2 h1)) _ hw
          (fun h1 => hwU (mem_subgroupOf.2 h1))))
    rw [mem_subgroupOf]
    simp

theorem localFieldBound_tupleOne (hS : Setting h L η t Q T) :
    GMS.LocalFieldBound ((miyamotoN1G h L η).subgroupOf (miyamotoH1G h L η t))
      (⟨t, hS.t_mem_H1⟩ : miyamotoH1G h L η t) (2 * f) := by
  set H := miyamotoH1G h L η t with hHdef
  refine ⟨fun x hx => ?_, fun hf => absurd hf (by have := hS.two_le; omega)⟩
  rw [centralizer_singleton_subgroupOf hS.t_mem_H1, mem_subgroupOf] at hx
  obtain ⟨a, ha, c, hc, hac⟩ := hS.exists_sq_eq_mul_of_mem_H1 hx x.2
  have hcN : (⟨c, (mem_inf.1 hc).1⟩ : H) ∈
      centralizer (((miyamotoN1G h L η).subgroupOf H : Subgroup H) : Set H) := by
    rw [centralizer_subgroupOf hS.N1G_le_H1, mem_subgroupOf]
    exact (mem_inf.1 hc).2
  have e : x ^ 2 = ⟨a, hS.N1G_le_H1 ha⟩ * ⟨c, (mem_inf.1 hc).1⟩ := Subtype.ext (by simpa using hac)
  rw [e]
  exact mul_mem (mem_sup_left (mem_subgroupOf.2 ha)) (mem_sup_right hcN)

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
