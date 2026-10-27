module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCKind
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWA
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem catalog_center_quotient_of_kProper_of_surjective_nOne {G : Type} [Group G]
    (hKP : CFSG.Assembly.KProper Catalog G) {H : Subgroup G} (hH : H ≠ ⊤) {Q : Type} [Group Q]
    (f : H →* Q) (hf : Function.Surjective f) {Kc : Subgroup Q} (hKc : IsQuasisimple Kc) :
    Catalog (Kc ⧸ center Kc) := by
  have : IsSimpleGroup (Kc ⧸ center Kc) := hKc.2.1
  set M : Subgroup G := (Kc.comap f).map H.subtype with hM
  have hMH : M ≤ H := map_subtype_le _
  have hMtop : M ≠ ⊤ := fun h => hH (top_unique (h ▸ hMH))
  have hmem : ∀ m : M, (f.comp (Subgroup.inclusion hMH)) m ∈ Kc := by
    rintro ⟨_, h, hh, rfl⟩
    exact hh
  let ψ : M →* Kc := (f.comp (Subgroup.inclusion hMH)).codRestrict Kc hmem
  let φ : M →* Kc ⧸ center Kc := (QuotientGroup.mk' (center Kc)).comp ψ
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center Kc) z
    obtain ⟨h, hh⟩ := hf (k : Q)
    have hhK : h ∈ Kc.comap f := by
      rw [mem_comap, hh]
      exact k.2
    refine ⟨⟨(h : G), h, hhK, rfl⟩, ?_⟩
    change QuotientGroup.mk' (center Kc) (ψ _) = QuotientGroup.mk' (center Kc) k
    congr 1
    exact Subtype.ext hh
  exact EvenSmallLie.CatalogOrders.catalog_of_kProper_of_surjective hKP M hMtop _ hKc.2.2 φ hφ

@[expose] def LFiveNormalizerPointRadicalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ c : Fin 5, normalizer (modelToG e (pointRadical (K := K) c) : Set G) ⊓
        centralizer ({t} : Set G) ≤
      modelToG e (pointRadical (K := K) c) ⊔ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ⊔
        zpowers t

section Levi

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
  (e : L ≃* LinearFlag.projectiveSL 5 K)

theorem card_specialLinearGroup_four_of_card_two (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) = 20160 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  classical
  rw [Matrix.card_SL_field, hq]
  decide

theorem nonempty_modelToG_blockSL_compl_mulEquiv (c : Fin 5) :
    Nonempty (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≃*
      Matrix.SpecialLinearGroup (Fin 4) K) := by
  have h4 : (({c}ᶜ : Finset (Fin 5))).card = 4 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  obtain ⟨eB⟩ := blockSL_mulEquiv (K := K) (I := ({c}ᶜ : Finset (Fin 5))) (by rw [h4]; norm_num)
  exact ⟨(linearModelToGEquiv e _).symm.trans (eB.trans (reindexSpecialLinear (finCongr h4)))⟩

theorem modelToG_blockSL_compl_facts (hK : Nat.card K = 2) (c : Fin 5) :
    IsSimpleGroup (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))) ∧
      center (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))) = ⊥ ∧
      LieModel (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ⧸
        center (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))))) .PSL 4 2 1 ∧
      Nat.card (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))) = 20160 ∧
      CFSG.Open.IsQuasisimple (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))) := by
  obtain ⟨φ⟩ := nonempty_modelToG_blockSL_compl_mulEquiv e c
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have hSL : center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (mem_bot).2 (eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz)
  have hZ := F4Pilot.center_eq_bot_congr φ.symm hSL
  have hLm := lieModel_quotient_center_of_mulEquiv_specialLinear hK1 (by norm_num) φ
  have hL : LieModel (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))) .PSL 4 2 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hLm
  have hsimp := isSimpleGroup_of_lieModel_PSL hL
  have hcard : Nat.card (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))) = 20160 := by
    rw [Nat.card_congr φ.toEquiv, card_specialLinearGroup_four_of_card_two hK]
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hcardc : (({c}ᶜ : Finset (Fin 5))).card = 4 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  exact ⟨hsimp, hZ, hLm, hcard, isQuasisimple_open_map_blockSL e (by rw [hcardc]; norm_num)
    (by rw [hcardc]; norm_num) (Or.inl (by rw [hcardc]; norm_num))⟩

end Levi

section Bar

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
  (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} {c : Fin 5} {W₁ : Subgroup G}

theorem card_wOne_inf_centralizer (hK : Nat.card K = 2)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c)) :
    Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4 := by
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
    Finset.card_singleton, Fintype.card_fin]

theorem not_mem_wOne (hK : Nat.card K = 2) (hW₁c : Nat.card W₁ = 2 ^ 8)
    (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c)) : t ∉ W₁ := by
  intro htW
  have hle : W₁ ≤ centralizer ({t} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.2 (mul_comm_of_forall_mul_self_eq_one hW₁2 hw htW)
  have h := card_wOne_inf_centralizer e hK hW₁t
  rw [inf_eq_left.2 hle, hW₁c] at h
  norm_num at h

theorem orderOf_mk_wOne_eq_two (hK : Nat.card K = 2) (ht : orderOf t = 2)
    (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G)) :
    orderOf (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htW₁⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have h1 : (⟨t, htW₁⟩ : normalizer (W₁ : Set G)) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [h1, map_one]
  · intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact not_mem_wOne e hK hW₁c hW₁2 hW₁t h1

theorem inf_eq_bot_of_wOne (hK : Nat.card K = 2) (hW₁c : Nat.card W₁ = 2 ^ 8)
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G)) :
    modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ⊓ W₁ = ⊥ := by
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  obtain ⟨hsimp, -, -, hcard, -⟩ := modelToG_blockSL_compl_facts e hK c
  have hn : ((L₁ ⊓ W₁).subgroupOf L₁).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hxL, hxW⟩ := Subgroup.mem_inf.1 hx
    simp only [coe_mul, coe_inv]
    exact Subgroup.mem_inf.2 ⟨L₁.mul_mem (L₁.mul_mem g.2 hxL) (L₁.inv_mem g.2),
      (mem_normalizer_iff.1 (hLW g.2) x).1 hxW⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L₁ ⊓ W₁).subgroupOf L₁) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, (Subgroup.mem_inf.1 hx).1⟩ : L₁) ∈ (L₁ ⊓ W₁).subgroupOf L₁ :=
      mem_subgroupOf.2 hx
    rw [h] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hx'))
  · exfalso
    have hle : L₁ ≤ W₁ := fun x hx => by
      have hx' : (⟨x, hx⟩ : L₁) ∈ (L₁ ⊓ W₁).subgroupOf L₁ := h ▸ mem_top _
      exact (Subgroup.mem_inf.1 (mem_subgroupOf.1 hx')).2
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard, hW₁c] at hdvd
    norm_num at hdvd

theorem leviBar_facts (hK : Nat.card K = 2) (htC : t ∈ centralizer (L : Set G))
    (hW₁c : Nat.card W₁ = 2 ^ 8)
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    (htW₁ : t ∈ normalizer (W₁ : Set G)) :
    CFSG.Open.IsQuasisimple (((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
        (normalizer (W₁ : Set G))).map
        (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))) ∧
      center (((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
        (normalizer (W₁ : Set G))).map
        (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))) = ⊥ ∧
      LieModel ((((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
          (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))) ⧸
        center (((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
          (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G)))))) .PSL 4 2 1 ∧
      Nat.card (((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
        (normalizer (W₁ : Set G))).map
        (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))) = 20160 ∧
      ((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
        (normalizer (W₁ : Set G))).map
        (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G)))) ≤
        centralizer ({QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htW₁⟩} :
          Set (normalizer (W₁ : Set G) ⧸ W₁.subgroupOf (normalizer (W₁ : Set G)))) := by
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  have hinf := inf_eq_bot_of_wOne e hK hW₁c hLW
  have hinf' : L₁.subgroupOf (normalizer (W₁ : Set G)) ⊓
      W₁.subgroupOf (normalizer (W₁ : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have hx' : (x : G) ∈ L₁ ⊓ W₁ := Subgroup.mem_inf.2 ⟨mem_subgroupOf.1 h1, mem_subgroupOf.1 h2⟩
    rw [hinf] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hx'))
  set ψ := (subgroupOfEquivOfLe hLW).symm.trans
    (F4Pilot.mapMkEquivOfInfEqBot (W₁.subgroupOf (normalizer (W₁ : Set G)))
      (L₁.subgroupOf (normalizer (W₁ : Set G))) hinf') with hψ
  obtain ⟨-, hZ₁, hLm₁, hcard₁, hq₁⟩ := modelToG_blockSL_compl_facts e hK c
  refine ⟨F4Pilot.isQuasisimple_open_of_mulEquiv ψ hq₁, F4Pilot.center_eq_bot_congr ψ hZ₁,
    lieModel_quotient_center_congr ψ hLm₁, (Nat.card_congr ψ.toEquiv).symm.trans hcard₁, ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (mem_centralizer_iff.1 htC) l (modelToG_le e _ (mem_subgroupOf.1 hl))

theorem centralizer_bar_le_sup [Finite G] (hK : Nat.card K = 2) (ht : orderOf t = 2)
    (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    (hNV : normalizer (modelToG e (pointRadical (K := K) c) : Set G) ⊓ centralizer ({t} : Set G) ≤
      modelToG e (pointRadical (K := K) c) ⊔
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ⊔ zpowers t) :
    centralizer ({QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htW₁⟩} :
        Set (normalizer (W₁ : Set G) ⧸ W₁.subgroupOf (normalizer (W₁ : Set G)))) ≤
      ((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
          (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G)))) ⊔
        zpowers (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htW₁⟩) := by
  set ν := QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) with hν
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set V₁ := modelToG e (pointRadical (K := K) c) with hV₁
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htW₁
    (by rw [hW₁c, card_wOne_inf_centralizer e hK hW₁t]; norm_num)
  set T : Subgroup G := ((L₁.subgroupOf (normalizer (W₁ : Set G))).map ν ⊔
    zpowers (ν ⟨t, htW₁⟩)).comap ν |>.map (normalizer (W₁ : Set G)).subtype with hT
  have hVT : V₁ ≤ T := by
    intro v hv
    have hv' : v ∈ W₁ ⊓ centralizer ({t} : Set G) := by rw [hW₁t]; exact hv
    have hvW : v ∈ W₁ := (Subgroup.mem_inf.1 hv').1
    have hvN : v ∈ normalizer (W₁ : Set G) := le_normalizer hvW
    refine ⟨⟨v, hvN⟩, Subgroup.mem_comap.2 ?_, rfl⟩
    have h1 : ν ⟨v, hvN⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hvW)
    rw [h1]
    exact one_mem _
  have hLT : L₁ ≤ T := by
    intro l hl
    exact ⟨⟨l, hLW hl⟩, Subgroup.mem_comap.2
      (mem_sup_left ⟨⟨l, hLW hl⟩, mem_subgroupOf.2 hl, rfl⟩), rfl⟩
  have htT : t ∈ T :=
    ⟨⟨t, htW₁⟩, Subgroup.mem_comap.2 (mem_sup_right (mem_zpowers _)), rfl⟩
  have hsupT : V₁ ⊔ L₁ ⊔ zpowers t ≤ T := sup_le (sup_le hVT hLT) ((zpowers_le).2 htT)
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hcomm : ν g * ν ⟨t, htW₁⟩ = ν ⟨t, htW₁⟩ * ν g := mem_centralizer_singleton_iff.1 hx
  have hw : (g : G) * t * (g : G)⁻¹ * t⁻¹ ∈ W₁ := by
    have h1 : ν (g * ⟨t, htW₁⟩ * g⁻¹ * (⟨t, htW₁⟩ : normalizer (W₁ : Set G))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1
  set w := (g : G) * t * (g : G)⁻¹ * t⁻¹ with hwdef
  have hwt' : w * t = (g : G) * t * (g : G)⁻¹ := by rw [hwdef]; group
  have hwt : w * t * (w * t) = 1 := by
    rw [hwt']
    calc (g : G) * t * (g : G)⁻¹ * ((g : G) * t * (g : G)⁻¹) = (g : G) * (t * t) * (g : G)⁻¹ := by
          group
      _ = 1 := by rw [ht2]; group
  obtain ⟨u, huW, hu⟩ := exists_conj_eq_of_mul_self_eq_one hW₁2 ht2 hsurj hw hwt
  have hugt : u⁻¹ * (g : G) ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (g : G) * t * (g : G)⁻¹ = u * t * u⁻¹ := by rw [← hwt', hu]
    calc u⁻¹ * g * t = u⁻¹ * ((g : G) * t * (g : G)⁻¹) * g := by group
      _ = u⁻¹ * (u * t * u⁻¹) * g := by rw [h1]
      _ = t * (u⁻¹ * g) := by group
  have huN : u ∈ normalizer (W₁ : Set G) := le_normalizer huW
  have hugN : u⁻¹ * (g : G) ∈ normalizer (W₁ : Set G) := mul_mem (inv_mem huN) g.2
  have hugV : u⁻¹ * (g : G) ∈ normalizer (V₁ : Set G) := by
    have h1 := mem_normalizer_inf_centralizer hugN (mem_centralizer_singleton_iff.1 hugt)
    rw [hW₁t] at h1
    exact h1
  obtain ⟨y, hy, hyeq⟩ := hsupT (hNV (Subgroup.mem_inf.2 ⟨hugV, hugt⟩))
  have hyval : y = (⟨u, huN⟩ : normalizer (W₁ : Set G))⁻¹ * g := Subtype.ext (by simpa using hyeq)
  replace hy := Subgroup.mem_comap.1 hy
  rw [hyval, map_mul, map_inv] at hy
  have hνu : ν ⟨u, huN⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 huW)
  rw [hνu, inv_one, one_mul] at hy
  exact hy

end Bar

section Output

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem normalizer_wOne_ne_top (hset : SeitzSetting G L) {W₁ : Subgroup G}
    (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1) :
    normalizer (W₁ : Set G) ≠ ⊤ := by
  intro h
  have : W₁.Normal := normalizer_eq_top_iff.1 h
  have : IsSimpleGroup G := hset.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W₁ with h1 | h1
  · rw [h1, Subgroup.card_bot] at hW₁c
    norm_num at hW₁c
  · obtain ⟨a, b, hab⟩ := hset.2.1
    exact hab (mul_comm_of_forall_mul_self_eq_one hW₁2 (h1 ▸ mem_top a) (h1 ▸ mem_top b))

theorem neighbourOvergroupSLmField_nOneBar (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 4) (hdet : SLmEvenTypeDetAt 4)
    (hspor : SporadicFixedLFourTwoInput) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (c : Fin 5)
    {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    (hNV : normalizer (modelToG e (pointRadical (K := K) c) : Set G) ⊓ centralizer ({t} : Set G) ≤
      modelToG e (pointRadical (K := K) c) ⊔
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ⊔ zpowers t)
    (hnn : ¬ ((((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
            (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))).map
        (QuotientGroup.mk' (oddCore (normalizer (W₁ : Set G) ⧸
          W₁.subgroupOf (normalizer (W₁ : Set G)))))).Normal) :
    NeighbourOvergroupSLmField
        (QuotientGroup.mk' (oddCore (normalizer (W₁ : Set G) ⧸
          W₁.subgroupOf (normalizer (W₁ : Set G))))
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htW₁⟩))
        ((((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
            (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))).map
        (QuotientGroup.mk' (oddCore (normalizer (W₁ : Set G) ⧸
          W₁.subgroupOf (normalizer (W₁ : Set G)))))) 4 1 ∧
      center ((((modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5)))).subgroupOf
            (normalizer (W₁ : Set G))).map
          (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))).map
        (QuotientGroup.mk' (oddCore (normalizer (W₁ : Set G) ⧸
          W₁.subgroupOf (normalizer (W₁ : Set G)))))) = ⊥ := by
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  obtain ⟨hLq, hLZ, hLm, hLc, hLs⟩ := leviBar_facts e hK htC hW₁c hLW htW₁
  have hs := orderOf_mk_wOne_eq_two e hK ht hW₁c hW₁2 hW₁t htW₁
  have hCs := centralizer_bar_le_sup e hK ht hW₁c hW₁2 hW₁t htW₁ hLW hNV
  have hN₁ := normalizer_wOne_ne_top hset hW₁c hW₁2
  have hsec : ∀ Kc : Subgroup ((normalizer (W₁ : Set G) ⧸
      W₁.subgroupOf (normalizer (W₁ : Set G))) ⧸ oddCore (normalizer (W₁ : Set G) ⧸
        W₁.subgroupOf (normalizer (W₁ : Set G)))), IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => catalog_center_quotient_of_kProper_of_surjective_nOne hset.2.2.1 hN₁
      ((QuotientGroup.mk' _).comp (QuotientGroup.mk' _))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) hKc.1
  exact neighbourOvergroupSLmField_of_centralizer_le_sup hcat hdet hspor hs hLs hLq hLZ hLm hLc
    hCs hsec hnn

end Output

end CFSG.SeitzReduction.LinearPilot
