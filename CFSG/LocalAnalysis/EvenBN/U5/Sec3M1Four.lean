module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Three
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Field
public import CFSG.LocalAnalysis.EvenBN.U4.LayersGMS
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearStageZero
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Walter.J1
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8026Base
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.U4 (centralizer_subgroupOf centralizer_singleton_subgroupOf
  normalizer_subgroupOf' inf_subgroupOf' map_subtype_subgroupOf card_subgroupOf_of_le
  zpowers_mk_eq isSylowOf_subgroupOf existsUnique_subgroupOf_iff
  map_closure_commutator_subgroupOf not_normal_of_isSylowOf_zpowers)

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

noncomputable abbrev Hyp.tOne (hd : d.Hyp) : centralizer (d.I₁ : Set G) :=
  ⟨d.t, hd.t_mem_centralizer_I₁⟩

theorem Hyp.N₁_le_centralizer_t (hd : d.Hyp) : d.N₁ ≤ centralizer ({d.t} : Set G) :=
  (d.pull_le_L _).trans hd.L_le_centralizer

theorem Hyp.localFieldBound_one (hd : d.Hyp) (hf : 3 ≤ f) :
    GMS.LocalFieldBound (d.N₁.subgroupOf (centralizer (d.I₁ : Set G))) hd.tOne (2 * f) := by
  set H := centralizer (d.I₁ : Set G) with hHdef
  refine ⟨fun x hx => ?_, fun hn => absurd hn (by omega)⟩
  rw [centralizer_singleton_subgroupOf hd.t_mem_centralizer_I₁, mem_subgroupOf] at hx
  set c : G := (x : G) with hcdef
  have hcI : c ∈ centralizer (d.I₁ : Set G) := x.2
  have hcL := hd.centralizer_le_normalizer hx
  have hc2L : c * c ∈ normalizer (d.L : Set G) := mul_mem hcL hcL
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨c, hcL⟩)
  have hy2 : Phi h (y * y) = d.act ⟨c * c, hc2L⟩ := by
    rw [map_mul, hy, ← map_mul]
    rfl
  have hI := d.act_I₁_of_mem_centralizer hcL hy hcI
  have hI' := d.act_I₁_of_mem_centralizer hc2L hy2 (mul_mem hcI hcI)
  obtain ⟨g, hg, hgn⟩ := exists_N₁_of_sq hf hI hI'
  have hgH : d.η g ∈ H := d.N₁_le_centralizer_I₁ ⟨g, hg, rfl⟩
  have hbC : (d.η g)⁻¹ * (c * c) ∈ centralizer (d.N₁ : Set G) := by
    refine mem_centralizer_iff.2 ?_
    rintro _ ⟨n, hn, rfl⟩
    have e := d.conj_η_eq hc2L hy2 n
    rw [hgn n hn, map_mul, map_mul, map_inv] at e
    calc d.η n * ((d.η g)⁻¹ * (c * c)) = (d.η g)⁻¹ * (d.η g * d.η n * (d.η g)⁻¹) * (c * c) := by
          group
      _ = (d.η g)⁻¹ * (c * c * d.η n * (c * c)⁻¹) * (c * c) := by rw [e]
      _ = (d.η g)⁻¹ * (c * c) * d.η n := by group
  have hbH : (d.η g)⁻¹ * (c * c) ∈ H := mul_mem (inv_mem hgH) (mul_mem hcI hcI)
  have hcN : (⟨(d.η g)⁻¹ * (c * c), hbH⟩ : H) ∈
      centralizer ((d.N₁.subgroupOf H : Subgroup H) : Set H) := by
    rw [centralizer_subgroupOf d.N₁_le_centralizer_I₁, mem_subgroupOf]
    exact hbC
  have e : x ^ 2 = ⟨d.η g, hgH⟩ * ⟨(d.η g)⁻¹ * (c * c), hbH⟩ :=
    Subtype.ext (by simp [sq, hcdef])
  rw [e]
  exact mul_mem (mem_sup_left (mem_subgroupOf.2 ⟨g, hg, rfl⟩)) (mem_sup_right hcN)

theorem Hyp.gmsLinearLocalApplication_one (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    GMSLinearLocalApplication (d.N₁.subgroupOf (centralizer (d.I₁ : Set G))) hd.tOne
      (d.U₁.subgroupOf (centralizer (d.I₁ : Set G)))
      (d.V₁.subgroupOf (centralizer (d.I₁ : Set G)))
      (d.D₁.subgroupOf (centralizer (d.I₁ : Set G))) (2 * f) := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer (d.I₁ : Set G) with hHdef
  set tH : H := hd.tOne with htHdef
  have hNH : d.N₁ ≤ H := d.N₁_le_centralizer_I₁
  have hUH : d.U₁ ≤ H := d.U₁_le_N₁.trans hNH
  have hVH : d.V₁ ≤ H := d.V₁_le_centralizer_I₁
  have hDH : d.D₁ ≤ H := d.D₁_le_N₁.trans hNH
  have hCt : centralizer ({tH} : Set H) = (centralizer ({d.t} : Set G)).subgroupOf H :=
    centralizer_singleton_subgroupOf hd.t_mem_centralizer_I₁
  have hCA : centralizer ((d.N₁.subgroupOf H : Subgroup H) : Set H) =
      (H ⊓ centralizer (d.N₁ : Set G)).subgroupOf H := by
    rw [centralizer_subgroupOf hNH, inf_subgroupOf_left]
  have hzt : zpowers tH = (zpowers d.t).subgroupOf H := zpowers_mk_eq hd.t_mem_centralizer_I₁
  have htH2 : orderOf tH = 2 := by rw [htHdef, Subgroup.orderOf_mk, hd.t_two]
  have hsyl : IsSylowOf 2 (zpowers tH)
      (centralizer ((d.N₁.subgroupOf H : Subgroup H) : Set H)) := by
    rw [hzt, hCA]
    exact isSylowOf_subgroupOf (zpowers_le.2 hd.t_mem_centralizer_I₁) inf_le_left
      hd.isSylowOf_zpowers_N₁
  have htC : tH ∈ centralizer ((d.N₁.subgroupOf H : Subgroup H) : Set H) := by
    rw [hCA, mem_subgroupOf]
    exact Subgroup.mem_inf.2 ⟨hd.t_mem_centralizer_I₁, hd.t_mem_centralizer_N₁⟩
  have he : ∀ S : Sylow 2 H, ∃ x ∈ (S : Subgroup H), x * tH ≠ tH * x := by
    intro S
    obtain ⟨y, ⟨x, hxS, rfl⟩, hy⟩ := hd.exists_not_commute_of_isSylowOf hGMS
      (S := (S : Subgroup H).map H.subtype) ⟨S, rfl⟩
    exact ⟨x, hxS, fun e => hy (by simpa using congrArg Subtype.val e)⟩
  have hnorm : centralizer ({tH} : Set H) ≤
      normalizer ((d.N₁.subgroupOf H : Subgroup H) : Set H) := by
    intro x hx
    rw [hCt, mem_subgroupOf] at hx
    rw [normalizer_subgroupOf' hNH, mem_subgroupOf]
    refine mem_normalizer_fintype fun n hn => ?_
    exact hd.conj_mem_N₁ (hd.centralizer_le_normalizer hx) x.2 hn
  have hAC : d.N₁.subgroupOf H ≤ centralizer ({tH} : Set H) := by
    rw [hCt]
    exact subgroupOf_mono _ hd.N₁_le_centralizer_t
  have := h.finite
  let := Fintype.ofFinite K
  have hq : (Matrix.SpecialLinearGroup (Fin 2) K) ≃* (d.N₁.subgroupOf H) :=
    d.N₁equiv.trans (subgroupOfEquivOfLe hNH).symm
  refine ⟨by have := hd.two_le; omega, htH2, ⟨?_, ?_, ?_⟩, ⟨htC, ?_, hAC, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun S _ => he S⟩
  ·
    have hsq : CFSG.Open.IsQuasisimple (d.N₁.subgroupOf H) :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv (subgroupOfEquivOfLe hNH)
        hd.isQuasisimple_N₁
    have hR : ∀ r ∈ zpowers tH, r ≠ 1 → r = tH := by
      intro r hr hr1
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
      have hk2 : tH ^ k = tH ^ (k % 2) := by
        rw [← zpow_mod_orderOf, htH2]
        norm_cast
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · rw [hk2, h0, zpow_zero] at hr1 ⊢
        exact absurd rfl hr1
      · rw [hk2, h1, zpow_one]
    refine CFSG.ComponentClassification.AS81.Sec2Quot.standardComponentIsStandard_of_sylow hsq
      hsyl (fun hb => ?_) (fun x r hr hr1 hxr => ?_) (fun x r hr hr1 hxr => ?_) ?_
    · have := mem_zpowers tH
      rw [hb, mem_bot] at this
      rw [this, orderOf_one] at htH2
      exact absurd htH2 (by norm_num)
    ·
      obtain rfl := hR r hr hr1
      have hxr1 : x * tH * x⁻¹ ≠ 1 := fun e => hr1 (by
        calc tH = x⁻¹ * (x * tH * x⁻¹) * x := by group
          _ = 1 := by rw [e]; group)
      have hc := hR _ hxr hxr1
      refine hnorm (mem_centralizer_singleton_iff.2 ?_)
      calc x * tH = x * tH * x⁻¹ * x := by group
        _ = tH * x := by rw [hc]
    ·
      obtain rfl := hR r hr hr1
      apply hd.sec3_1'.2.2.2.2.2 (x : G)⁻¹
      rw [mem_subgroupOf] at hxr
      rw [inv_inv]
      exact d.pull_le_L _ hxr
    ·
      refine ⟨⟨d.η (uSU h 1), hUH (d.η_uSU_mem 1)⟩,
        mem_subgroupOf.2 (d.U₁_le_N₁ (d.η_uSU_mem 1)), fun e1 => ?_, ?_⟩
      · have h1 : d.η (uSU h 1) = 1 := by simpa using congrArg Subtype.val e1
        have := d.η_uSU_injective (show d.η (uSU h 1) = d.η (uSU h 0) by
          rw [uSU_zero, map_one, h1])
        exact one_ne_zero this
      · apply Subtype.ext
        simp [sq, mul_self_of_mem_U₁ (d.η_uSU_mem (h := h) 1)]
  ·
    exact not_normal_of_isSylowOf_zpowers htH2 htC hsyl he
  ·
    refine ⟨K, inferInstance, inferInstance, ?_, ⟨hq.symm⟩⟩
    rw [← Nat.card_eq_fintype_card, h.card_eq_sq, ← pow_mul, mul_comm]
  ·
    obtain ⟨S, hS'⟩ := hsyl.exists_sylow_eq_subgroupOf
    exact ⟨S, hS'⟩
  ·
    exact (normal_subgroupOf_iff_le_normalizer hAC).2 hnorm
  ·
    exact subgroupOf_mono _ d.U₁_le_N₁
  ·
    exact (isSylowOf_subgroupOf hUH hNH hd.isSylowOf_U₁_N₁).exists_sylow_eq_subgroupOf
  ·
    have := hd.isElementaryAbelian_V₁ hGMS
    exact CFSG.IsElementaryAbelian.subgroupOf hVH
  ·
    rw [card_subgroupOf_of_le hVH, hd.card_V₁ hGMS]
    ring
  ·
    rw [normalizer_subgroupOf' hVH, mem_subgroupOf]
    exact hd.t_mem_normalizer_V₁
  ·
    rw [inf_subgroupOf', hd.V₁_inf_N₁ hGMS]
  ·
    rw [hCt, inf_subgroupOf', hd.V₁_inf_centralizer_t hGMS]
  ·
    apply map_injective H.subtype_injective
    rw [map_closure_commutator_subgroupOf hVH hd.t_mem_centralizer_I₁,
      map_subtype_subgroupOf hUH]
    exact hd.closure_commutator_V₁ hGMS
  ·
    rw [normalizer_subgroupOf' hUH, inf_subgroupOf']
    exact subgroupOf_mono _ (le_inf d.D₁_le_N₁ d.D₁_le_normalizer_U₁)
  ·
    have := d.isCyclic_D₁
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hDH).symm.toMonoidHom
      (subgroupOfEquivOfLe hDH).symm.surjective
  ·
    rw [card_subgroupOf_of_le hDH, d.card_D₁, ← pow_mul, mul_comm]
  ·
    rw [inf_subgroupOf', hd.D₁_inf_U₁, bot_subgroupOf]
  ·
    rw [← subgroupOf_sup hUH hDH, normalizer_subgroupOf' hUH, inf_subgroupOf', d.U₁_sup_D₁]
  ·
    rw [normalizer_subgroupOf' hVH]
    exact subgroupOf_mono _ (hd.D₁_le_normalizer_V₁ hGMS)
  ·
    rw [hCt]
    exact subgroupOf_mono _ hd.D₁_le_centralizer_t
  ·
    intro u hu hu1 w hw hw1
    have hu1' : (u : G) ≠ 1 := fun e1 => hu1 (Subtype.ext e1)
    have hw1' : (w : G) ≠ 1 := fun e1 => hw1 (Subtype.ext e1)
    refine (existsUnique_congr fun x => ?_).2 ((existsUnique_subgroupOf_iff hDH
      (fun g => g * (u : G) * g⁻¹ = w)).2 (d.D₁_regular_U₁ _ hu hu1' _ hw hw1'))
    rw [Subtype.ext_iff]
    simp
  ·
    intro v hv hvU w hw hwU
    refine (existsUnique_congr fun x => ?_).2 ((existsUnique_subgroupOf_iff hDH
      (fun g => (g * (v : G) * g⁻¹)⁻¹ * w ∈ d.U₁)).2
        (hd.D₁_regular_V₁ hGMS _ hv (fun h1 => hvU (mem_subgroupOf.2 h1)) _ hw
          (fun h1 => hwU (mem_subgroupOf.2 h1))))
    rw [mem_subgroupOf]
    simp

end Data

end CFSG.LocalAnalysis.EvenBN.U5
