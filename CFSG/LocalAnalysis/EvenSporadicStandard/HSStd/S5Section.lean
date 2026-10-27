module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5A8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Steps
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv
open scoped commutatorElement

section Section

variable {G : Type} [Group G]

@[expose] def vElem (v : G) : ↥(centralizer ({v} : Set G)) :=
  ⟨v, mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def vSub (v : G) : Subgroup ↥(centralizer ({v} : Set G)) := zpowers (vElem v)

instance vSub_normal (v : G) : (vSub v).Normal where
  conj_mem := by
    intro n hn g
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hc : g * vElem v = vElem v * g :=
      Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
    have : g * vElem v ^ k * g⁻¹ = vElem v ^ k := by
      rw [(Commute.zpow_right (show Commute g (vElem v) from hc) k).eq]
      simp
    rw [this]
    exact zpow_mem_zpowers _ _

theorem vSub_le_center (v : G) : vSub v ≤ center ↥(centralizer ({v} : Set G)) := by
  rw [vSub, zpowers_le, mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)

abbrev OuterSection (v : G) : Type := ↥(centralizer ({v} : Set G)) ⧸ vSub v

@[expose] def sectionImage (v : G) (A : Subgroup G) : Subgroup (OuterSection v) :=
  (A.subgroupOf (centralizer ({v} : Set G))).map (QuotientGroup.mk' (vSub v))

theorem orderOf_vElem {v : G} (hv2 : v * v = 1) (hv1 : v ≠ 1) : orderOf (vElem v) = 2 := by
  have h : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  rw [← h]
  exact (Subgroup.orderOf_coe (vElem v)).symm

theorem card_vSub {v : G} (hv2 : v * v = 1) (hv1 : v ≠ 1) : Nat.card (vSub v) = 2 := by
  rw [vSub, Nat.card_zpowers, orderOf_vElem hv2 hv1]

theorem mk_comp_subtype_injective {v : G} (hv2 : v * v = 1) (hv1 : v ≠ 1) (A : Subgroup G)
    (hvA : v ∉ A) :
    Function.Injective
      ((QuotientGroup.mk' (vSub v)).comp (A.subgroupOf (centralizer ({v} : Set G))).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
  have hxA : (x : ↥(centralizer ({v} : Set G))) ∈ A.subgroupOf (centralizer ({v} : Set G)) := x.2
  rw [mem_bot]
  have hord := orderOf_vElem hv2 hv1
  have hsq : vElem v ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← hord]
    exact pow_orderOf_eq_one _
  have hk' : vElem v ^ k = vElem v ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, hsq]
    simp
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · apply Subtype.ext
    rw [← hk, hk', h0]
    simp
  · exfalso
    apply hvA
    rw [hk', h1, zpow_one] at hk
    have : (x : ↥(centralizer ({v} : Set G))) = vElem v := hk.symm
    have h2 : vElem v ∈ A.subgroupOf (centralizer ({v} : Set G)) := this ▸ hxA
    exact h2

theorem sectionImage_equiv {v : G} (hv2 : v * v = 1) (hv1 : v ≠ 1) {A : Subgroup G}
    (hA : A ≤ centralizer ({v} : Set G)) (hvA : v ∉ A) :
    Nonempty (↥(sectionImage v A) ≃* ↥A) := by
  set H := centralizer ({v} : Set G)
  set f := (QuotientGroup.mk' (vSub v)).comp (A.subgroupOf H).subtype with hf
  have hrange : f.range = sectionImage v A := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have e1 : ↥(A.subgroupOf H) ≃* ↥(sectionImage v A) :=
    (MonoidHom.ofInjective (mk_comp_subtype_injective hv2 hv1 A hvA)).trans
      (MulEquiv.subgroupCongr hrange)
  exact ⟨e1.symm.trans (Subgroup.subgroupOfEquivOfLe hA)⟩

theorem alternatingGroup_eight_isPerfect : Group.IsPerfect (alternatingGroup (Fin 8)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hc : Subgroup.center (alternatingGroup (Fin 8)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 8)))
    with h | h
  · exfalso
    have htop : (⊤ : Subgroup (alternatingGroup (Fin 8))) ≤
        Subgroup.centralizer ((⊤ : Subgroup (alternatingGroup (Fin 8))) : Set _) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact h
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hc, top_le_iff] at htop
    have : Nontrivial (alternatingGroup (Fin 8)) := hs.toNontrivial
    exact (bot_ne_top htop).elim
  · exact h

theorem commutator_eq_self_of_equiv_alternating_eight {Y : Type*} [Group Y] {B : Subgroup Y}
    (e : ↥B ≃* alternatingGroup (Fin 8)) : ⁅B, B⁆ = B := by
  have hperf : commutator ↥B = ⊤ := by
    have h1 : commutator (alternatingGroup (Fin 8)) = ⊤ := alternatingGroup_eight_isPerfect.1
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ (commutator ↥B).map e.toMonoidHom := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
        ← commutator_def, h1]
      exact mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    exact (e.injective hyx) ▸ hy
  have h2 : (commutator ↥B).map B.subtype = ⁅B, B⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h2, hperf, Subgroup.map_top, Subgroup.range_subtype]

theorem derivedCentralizerIn_le_centralizer (L : Subgroup G) (v : G) :
    derivedCentralizerIn L v ≤ centralizer ({v} : Set G) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2.1

theorem derivedCentralizerIn_le (L : Subgroup G) (v : G) : derivedCentralizerIn L v ≤ L := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2.2

theorem derivedCentralizerIn_equiv {L : Subgroup G} {v : G}
    (h : Nonempty (↥(centralizer ({v} : Set G) ⊓ L) ≃* Perm (Fin 8))) :
    Nonempty (↥(derivedCentralizerIn L v) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := h
  set T := centralizer ({v} : Set G) ⊓ L with hT
  let ψ : Perm (Fin 8) →* G := T.subtype.comp e.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hrange : ψ.range = T := by
    ext g
    constructor
    · rintro ⟨σ, rfl⟩
      exact (e.symm σ).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [ψ]⟩
  have hΛ : derivedCentralizerIn L v = (alternatingGroup (Fin 8)).map ψ :=
    map_commutator_range ψ hψ T hrange
  exact ⟨(MulEquiv.subgroupCongr hΛ).trans (Subgroup.equivMapOfInjective _ ψ hψ).symm⟩

theorem commutator_mul_central {Y : Type*} [Group Y] {a c y : Y} (hc : c ∈ center Y) :
    ⁅a * c, y⁆ = ⁅a, y⁆ := by
  have hcy : c * y * c⁻¹ = y := by
    rw [← mem_center_iff.1 hc y, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * y * (a * c)⁻¹ * y⁻¹ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [hcy]

theorem commutator_mul_central_mul {Y : Type*} [Group Y] {a b c d : Y} (hc : c ∈ center Y)
    (hd : d ∈ center Y) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  rw [commutator_mul_central hc, ← commutatorElement_inv, commutator_mul_central hd,
    commutatorElement_inv]

theorem subgroupOf_normal_of_sectionImage_normal {v : G} {A : Subgroup G}
    (hA : A ≤ centralizer ({v} : Set G)) (e : ↥A ≃* alternatingGroup (Fin 8))
    (hN : (sectionImage v A).Normal) : (A.subgroupOf (centralizer ({v} : Set G))).Normal := by
  set H := centralizer ({v} : Set G) with hH
  set AH := A.subgroupOf H with hAH
  have hperf : ⁅AH, AH⁆ = AH :=
    commutator_eq_self_of_equiv_alternating_eight ((Subgroup.subgroupOfEquivOfLe hA).trans e)
  have hPn : ((sectionImage v A).comap (QuotientGroup.mk' (vSub v))).Normal :=
    hN.comap (QuotientGroup.mk' (vSub v))
  set P := (sectionImage v A).comap (QuotientGroup.mk' (vSub v)) with hP
  have hAP : AH ≤ P := fun x hx => ⟨x, hx, rfl⟩
  have h1 : ⁅P, P⁆ = AH := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      have hc1 : a⁻¹ * x ∈ vSub v := QuotientGroup.eq.1 hax
      have hc2 : b⁻¹ * y ∈ vSub v := QuotientGroup.eq.1 hby
      have hx' : x = a * (a⁻¹ * x) := by group
      have hy' : y = b * (b⁻¹ * y) := by group
      rw [hx', hy', commutator_mul_central_mul (vSub_le_center v hc1) (vSub_le_center v hc2)]
      rw [← hperf]
      exact Subgroup.commutator_mem_commutator ha hb
    · conv_lhs => rw [← hperf]
      exact Subgroup.commutator_mono hAP hAP
  have : ⁅P, P⁆.Normal := inferInstance
  rw [h1] at this
  exact this

end Section

section Outer

variable {G : Type} [Group G] [Finite G]

structure HSOuterSetup (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G)
    (S : Subgroup G) (z n v s : G) : Prop where
  setting : HSLemma21Setting G L
  t_mem : t ∈ centralizer (L : Set G)
  t_two : orderOf t = 2
  index : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2
  ctx : HSOuterCtx L t S z n v s
  not_normal : ¬ ((derivedCentralizerIn L v).subgroupOf (centralizer ({v} : Set G))).Normal

variable {L : Subgroup G} {t : G} {S : Subgroup G} {z n v s : G}

theorem HSOuterSetup.v_ne_one (h : HSOuterSetup G L t S z n v s) : v ≠ 1 := by
  intro hv
  exact h.ctx.v_outer (hv ▸ one_mem _)

theorem HSOuterSetup.v_not_mem_derived (h : HSOuterSetup G L t S z n v s) :
    v ∉ derivedCentralizerIn L v := fun hv =>
  h.ctx.v_outer
    ((le_sup_left : L ≤ L ⊔ zpowers t) (derivedCentralizerIn_le L v hv))

theorem HSOuterSetup.sectionImage_equiv (h : HSOuterSetup G L t S z n v s) :
    Nonempty (↥(sectionImage v (derivedCentralizerIn L v)) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e1⟩ := _root_.CFSG.EvenSporadicStandard.HSStd.sectionImage_equiv h.ctx.v_sq h.v_ne_one
    (derivedCentralizerIn_le_centralizer L v) h.v_not_mem_derived
  obtain ⟨e2⟩ := derivedCentralizerIn_equiv h.ctx.v_cls
  exact ⟨e1.trans e2⟩

theorem HSOuterSetup.not_normal_sectionImage (h : HSOuterSetup G L t S z n v s) :
    ¬ (sectionImage v (derivedCentralizerIn L v)).Normal := fun hN =>
  h.not_normal (subgroupOf_normal_of_sectionImage_normal
    (derivedCentralizerIn_le_centralizer L v)
    (derivedCentralizerIn_equiv h.ctx.v_cls).some hN)

theorem HSOuterSetup.t_comm_v (h : HSOuterSetup G L t S z n v s) : t * v = v * t :=
  (mem_centralizer_singleton_iff.1 (h.ctx.fusion.le h.ctx.v_mem)).symm

theorem HSOuterSetup.t_ne_one (h : HSOuterSetup G L t S z n v s) : t ≠ 1 := by
  intro ht
  have h2 := h.t_two
  rw [ht, orderOf_one] at h2
  omega

theorem HSOuterSetup.t_ne_v (h : HSOuterSetup G L t S z n v s) : t ≠ v := by
  intro htv
  exact h.ctx.v_outer (htv ▸ (le_sup_right : zpowers t ≤ L ⊔ zpowers t) (mem_zpowers t))

@[expose] def HSOuterSetup.tElem (h : HSOuterSetup G L t S z n v s) :
    ↥(centralizer ({v} : Set G)) :=
  ⟨t, mem_centralizer_singleton_iff.2 h.t_comm_v⟩

@[expose] def HSOuterSetup.tBar (h : HSOuterSetup G L t S z n v s) : OuterSection v :=
  QuotientGroup.mk h.tElem

theorem HSOuterSetup.tBar_mem_centralizer (h : HSOuterSetup G L t S z n v s) :
    h.tBar ∈ centralizer ((sectionImage v (derivedCentralizerIn L v) : Subgroup (OuterSection v)) :
      Set (OuterSection v)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have hal : (a : G) ∈ L := derivedCentralizerIn_le L v ha
  have hc : (a : G) * t = t * a := mem_centralizer_iff.1 h.t_mem a hal
  change (QuotientGroup.mk a : OuterSection v) * QuotientGroup.mk h.tElem =
    QuotientGroup.mk h.tElem * QuotientGroup.mk a
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hc

theorem HSOuterSetup.orderOf_tBar (h : HSOuterSetup G L t S z n v s) : orderOf h.tBar = 2 := by
  have h2 : h.tBar ^ 2 = 1 := by
    rw [HSOuterSetup.tBar, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : h.tElem ^ 2 = 1 := by
      apply Subtype.ext
      show t ^ 2 = 1
      rw [← h.t_two]
      exact pow_orderOf_eq_one t
    rw [this]
    exact one_mem _
  refine orderOf_eq_prime h2 ?_
  intro h1
  rw [HSOuterSetup.tBar, QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h1
  have hord := orderOf_vElem h.ctx.v_sq h.v_ne_one
  have hsq : vElem v ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← hord]
    exact pow_orderOf_eq_one _
  have hk' : vElem v ^ k = vElem v ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, hsq]
    simp
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1'
  · rw [hk', h0, zpow_zero] at hk
    exact h.t_ne_one (congrArg Subtype.val hk.symm)
  · rw [hk', h1', zpow_one] at hk
    exact h.t_ne_v (congrArg Subtype.val hk.symm)

end Outer

end CFSG.EvenSporadicStandard.HSStd
