module

public import CFSG.LargeExtraspecial.S8CorBUniv
public import CFSG.LargeExtraspecial.S45QMain
import CFSG.Adapters.WholeGroupLayer
public import CFSG.LargeExtraspecial.S6ThreeC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] def conjCentM (t : S.O) : Set S.O :=
  {τ | τ ∈ S.Mbar ∧ τ * t = t * τ ∧ ∃ x ∈ S.Mbar, τ = x * t * x⁻¹}

theorem eq_bot_of_isSubnormal_top_Mbar (P : Subgroup S.Mbar) (hP : IsSubnormal P ⊤)
    (h2 : IsPGroup 2 P) : P = ⊥ := by
  have hle : P.map S.Mbar.subtype ≤ S.Mbar := map_subtype_le P
  have e : (P.map S.Mbar.subtype).subgroupOf S.Mbar = P :=
    comap_map_eq_self_of_injective S.Mbar.subtype_injective P
  have hsub : IsSubnormal (P.map S.Mbar.subtype) S.Mbar := by
    refine (S5.isSubnormal_subgroupOf_top_iff hle).mp ?_
    rw [e]
    exact hP
  have h2' : IsPGroup 2 (P.map S.Mbar.subtype) := h2.map _
  have := S5.eq_bot_of_isSubnormal_Mbar S hsub h2'
  exact (map_eq_bot_iff_of_injective P S.Mbar.subtype_injective).mp this

noncomputable abbrev NbarM (S : Setting G) (g : G) (t : S.O) : Subgroup S.Mbar :=
  (Nbar S g t).subgroupOf S.Mbar

noncomputable def RbarX (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O)
    (X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) : Subgroup S.O :=
  (X.comap (resV haQ t)).map (Rbar S g t).subtype

theorem mem_RbarX {haQ : g * S.z * g⁻¹ ∈ S.QG} {t : S.O}
    {X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} {x : S.O} :
    x ∈ RbarX haQ t X ↔ ∃ hx : x ∈ Rbar S g t, resV haQ t ⟨x, hx⟩ ∈ X := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.2, hr⟩
  · rintro ⟨hx, hX⟩
    exact ⟨⟨x, hx⟩, hX, rfl⟩

theorem RbarX_le_Rbar (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O)
    (X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) : RbarX haQ t X ≤ Rbar S g t :=
  map_subtype_le _

theorem Nbar_le_RbarX (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) : Nbar S g t ≤ RbarX haQ t X := fun n hn =>
  mem_RbarX.mpr ⟨Nbar_le_Rbar hn, by
    rw [(resV_eq_one_iff haQ ⟨n, Nbar_le_Rbar hn⟩).mpr hn]
    exact one_mem X⟩

theorem normal_NbarX (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) :
    ((NbarM S g t).subgroupOf ((RbarX haQ t X).subgroupOf S.Mbar)).Normal := ⟨fun n hn r => by
  rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (r : S.Mbar).2
  have hr : S.ρ k ∈ Rbar S g t := by
    rw [hk]
    exact RbarX_le_Rbar haQ t X (mem_subgroupOf.mp r.2)
  have := conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hr) hn
  rw [hk] at this
  exact this⟩

noncomputable def resX (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O)
    (X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) :
    (RbarX haQ t X).subgroupOf S.Mbar →* X where
  toFun r := ⟨resV haQ t ⟨((r : S.Mbar) : S.O), (mem_RbarX.mp (mem_subgroupOf.mp r.2)).1⟩,
    (mem_RbarX.mp (mem_subgroupOf.mp r.2)).2⟩
  map_one' := Subtype.ext (map_one (resV haQ t))
  map_mul' _ _ := Subtype.ext (map_mul (resV haQ t) ⟨_, _⟩ ⟨_, _⟩)

theorem resX_eq_one_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) (r : (RbarX haQ t X).subgroupOf S.Mbar) :
    resX haQ t X r = 1 ↔ r ∈ (NbarM S g t).subgroupOf ((RbarX haQ t X).subgroupOf S.Mbar) := by
  rw [mem_subgroupOf, mem_subgroupOf]
  have h := resV_eq_one_iff haQ
    ⟨((r : S.Mbar) : S.O), (mem_RbarX.mp (mem_subgroupOf.mp r.2)).1⟩
  exact ⟨fun h1 => h.mp (congrArg Subtype.val h1), fun h1 => Subtype.ext (h.mpr h1)⟩

theorem resX_surjective (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    {X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hX : X ≤ RmodN S g t) :
    Function.Surjective (resX haQ t X) := by
  intro x
  have hx : (x : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV haQ t).range := by
    rw [range_resV]
    exact hX x.2
  obtain ⟨r, hr⟩ := hx
  have hrX : ((r : S.O) : S.O) ∈ RbarX haQ t X := mem_RbarX.mpr ⟨r.2, by
    change resV haQ t r ∈ X
    rw [hr]
    exact x.2⟩
  exact ⟨⟨⟨r, Rbar_le_Mbar r.2⟩, hrX⟩, Subtype.ext hr⟩

noncomputable def quotEquivX (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O)
    {X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hX : X ≤ RmodN S g t)
    [((NbarM S g t).subgroupOf ((RbarX haQ t X).subgroupOf S.Mbar)).Normal] :
    (↥((RbarX haQ t X).subgroupOf S.Mbar) ⧸
      (NbarM S g t).subgroupOf ((RbarX haQ t X).subgroupOf S.Mbar)) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq (by
      ext r; rw [MonoidHom.mem_ker]; exact (resX_eq_one_iff haQ X r).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (resX haQ t X) (resX_surjective haQ hX))

theorem exists_noncomm_of_nonabelianSylowTwo {Y V : Type*} [Group Y] [Finite Y]
    [AddCommGroup V] [Module (ZMod 2) V] {X : Subgroup (V ≃ₗ[ZMod 2] V)} (e : Y ≃* X)
    (hnab : S5.NonabelianSylowTwo X) (P : Sylow 2 Y) :
    ∃ x ∈ (P : Subgroup Y), ∃ y ∈ (P : Subgroup Y), x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv Y e.toEquiv
  set P' : Sylow 2 X := P.mapSurjective (f := e.toMonoidHom) e.surjective with hP'
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab ((P' : Subgroup X).map X.subtype) (map_subtype_le _)
    (P'.isPGroup'.map _) (by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        comap_map_eq_self_of_injective X.subtype_injective]
      exact P'.not_dvd_index)
  obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
  obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
  have hx1 : x' ∈ (P : Subgroup Y).map e.toMonoidHom := hx'
  have hy1 : y' ∈ (P : Subgroup Y).map e.toMonoidHom := hy'
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx1
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hy1
  refine ⟨a, ha, b, hb, fun hab => hxy ?_⟩
  have := congrArg (fun z => X.subtype (e.toMonoidHom z)) hab
  simpa only [map_mul] using this

theorem Nbar_le_zpowers_of_oddCore (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hN2 : IsPGroup 2 (Nbar S g t)) (hO3 : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    {K : Subgroup S.Mbar} (hKN : K.Normal) (hKodd : Odd (Nat.card K))
    (hUK : normalClosure ({(⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar)} : Set S.Mbar) =
      K ⊔ zpowers ⟨t, S.Lbar_le_Mbar g ht⟩) :
    Nbar S g t ≤ zpowers t := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  set tX : S.Mbar := ⟨t, htM⟩ with htX
  have hKO : K ≤ timmesfeldOddCore S.Mbar := le_sSup ⟨hKN, hKodd⟩
  have hOn' := S5.timmesfeldOddCore_normal S.Mbar
  refine le_zpowers_of_conj_mem (X := S.Mbar) (O := (timmesfeldOddCore S.Mbar).map
    S.Mbar.subtype) (L := S.Lbar g) htM htt ht1
    (fun P hP h2 => S5.eq_bot_of_isSubnormal_Mbar S hP h2) (map_subtype_le _) ?_ ?_ ?_
    (S.Lbar_le_Mbar g) (fun a ha b hb => Lbar_comm S haQ ha hb)
    (fun l hl => mul_self_of_mem_Lbar S haQ hl) ht ?_ ?_ Nbar_le_Rbar ?_ hN2
    (self_mem_Nbar H ht)
  · intro x hx o' ho'
    obtain ⟨o, ho, ho'o⟩ := Subgroup.mem_map.mp ho'
    have h1 : (⟨x, hx⟩ : S.Mbar) * o * (⟨x, hx⟩ : S.Mbar)⁻¹ ∈ timmesfeldOddCore S.Mbar :=
      hOn'.conj_mem o ho _
    have h2 := Subgroup.mem_map_of_mem S.Mbar.subtype h1
    rw [map_mul, map_mul, map_inv, ho'o] at h2
    exact h2
  · rw [Subgroup.card_map_of_injective S.Mbar.subtype_injective]
    exact hO3
  · intro x hx
    have h1 : (⟨x, hx⟩ : S.Mbar) * tX * (⟨x, hx⟩ : S.Mbar)⁻¹ ∈
        timmesfeldOddCore S.Mbar ⊔ zpowers tX := by
      have := normalClosure_normal.conj_mem tX
        (subset_normalClosure (Set.mem_singleton tX)) ⟨x, hx⟩
      rw [hUK] at this
      exact sup_le_sup_right hKO _ this
    have h2 := Subgroup.mem_map_of_mem S.Mbar.subtype h1
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h2
    simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
      map_mul, map_inv] using h2
  · refine sSup_le fun Z hZ => ?_
    obtain ⟨h, rfl, htZ⟩ := mem_Dset.mp hZ
    exact le_sSup ⟨S.ρ h, ⟨h, rfl⟩, Lbar_mul S h g, (Lbar_mul S h g) ▸ htZ⟩
  · rintro x ⟨h, rfl⟩ htZ
    rw [← Lbar_mul S h g] at htZ ⊢
    exact Lbar_mul_le_Rbar htZ
  · intro r hr n hn
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
    exact conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hr) hn

theorem Nbar_le_zpowers_of_corB (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (hn : 4 < S.width) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hN2 : IsPGroup 2 (Nbar S g t)) {X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hXR : X ≤ RmodN S g t) (hsimp : IsSimpleGroup X) (hnab : S5.NonabelianSylowTwo X)
    (h1p : IsPGroup 2 (closure (conjCentM S t)))
    (h1c : ⁅⁅closure (conjCentM S t), closure (conjCentM S t)⁆, closure (conjCentM S t)⁆ = ⊥)
    (h2 : ∀ τ ∈ conjCentM S t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t) :
    Nbar S g t ≤ zpowers t := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  set tX : S.Mbar := ⟨t, htM⟩ with htX
  have htXX : tX * tX = 1 := Subtype.ext htt
  have htX1 : tX ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have htXo : orderOf tX = 2 := orderOf_eq_prime (by rw [pow_two]; exact htXX) htX1
  have himage : S.Mbar.subtype '' conjCent tX = conjCentM S t := by
    ext τ
    constructor
    · rintro ⟨τ', ⟨hc, hconj⟩, rfl⟩
      obtain ⟨c, hc'⟩ := isConj_iff.mp hconj
      exact ⟨τ'.2, congrArg Subtype.val hc, c, c.2, by rw [← hc']; rfl⟩
    · rintro ⟨hτM, hτt, x, hxM, hxτ⟩
      exact ⟨⟨τ, hτM⟩, ⟨Subtype.ext hτt, isConj_iff.mpr ⟨⟨x, hxM⟩, Subtype.ext hxτ.symm⟩⟩, rfl⟩
  have hmapW : (closure (conjCent tX)).map S.Mbar.subtype = closure (conjCentM S t) := by
    rw [MonoidHom.map_closure, himage]
  have h1p' : IsPGroup 2 (closure (conjCent tX)) := by
    have := h1p.comap_of_injective S.Mbar.subtype S.Mbar.subtype_injective
    rwa [← hmapW, comap_map_eq_self_of_injective S.Mbar.subtype_injective] at this
  have h1c' : ⁅⁅closure (conjCent tX), closure (conjCent tX)⁆, closure (conjCent tX)⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ S.Mbar.subtype_injective).mp
    rw [map_commutator, map_commutator, hmapW]
    exact h1c
  have h2' : ∀ τ : S.Mbar, τ * tX = tX * τ → IsConj tX τ → τ ≠ tX → IsConj tX (tX * τ) := by
    intro τ hτt hconj hne
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hmem : (τ : S.O) ∈ conjCentM S t :=
      ⟨τ.2, congrArg Subtype.val hτt, c, c.2, by rw [← hc]; rfl⟩
    obtain ⟨y, hyM, hy⟩ := h2 τ hmem fun h => hne (Subtype.ext h)
    refine isConj_iff.mpr ⟨⟨y, hyM⟩ * c, Subtype.ext ?_⟩
    have hc' : (c : S.O) * t * (c : S.O)⁻¹ = τ := congrArg Subtype.val hc
    calc ((⟨y, hyM⟩ * c : S.Mbar) : S.O) * t * ((⟨y, hyM⟩ * c : S.Mbar) : S.O)⁻¹ =
        y * ((c : S.O) * t * (c : S.O)⁻¹) * y⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_mk]; group
      _ = (τ : S.O) * t := by rw [hc', hy]
      _ = t * τ := (congrArg Subtype.val hτt)
  obtain ⟨hO3, hEq, hF⟩ := S5.timmesfeld_5_5 hCE hIrr H hNo C (S45Q.hyp45Q H C) hn
  have hO2X : ∀ P : Subgroup S.Mbar, IsSubnormal P ⊤ → IsPGroup 2 P → P = ⊥ :=
    eq_bot_of_isSubnormal_top_Mbar
  rcases corB_trichotomy hCorB hFacts htXo h1p' h1c' h2' with ⟨K, hKN, hKodd, hUK⟩ | hab |
    ⟨hsimpU, hder, hsect⟩
  ·
    exact Nbar_le_zpowers_of_oddCore H ht ht1 hN2 hO3 hKN hKodd hUK
  ·
    exfalso
    have hU2 : IsPGroup 2 (normalClosure ({tX} : Set S.Mbar)) := fun u =>
      ⟨1, Subtype.ext (by
        rw [SubmonoidClass.coe_pow, Subgroup.coe_one, pow_one, pow_two]
        exact (hab u u.2 u u.2).2)⟩
    have hsub : IsSubnormal (normalClosure ({tX} : Set S.Mbar)) ⊤ :=
      IsSubnormal.step le_top ⟨fun n hn x => by
        rw [mem_subgroupOf] at hn ⊢
        exact normalClosure_normal.conj_mem _ hn _⟩ (IsSubnormal.refl ⊤)
    have hbot := hO2X _ hsub hU2
    have : tX ∈ normalClosure ({tX} : Set S.Mbar) := subset_normalClosure (Set.mem_singleton _)
    rw [hbot, Subgroup.mem_bot] at this
    exact htX1 this
  ·
    have hB : centralizer (timmesfeldFStar S.Mbar : Set S.Mbar) ≤ timmesfeldFStar S.Mbar :=
      CFSG.Adapters.centralizer_timmesfeldFStar_le _
    have hNn := normal_NbarX haQ (t := t) X
    have := hsimp
    exact (false_of_corB_list htXX htX1 hO2X hO3 hEq hF hB hsimpU hder hsect
      (R := (RbarX haQ t X).subgroupOf S.Mbar) (N := NbarM S g t)
      (fun r hr => mem_centralizer_singleton_iff.mpr
        (Subtype.ext (commute_of_mem_Rbar haQ (RbarX_le_Rbar haQ t X (mem_subgroupOf.mp hr)))))
      (fun n hn => Nbar_le_RbarX haQ X hn) (quotEquivX haQ t hXR).isSimpleGroup
      (exists_noncomm_of_nonabelianSylowTwo (quotEquivX haQ t hXR) hnab)).elim

theorem mem_and_comm_of_mem_closure {Y : Type*} [Group Y] {N : Subgroup Y} {t : Y}
    (htN : ∀ n ∈ N, n * t = t * n) {s : Set Y} (hsN : s ⊆ N)
    (hs : ∀ τ ∈ s, ∀ n ∈ N, n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t) {y : Y} (hy : y ∈ closure s) :
    y ∈ N ∧ ∀ n ∈ N, n * y * n⁻¹ * y⁻¹ ∈ zpowers t := by
  have hcen : ∀ x ∈ N, ∀ c ∈ zpowers t, x * c * x⁻¹ = c := by
    intro x hx c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rw [(Commute.zpow_right (htN x hx) k).eq, mul_inv_cancel_right]
  induction hy using closure_induction with
  | mem τ hτ => exact ⟨hsN hτ, hs τ hτ⟩
  | one =>
    refine ⟨one_mem _, fun n _ => ?_⟩
    rw [mul_one, mul_inv_cancel, inv_one, mul_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    refine ⟨mul_mem hx.1 hy.1, fun n hn => ?_⟩
    have e : n * (x * y) * n⁻¹ * (x * y)⁻¹ =
        (n * x * n⁻¹ * x⁻¹) * (x * (n * y * n⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e, hcen x hx.1 _ (hy.2 n hn)]
    exact mul_mem (hx.2 n hn) (hy.2 n hn)
  | inv x _ hx =>
    refine ⟨inv_mem hx.1, fun n hn => ?_⟩
    have e : n * x⁻¹ * n⁻¹ * x⁻¹⁻¹ = x⁻¹ * (n * x * n⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e, hcen x⁻¹ (inv_mem hx.1) _ (inv_mem (hx.2 n hn))]
    exact inv_mem (hx.2 n hn)

theorem commutator_commutator_closure_eq_bot {Y : Type*} [Group Y] {N : Subgroup Y} {t : Y}
    (htN : ∀ n ∈ N, n * t = t * n) {s : Set Y} (hsN : s ⊆ N)
    (hs : ∀ τ ∈ s, ∀ n ∈ N, n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t) :
    ⁅⁅closure s, closure s⁆, closure s⁆ = ⊥ := by
  have h1 : ⁅closure s, closure s⁆ ≤ zpowers t := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (mem_and_comm_of_mem_closure htN hsN hs hb).2 a
      (mem_and_comm_of_mem_closure htN hsN hs ha).1
  refine eq_bot_iff.mpr ((commutator_mono h1 le_rfl).trans (le_of_eq ?_))
  rw [commutator_eq_bot_iff_le_centralizer, zpowers_le, mem_centralizer_iff]
  intro w hw
  exact htN w (mem_and_comm_of_mem_closure htN hsN hs hw).1

theorem Nbar_le_zpowers_of_corB_of_subset (hCorB : TimmesfeldCorBInput)
    (hFacts : CorBListFacts) (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (hn : 4 < S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hN2 : IsPGroup 2 (Nbar S g t)) {X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hXR : X ≤ RmodN S g t) (hsimp : IsSimpleGroup X) (hnab : S5.NonabelianSylowTwo X)
    (hin : conjCentM S t ⊆ Nbar S g t)
    (hcomm : ∀ τ ∈ conjCentM S t, ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t)
    (h2 : ∀ τ ∈ conjCentM S t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t) :
    Nbar S g t ≤ zpowers t := by
  have htN : ∀ n ∈ Nbar S g t, n * t = t * n := fun n hn =>
    commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar hn)
  exact Nbar_le_zpowers_of_corB hCorB hFacts hCE hIrr H hNo C hn ht ht1 hN2 hXR hsimp hnab
    (hN2.to_le ((closure_le _).mpr hin)) (commutator_commutator_closure_eq_bot htN hin hcomm) h2

theorem false_of_corB (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (hn : 4 < S.width) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) (hN2 : IsPGroup 2 (Nbar S g t))
    {X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hXR : X ≤ RmodN S g t)
    (hsimp : IsSimpleGroup X) (hnab : S5.NonabelianSylowTwo X)
    (hin : conjCentM S t ⊆ Nbar S g t)
    (hcomm : ∀ τ ∈ conjCentM S t, ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t)
    (h2 : ∀ τ ∈ conjCentM S t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t) : False := by
  apply hA
  refine le_antisymm (inf_le_right.trans (Nbar_le_zpowers_of_corB_of_subset hCorB hFacts hCE hIrr
    H hNo C hn ht ht1 hN2 hXR hsimp hnab hin hcomm h2)) ?_
  rw [zpowers_le]
  exact ⟨ht, self_mem_Nbar H ht⟩

end CFSG.LargeExtraspecial.S8
