module

public import CFSG.GH74.GLS.C3.Layer1.Th2IV26Abs
public import CFSG.GH74.GLS.C3.Layer1.Th2P86
public import CFSG.GH74.GLS.C3.Layer1.Th2HYPump
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i
public import CFSG.GH74.GLS.C3.Layer1.EvenAltConfig
public import CFSG.GH74.GLS.C3.Layer1.EvenStd
public import CFSG.GH74.GLS.C3.Layer1.Th2L83Gen
public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.GLS.C3.Layer1.Th2P812
public import CFSG.GH74.GLS.C3.Layer1.Th2P812Rows
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def B_B2 : Prop := B_B2_g4

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.IV26

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Th2.P85
open scoped commutatorElement

section Conj

variable {X : Type} [Group X]

theorem isCompIn_map_conj' {H L : Subgroup X} (h : IsCompIn H L) (c : X) :
    IsCompIn (H.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨hLH, hcomp⟩ := h
  refine ⟨Subgroup.map_mono hLH, ?_⟩
  let e : ↥H ≃* ↥(H.map (MulAut.conj c).toMonoidHom) := (MulAut.conj c).subgroupMap H
  have hmap : (L.subgroupOf H).map e.toMonoidHom =
      (L.map (MulAut.conj c).toMonoidHom).subgroupOf (H.map (MulAut.conj c).toMonoidHom) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_subgroupOf.mp hz
      have hkH : k ∈ H := hLH hk
      exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
  have := CFSG.LocalCores.isComponent_map_mulEquiv e hcomp
  rwa [hmap] at this

theorem isCompIn_conj_fixed {K : Subgroup X} {w : X} (c : X) (hc : ∀ k ∈ K, c * k = k * c)
    (h : IsCompIn (centralizer ({w} : Set X)) K) :
    IsCompIn (centralizer ({c * w * c⁻¹} : Set X)) K := by
  have h1 := isCompIn_map_conj' h c
  rw [Stage1.Thm2.Recip.map_centralizer_singleton_conj] at h1
  have hK : K.map (MulAut.conj c).toMonoidHom = K := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : c * k * c⁻¹ = k := by rw [hc k hk]; group
      simpa [MulAut.conj_apply, this] using hk
    · intro hy
      refine ⟨y, hy, ?_⟩
      have : c * y * c⁻¹ = y := by rw [hc y hy]; group
      simpa [MulAut.conj_apply] using this
  rwa [hK] at h1

end Conj

section Transport

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

abbrev eb (M : Subgroup G) {e : G} (he : e ∈ M) : Mb M := barMk ↥M ⟨e, he⟩

theorem exists_subnormal_transport {e : G} (heM : e ∈ M) (he2 : orderOf e = 2)
    {W : Subgroup ↥(centralizer ({e} : Set G))} (hW : W.IsSubnormal) :
    ∃ Z : Subgroup ↥(centralizer ({eb M heM} : Set (Mb M))), Z.IsSubnormal ∧
      ∀ d : ↥(centralizer ({eb M heM} : Set (Mb M))), d ∈ Z ↔
        ∃ (g : G) (hg : g ∈ centralizer ({e} : Set G)) (hgM : g ∈ M),
          (⟨g, hg⟩ : ↥(centralizer ({e} : Set G))) ∈ W ∧ barMk ↥M ⟨g, hgM⟩ = (d : Mb M) := by
  have hso : orderOf (⟨e, heM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk e heM).trans he2
  have hψ := barMkCentralizer_surjective hso
  let ι : ↥(centralizer ({(⟨e, heM⟩ : ↥M)} : Set ↥M)) →* ↥(centralizer ({e} : Set G)) :=
    { toFun := fun c => ⟨(c : ↥M).1, by
        have h := c.2
        rw [mem_centralizer_singleton_iff] at h ⊢
        exact congrArg Subtype.val h⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  refine ⟨(W.comap ι).map (barMkCentralizer hso), (hW.comap ι).map hψ, fun d => ?_⟩
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : ↥M).1, (ι c).2, (c : ↥M).2, hc, (barMkCentralizer_apply hso c).symm⟩
  · rintro ⟨g, hg, hgM, hgW, hd⟩
    have hc : (⟨g, hgM⟩ : ↥M) ∈ centralizer ({(⟨e, heM⟩ : ↥M)} : Set ↥M) := by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 hg)
    refine ⟨⟨⟨g, hgM⟩, hc⟩, hgW, Subtype.ext ?_⟩
    rw [barMkCentralizer_apply hso]
    exact hd

end Transport

section B2

variable {X : Type} [Group X] [Finite X]

theorem isComponent_of_B2 (hB2 : B_B2) (hg : Gen4 X) (hX : IsKGroupNative X)
    (hcore : pPrimeCore 2 X = ⊥) {y : X} (hy : orderOf y = 2) :
    ∀ J : Subgroup ↥(centralizer ({y} : Set X)), IsPComponent 2 J → IsComponent J := by
  intro J hJ
  have hKJ : (J.map (centralizer ({y} : Set X)).subtype).subgroupOf (centralizer ({y} : Set X)) = J :=
    Subgroup.comap_map_eq_self_of_injective (centralizer ({y} : Set X)).subtype_injective J
  have h1 : IsPCompIn 2 (centralizer ({y} : Set X)) (J.map (centralizer ({y} : Set X)).subtype) :=
    ⟨Subgroup.map_subtype_le J, by rw [hKJ]; exact hJ⟩
  have h2 := hB2 X hg hX hcore y hy _ h1
  have := h2.2
  rwa [hKJ] at this

theorem lBalanceIsKGroup_of_isKGroupNative
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Blueprint.Catalog CFSG.Assembly.InCatalog)
    {X : Type} [Group X] [Finite X] (hX : CFSG.GH74.GLS.IsKGroupNative X) :
    CFSG.Open.lBalanceIsKGroup X :=
  CFSG.KCore.KGroupNonab.mono_of_finite hbridge
    (CFSG.KCore.KGroupAllSimple.kGroupNonab hX)

theorem gen4_Mb {G : Type} [Group G] [Finite G] (hg : Gen4 G) (M : Subgroup G) : Gen4 (Mb M) :=
  Gen4.quotient (pPrimeCore 2 ↥M) (Gen4.subgroup M hg)

end B2

section StepOne

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
theorem isPerfect_imgM {K : Subgroup G} (hKM : K ≤ M) (hKperf : ⁅K, K⁆ = K) :
    ⁅imgM M K, imgM M K⁆ = imgM M K := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
  have : Group.IsPerfect ↥(imgM M K) :=
    Group.IsPerfect.ofSurjective (f := toImgM hKM) (toImgM_surjective hKM)
  exact Subgroup.isPerfect_iff.mp this

theorem imgM_ne_bot {X K : Subgroup G} (hKM : K ≤ M) (hKc : IsPCompIn 2 X K) : imgM M K ≠ ⊥ := by
  intro hbot
  obtain ⟨e⟩ := kBar_equiv_imgM hKM
  have hq := CFSG.LocalCores.isQuasisimple_nontrivial (TwoThin.isQuasisimple_hat hKc)
  have hsub : Subsingleton (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) := by
    have : Subsingleton ↥(imgM M K) := by
      rw [hbot]
      infer_instance
    infer_instance
  have := e.symm.injective.subsingleton
  exact (not_subsingleton _) this

end StepOne

section StepOne2

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem isCompIn_imgM_at_x {x : G} {K : Subgroup G} (hxM : x ∈ M) (hx2 : orderOf x = 2)
    (hKM : K ≤ M) (hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hB : ∀ J : Subgroup ↥(centralizer ({eb M hxM} : Set (Mb M))), IsPComponent 2 J → IsComponent J) :
    IsCompIn (centralizer ({eb M hxM} : Set (Mb M))) (imgM M K) := by
  set C : Subgroup (Mb M) := centralizer ({eb M hxM} : Set (Mb M)) with hC
  have hKC : K ≤ centralizer ({x} : Set G) := hKc.1
  have hKC' : imgM M K ≤ C := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hw
    rw [hC, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hKC hm))
  have hsubW : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal := by
    obtain ⟨_, _, hsub, _, _⟩ := hKc.2
    exact hsub
  obtain ⟨Z, hZsub, hZmem⟩ := exists_subnormal_transport hxM hx2 hsubW
  have hZeq : Z = (imgM M K).subgroupOf C := by
    ext d
    rw [hZmem d, Subgroup.mem_subgroupOf, mem_imgM_iff]
    constructor
    · rintro ⟨g, hg, hgM, hgW, hd⟩
      exact ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mp hgW, hd⟩
    · rintro ⟨m, hm, hd⟩
      exact ⟨(m : G), hKC hm, m.2, Subgroup.mem_subgroupOf.mpr hm, hd⟩
  have hKperf : ⁅K, K⁆ = K :=
    commutator_self_of_isTwoComponent (isPCompIn_two_iff.1 hKc).1 (isPCompIn_two_iff.1 hKc).2
  have hperf : ⁅(imgM M K).subgroupOf C, (imgM M K).subgroupOf C⁆ = (imgM M K).subgroupOf C := by
    have h1 : Group.IsPerfect ↥(imgM M K) := Subgroup.isPerfect_iff.mpr (isPerfect_imgM hKM hKperf)
    have h2 : Group.IsPerfect ↥((imgM M K).subgroupOf C) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC').symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKC').symm.surjective
    exact Subgroup.isPerfect_iff.mp h2
  let g : ↥K →* ↥C := (Subgroup.inclusion hKC').comp (toImgM hKM)
  have hgrange : g.range = (imgM M K).subgroupOf C := by
    ext d
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (toImgM hKM k).2
    · intro hd
      obtain ⟨m, hm, hmd⟩ := mem_imgM_iff.1 (Subgroup.mem_subgroupOf.mp hd)
      exact ⟨⟨(m : G), hm⟩, Subtype.ext hmd⟩
  have hne : (imgM M K).subgroupOf C ≠ ⊥ := by
    intro hbot
    apply imgM_ne_bot hKM hKc
    rw [eq_bot_iff]
    intro w hw
    have h1 : (⟨w, hKC' hw⟩ : ↥C) ∈ (imgM M K).subgroupOf C := hw
    rw [hbot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hKq : IsQuasisimple ↥(((imgM M K).subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C))) := by
    have := isQuasisimple_map_of_hat (TwoThin.isQuasisimple_hat hKc) g (by rw [hgrange, ← hZeq]; exact hZsub)
      (by rw [hgrange]; exact hperf) (by rw [hgrange]; exact hne)
    rwa [hgrange] at this
  have hcomp : IsComponent ((imgM M K).subgroupOf C) :=
    isComponent_of_sandwich hB hperf (hZeq ▸ hZsub) le_rfl bot_le
      (fun z hz => ⟨z, hz, 1, Subgroup.one_mem _, (mul_one z).symm⟩) hKq
  exact ⟨hKC', hcomp⟩

end StepOne2

section KLam

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem imgM_eq_of_cover {K Λ : Subgroup G} (hKM : K ≤ M) (hΛK : Λ ≤ K)
    (hcover : ∀ k ∈ K, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o)
    (hKq : IsQuasisimple ↥(imgM M K)) : imgM M Λ = imgM M K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (imgM_mono hΛK) ?_
  set Kb : Subgroup (Mb M) := imgM M K with hKb
  set Nb : Subgroup (Mb M) := imgM M (pPrimeCoreOf 2 K) with hNb
  have hNK : Nb ≤ Kb := imgM_mono (TwoThin.pPrimeCoreOf_le K)
  have hNcent : ∀ n ∈ Nb, ∀ k ∈ Kb, n * k = k * n := by
    have hnorm : (Nb.subgroupOf Kb).Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨o, ho, hon⟩ := mem_imgM_iff.1 hn
      obtain ⟨k₀, hk₀, hk₀k⟩ := mem_imgM_iff.1 k.2
      have hk₀' : (k₀ : G) * o * (k₀ : G)⁻¹ ∈ pPrimeCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.1
          (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hk₀)) o).1 ho
      refine mem_imgM_iff.2 ⟨k₀ * ⟨o, hKM (TwoThin.pPrimeCoreOf_le K ho)⟩ * k₀⁻¹, ?_, ?_⟩
      · simpa using hk₀'
      · simp only [map_mul, map_inv, hon, hk₀k]
        rfl
    have hodd : Odd (Nat.card (Nb.subgroupOf Kb)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
      have h1 : Nat.card Nb ∣ Nat.card ((pPrimeCoreOf 2 K).subgroupOf M) := Subgroup.card_map_dvd _ _
      have h2 : Nat.card ((pPrimeCoreOf 2 K).subgroupOf M) = Nat.card (pPrimeCoreOf 2 K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((TwoThin.pPrimeCoreOf_le K).trans hKM)).toEquiv
      rw [h2] at h1
      exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) h1
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hnorm with htop | hcen
    · exfalso
      have hcard : Nat.card (Nb.subgroupOf Kb) = Nat.card ↥Kb := by
        rw [htop, Subgroup.card_top]
      rw [hcard] at hodd
      have hsolv : Group.IsSolvable ↥Kb := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      have : Nontrivial ↥Kb := CFSG.LocalCores.isQuasisimple_nontrivial hKq
      have : Group.IsPerfect ↥Kb := hKq.1
      exact Group.IsPerfect.not_isSolvable ↥Kb hsolv
    · intro n hn k hk
      have := Subgroup.mem_center_iff.1 (hcen (Subgroup.mem_subgroupOf.mpr hn : (⟨n, hNK hn⟩ : ↥Kb) ∈ Nb.subgroupOf Kb))
        ⟨k, hk⟩
      exact (congrArg Subtype.val this).symm
  have hKperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.mp hKq.1
  rw [← hKperf, Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a₀, ha₀, rfl⟩ := mem_imgM_iff.1 ha
  obtain ⟨b₀, hb₀, rfl⟩ := mem_imgM_iff.1 hb
  obtain ⟨l, hl, o, ho, ha₀eq⟩ := hcover _ ha₀
  obtain ⟨l', hl', o', ho', hb₀eq⟩ := hcover _ hb₀
  have hlM : l ∈ M := hKM (hΛK hl)
  have hl'M : l' ∈ M := hKM (hΛK hl')
  have hoM : o ∈ M := hKM (TwoThin.pPrimeCoreOf_le K ho)
  have ho'M : o' ∈ M := hKM (TwoThin.pPrimeCoreOf_le K ho')
  have ha₀' : a₀ = ⟨l, hlM⟩ * ⟨o, hoM⟩ := Subtype.ext ha₀eq
  have hb₀' : b₀ = ⟨l', hl'M⟩ * ⟨o', ho'M⟩ := Subtype.ext hb₀eq
  have hoN : barMk ↥M ⟨o, hoM⟩ ∈ Nb := mem_imgM_iff.2 ⟨⟨o, hoM⟩, ho, rfl⟩
  have ho'N : barMk ↥M ⟨o', ho'M⟩ ∈ Nb := mem_imgM_iff.2 ⟨⟨o', ho'M⟩, ho', rfl⟩
  have hlK : barMk ↥M ⟨l, hlM⟩ ∈ Kb := mem_imgM_iff.2 ⟨⟨l, hlM⟩, hΛK hl, rfl⟩
  have hl'K : barMk ↥M ⟨l', hl'M⟩ ∈ Kb := mem_imgM_iff.2 ⟨⟨l', hl'M⟩, hΛK hl', rfl⟩
  have e := commutator_mul_commuting (a := barMk ↥M ⟨l, hlM⟩) (b := barMk ↥M ⟨l', hl'M⟩)
    (r := barMk ↥M ⟨o, hoM⟩) (s := barMk ↥M ⟨o', ho'M⟩)
    (hNcent _ hoN _ hl'K) (hNcent _ hoN _ (hNK ho'N)) (hNcent _ ho'N _ hlK)
  rw [ha₀', hb₀', map_mul, map_mul, e, ← map_commutatorElement]
  refine mem_imgM_iff.2 ⟨⁅(⟨l, hlM⟩ : ↥M), ⟨l', hl'M⟩⁆, ?_, rfl⟩
  have : ((⁅(⟨l, hlM⟩ : ↥M), ⟨l', hl'M⟩⁆ : ↥M) : G) = ⁅l, l'⁆ := by
    simp [commutatorElement_def]
  rw [this, commutatorElement_def]
  exact Λ.mul_mem (Λ.mul_mem (Λ.mul_mem hl hl') (Λ.inv_mem hl)) (Λ.inv_mem hl')

end KLam

section StepThree

open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.Th2.HY

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem isCompIn_imgM_at_e_onePump
    {x : G} {K : Subgroup G}
    (hKM : K ≤ M) (hKq : IsQuasisimple ↥(imgM M K))
    {e : G} (heM : e ∈ M)
    {I : Subgroup G} (hpump : PumpUpLT 2 x K e I)
    (htriv : x ∈ normalizer (I : Set G) ∧ Nonempty (kBar I ≃* kBar K))
    (hB : ∀ J : Subgroup ↥(centralizer ({eb M heM} : Set (Mb M))), IsPComponent 2 J → IsComponent J) :
    IsCompIn (centralizer ({eb M heM} : Set (Mb M))) (imgM M K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hpump.1.2.2
  have he2 : orderOf e = 2 := hpump.2.1.1
  obtain ⟨Λ, hΛ⟩ := exists_isLam he2 hKc hpump.2.2.2.1
  obtain ⟨e₁⟩ := htriv.2
  have hIc : IsPCompIn 2 (centralizer ({e} : Set G)) I := hpump.2.1.2.2
  have hΛI : bar e Λ ≤ bar e I := bar_le_of_stable hpump hΛ htriv.1
  have hΛeq : bar e Λ = bar e I := bar_lam_eq hΛ hIc hΛI e₁
  have hcomp : IsComponent (bar e Λ) := hΛeq ▸ isComponent_bar hIc
  have hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
  have hΛC : Λ ≤ centralizer ({e} : Set G) := hΛ.le.trans inf_le_right
  set W : Subgroup ↥(centralizer ({e} : Set G)) :=
    (bar e Λ).comap (barMk ↥(centralizer ({e} : Set G))) with hW
  have hWsub : W.IsSubnormal := hcomp.2.comap _
  have hWmem : ∀ (g : G) (hg : g ∈ centralizer ({e} : Set G)),
      (⟨g, hg⟩ : ↥(centralizer ({e} : Set G))) ∈ W ↔
        ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({e} : Set G)), g = l * o := by
    intro g hg
    rw [hW, Subgroup.mem_comap]
    show sbar g hg ∈ bar e Λ ↔ _
    rw [sbar_mem_bar_iff hg hΛC]
    exact mem_sup_iff_mul_of_le_normalizer (le_normalizer_O hΛC)
  set D : Subgroup (Mb M) := centralizer ({eb M heM} : Set (Mb M)) with hD
  set Oe : Subgroup G := pPrimeCoreOf 2 (centralizer ({e} : Set G)) with hOe
  obtain ⟨Z, hZsub, hZmem⟩ := exists_subnormal_transport heM he2 hWsub
  have hΛb : imgM M Λ = imgM M K := imgM_eq_of_cover hKM hΛK hΛ.cover hKq
  have hΛcentEb : imgM M Λ ≤ Subgroup.centralizer ({eb M heM} : Set (Mb M)) := by
    intro w hw
    obtain ⟨m, hmΛ, rfl⟩ := mem_imgM_iff.1 hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    change barMk ↥M m * barMk ↥M ⟨e, heM⟩ =
      barMk ↥M ⟨e, heM⟩ * barMk ↥M m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hΛC hmΛ))
  have hecent : eb M heM ∈
      Subgroup.centralizer ((imgM M K : Subgroup (Mb M)) : Set (Mb M)) := by
    have h : imgM M K ≤ Subgroup.centralizer ({eb M heM} : Set (Mb M)) := by
      simpa [hΛb] using hΛcentEb
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (h hw)
  have hKbD : imgM M K ≤ D := by
    intro k hk
    rw [hD, mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hecent k hk
  have hOeC : Oe ≤ centralizer ({e} : Set G) := TwoThin.pPrimeCoreOf_le _
  have hObD : imgM M Oe ≤ D := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hw
    rw [hD, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hOeC hm))
  set K' : Subgroup ↥D := (imgM M K).subgroupOf D with hK'
  set R' : Subgroup ↥D := (imgM M Oe).subgroupOf D with hR'
  have hK'Z : K' ≤ Z := by
    intro d hd
    have hd' : (d : Mb M) ∈ imgM M K := hd
    rw [← hΛb] at hd'
    obtain ⟨l, hl, hld⟩ := mem_imgM_iff.1 hd'
    exact (hZmem d).2 ⟨(l : G), hΛC hl, l.2, (hWmem _ _).2 ⟨l, hl, 1, Subgroup.one_mem _, (mul_one _).symm⟩, hld⟩
  have hZKR : ∀ z ∈ Z, ∃ k ∈ K', ∃ r ∈ R', z = k * r := by
    intro z hz
    obtain ⟨g, hg, hgM, hgW, hzd⟩ := (hZmem z).1 hz
    obtain ⟨l, hl, o, ho, hgeq⟩ := (hWmem g hg).1 hgW
    have hlM : l ∈ M := hKM (hΛK hl)
    have hoM : o ∈ M := by
      have : o = l⁻¹ * g := by rw [hgeq]; group
      rw [this]
      exact M.mul_mem (M.inv_mem hlM) hgM
    have hlb : barMk ↥M ⟨l, hlM⟩ ∈ imgM M K := mem_imgM_iff.2 ⟨⟨l, hlM⟩, hΛK hl, rfl⟩
    have hob : barMk ↥M ⟨o, hoM⟩ ∈ imgM M Oe := mem_imgM_iff.2 ⟨⟨o, hoM⟩, ho, rfl⟩
    refine ⟨⟨barMk ↥M ⟨l, hlM⟩, hKbD hlb⟩, hlb, ⟨barMk ↥M ⟨o, hoM⟩, hObD hob⟩, hob, ?_⟩
    apply Subtype.ext
    rw [← hzd]
    have : (⟨g, hgM⟩ : ↥M) = ⟨l, hlM⟩ * ⟨o, hoM⟩ := Subtype.ext hgeq
    rw [this, map_mul]
    rfl
  have hso : orderOf (⟨e, heM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk e heM).trans he2
  have hRnorm : R'.Normal := by
    refine ⟨fun r hr d => ?_⟩
    rw [hR', Subgroup.mem_subgroupOf] at hr ⊢
    obtain ⟨o, hoO, hor⟩ := mem_imgM_iff.1 hr
    obtain ⟨c, hcd⟩ := barMkCentralizer_surjective hso d
    have hcG : ((c : ↥M) : G) ∈ centralizer ({e} : Set G) := by
      have h := c.2
      rw [mem_centralizer_singleton_iff] at h ⊢
      exact congrArg Subtype.val h
    have hcdv : (d : Mb M) = barMk ↥M (c : ↥M) := by
      rw [← hcd]
      exact barMkCentralizer_apply hso c
    have hmem : ((c : ↥M) * o * (c : ↥M)⁻¹ : ↥M).1 ∈ Oe := by
      have := TwoThin.pPrimeCoreOf_normalized (centralizer ({e} : Set G)) hcG hoO
      simpa using this
    refine mem_imgM_iff.2 ⟨(c : ↥M) * o * (c : ↥M)⁻¹, hmem, ?_⟩
    show barMk ↥M ((c : ↥M) * o * (c : ↥M)⁻¹) = (d : Mb M) * (r : Mb M) * (d : Mb M)⁻¹
    rw [map_mul, map_mul, map_inv, hor, hcdv]
  have hRodd : Odd (Nat.card R') := by
    rw [hR', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hObD).toEquiv]
    have h1 : Nat.card (imgM M Oe) ∣ Nat.card (Oe.subgroupOf M) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (Oe.subgroupOf M) ∣ Nat.card Oe := by
      have h3 : Nat.card (Oe.subgroupOf M) = Nat.card ((Oe.subgroupOf M).map M.subtype) :=
        (Subgroup.card_map_of_injective M.subtype_injective).symm
      rw [h3]
      exact Subgroup.card_dvd_of_le (by rintro _ ⟨m, hm, rfl⟩; exact hm)
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) (h1.trans h2)
  have hR : R' ≤ pPrimeCore 2 ↥D := le_sSup ⟨hRnorm, Nat.coprime_two_left.2 hRodd⟩
  have hKperf : ⁅K, K⁆ = K :=
    commutator_self_of_isTwoComponent (isPCompIn_two_iff.1 hKc).1 (isPCompIn_two_iff.1 hKc).2
  have hK'perf : ⁅K', K'⁆ = K' := by
    have h1 : Group.IsPerfect ↥(imgM M K) := Subgroup.isPerfect_iff.mpr (isPerfect_imgM hKM hKperf)
    have h2 : Group.IsPerfect ↥K' :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKbD).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKbD).symm.surjective
    exact Subgroup.isPerfect_iff.mp h2
  have hK'q : IsQuasisimple ↥K' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKbD).symm hKq
  have hKq' := isQuasisimple_map_of_isQuasisimple hK'q
  have hcompK' : IsComponent K' := isComponent_of_sandwich hB hK'perf hZsub hK'Z hR hZKR hKq'
  exact ⟨hKbD, hcompK'⟩

theorem isCompIn_imgM_at_e {x y : G} {K T S : Subgroup G} (hstd : Th2Std x y K T S)
    (hKM : K ≤ M) (hKq : IsQuasisimple ↥(imgM M K))
    {e : G} (heT : e ∈ T ⊓ CxK x K) (he2 : orderOf e = 2) (heM : e ∈ M)
    (hecent : eb M heM ∈ centralizer ((imgM M K : Subgroup (Mb M)) : Set (Mb M)))
    (hR3e : 3 ≤ pRank 2 ↥(centralizer ({e} : Set G)))
    (hB : ∀ J : Subgroup ↥(centralizer ({eb M heM} : Set (Mb M))), IsPComponent 2 J → IsComponent J) :
    IsCompIn (centralizer ({eb M heM} : Set (Mb M))) (imgM M K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hterm : IsTwoTerminal x K := hstd.v2ss.isV2Triple.2.1
  have heCxK : e ∈ CxK x K := heT.2
  obtain ⟨M₁, hlt⟩ := TwoThin.exists_pumpup_of_involution
      hstd.orderOf_x he2 hstd.comp heCxK.1 heCxK.2 hterm.1 hR3e
  obtain ⟨hxM₁, ⟨e₁⟩⟩ := hterm.2.1 e M₁ hlt
  exact isCompIn_imgM_at_e_onePump hKM hKq heM hlt ⟨hxM₁, ⟨e₁⟩⟩ hB
end StepThree

section Main

theorem isTerminalSub_of_Q {X : Type} [Group X] [Finite X] {Kb Qb : Subgroup X}
    (hQ : IsSylowOf 2 Qb (centralizer (Kb : Set X)))
    (h : ∀ ε ∈ Qb, orderOf ε = 2 → IsCompIn (centralizer ({ε} : Set X)) Kb) :
    IsTerminalSub Kb := by
  intro z hz2 hzK
  have hzC : z ∈ centralizer (Kb : Set X) :=
    Subgroup.mem_centralizer_iff.2 (fun k hk => (hzK k hk).symm)
  obtain ⟨c, hc, hcQ⟩ := EvenCore.exists_conj_mem_Q hQ hzC hz2
  have hord : orderOf (c⁻¹ * z * c) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) z
    simpa [MulAut.conj_apply] using this.trans hz2
  have hcK : ∀ k ∈ Kb, c * k = k * c := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 hc k hk).symm
  have := isCompIn_conj_fixed c hcK (h _ hcQ hord)
  rwa [show c * (c⁻¹ * z * c) * c⁻¹ = z by group] at this

variable {G : Type} [Group G] [Finite G]

theorem isTerminalSub_imgM_of_local {x y : G} {K T S M : Subgroup G}
    (hstd : Th2Std x y K T S) (hKM : K ≤ M)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    (hR3 : ∀ e ∈ T ⊓ CxK x K, orderOf e = 2 →
      3 ≤ pRank 2 ↥(centralizer ({e} : Set G)))
    (hB : ∀ ε : Mb M, orderOf ε = 2 →
      ∀ J : Subgroup ↥(centralizer ({ε} : Set (Mb M))), IsPComponent 2 J → IsComponent J) :
    IsTerminalSub (imgM M K) := by
  have hQM : T ⊓ CxK x K ≤ M := hQ.le.trans inf_le_left
  have hxM : x ∈ M := hQM ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  have hBx := hB (eb M hxM)
    (show orderOf (eb M hxM) = 2 from
      orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2))
  have hxcomp := isCompIn_imgM_at_x hxM hx2 hKM hstd.comp hBx
  have hKq : IsQuasisimple ↥(imgM M K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hxcomp.1)
      hxcomp.2.1
  have hQ2 : IsPGroup 2 ↥(T ⊓ CxK x K) := hstd.T_pGroup.to_le inf_le_left
  refine isTerminalSub_of_Q (isSylowOf_imgM_cmbar hKM hQ) ?_
  intro ε hε hε2
  obtain ⟨m, hmQ, rfl⟩ := mem_imgM_iff.1 hε
  have hmQ' : (m : G) ∈ T ⊓ CxK x K := hmQ
  have heM : (m : G) ∈ M := m.2
  have hm2 : orderOf (m : G) = 2 := by
    have h1 : barMk ↥M m * barMk ↥M m = 1 := by
      have := pow_orderOf_eq_one (barMk ↥M m)
      rwa [hε2, sq] at this
    have hsq : (m : G) * (m : G) ∈ pPrimeCoreOf 2 M :=
      (barMk_eq_one_iff_mem_pPrimeCoreOf (M := M) (m * m)).1 (by rw [map_mul]; exact h1)
    have hsq1 : (m : G) * (m : G) = 1 := by
      have hmem : (m : G) * (m : G) ∈ (T ⊓ CxK x K) ⊓ pPrimeCoreOf 2 M :=
        ⟨(T ⊓ CxK x K).mul_mem hmQ' hmQ', hsq⟩
      rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot M hQ2, Subgroup.mem_bot] at hmem
      exact hmem
    refine orderOf_eq_prime (by rw [sq]; exact hsq1) ?_
    intro h1
    have : m = 1 := Subtype.ext h1
    rw [this, map_one, orderOf_one] at hε2
    omega
  have hecent : eb M heM ∈ centralizer ((imgM M K : Subgroup (Mb M)) : Set (Mb M)) := by
    rw [← imgM_cmbar_eq hKM]
    exact mem_imgM_iff.2 ⟨m, hQ.le hmQ, rfl⟩
  have hε2' : orderOf (eb M heM) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk (m : G) heM).trans hm2)
  exact isCompIn_imgM_at_e hstd hKM hKq hmQ' hm2 heM hecent (hR3 _ hmQ' hm2)
    (hB _ hε2')

theorem isTerminalSub_imgM_of_B2 (hB2 : B_B2) (hG : C3Hyp G) {x y : G} {K T S M : Subgroup G}
    (hchoice : Th2Choice x y K T S M) (hKM : K ≤ M)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K)) : IsTerminalSub (imgM M K) := by
  have hstd := hchoice.std
  have hMtop : M ≠ ⊤ := hchoice.maximal.1
  have hMb : IsKGroupNative (Mb M) := isKGroupNative_Mb hG.kproper hMtop
  have hcore : pPrimeCore 2 (Mb M) = ⊥ := pPrimeCore_Mb_eq_bot M
  have hB : ∀ ε : Mb M, orderOf ε = 2 →
      ∀ J : Subgroup ↥(centralizer ({ε} : Set (Mb M))), IsPComponent 2 J → IsComponent J :=
    fun ε hε => isComponent_of_B2 hB2 (gen4_Mb hG.gen4 M) hMb hcore (y := ε) hε
  have hR3 : ∀ e ∈ T ⊓ CxK x K, orderOf e = 2 →
      3 ≤ pRank 2 ↥(centralizer ({e} : Set G)) := by
    intro e _ he2
    exact TwoThin.rankThreeCentralizers G hG.kproper.1 hG.kproper.2.1
      (by have := hG.pRank_eq_four; omega) e he2
  exact isTerminalSub_imgM_of_local hstd hKM hQ hR3 hB

end Main

end CFSG.GH74.GLS.Th2.IV26
