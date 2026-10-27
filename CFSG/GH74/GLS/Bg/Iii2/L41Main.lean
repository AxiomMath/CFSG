module

public import CFSG.GH74.GLS.Bg.Iii2.L41Basic
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Bg.Iii2.L41

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPerfect_subgroupOf {Θ Y' : Subgroup G} (hΘ : ⁅Θ, Θ⁆ = Θ) (hΘY : Θ ≤ Y') :
    Group.IsPerfect ↥(Θ.subgroupOf Y') := by
  refine Subgroup.isPerfect_iff.mpr ?_
  apply Subgroup.map_injective Y'.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hΘY, hΘ]

omit [Finite G] in
theorem false_of_cover_le_cSec {Λ L : Subgroup G} (hΛL : Λ ≤ L)
    (hcov : ∀ k ∈ L, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 L, k = l * o)
    (hq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    (h : Λ ≤ centralizerSection L (pPrimeCoreOf 2 L)) : False := by
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple' hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  obtain ⟨l, hl, o, ho, hbo⟩ := hcov (b' : G) b'.2
  have hlL : l ∈ L := hΛL hl
  have hal : ⁅(a' : G), l⁆ ∈ pPrimeCoreOf 2 L := (h hl).2.2 a' a'.2
  have hao : ⁅(a' : G), o⁆ ∈ pPrimeCoreOf 2 L := by
    have : ⁅(a' : G), o⁆ = ((a' : G) * o * (a' : G)⁻¹) * o⁻¹ := by
      simp only [commutatorElement_def]
    rw [this]
    exact mul_mem (pPrimeCoreOf_normalized L a'.2 ho) (inv_mem ho)
  have e2 : ⁅(a' : G), l * o⁆ = ⁅(a' : G), l⁆ * (l * ⁅(a' : G), o⁆ * l⁻¹) := by
    simp only [commutatorElement_def]; group
  have hcomm : ⁅(a' : G), (b' : G)⁆ ∈ pPrimeCoreOf 2 L := by
    rw [hbo, e2]
    exact mul_mem hal (pPrimeCoreOf_normalized L hlL hao)
  have hkL : ⁅(a' : G), (b' : G)⁆ ∈ L := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem a'.2 b'.2) (inv_mem a'.2)) (inv_mem b'.2)
  have h1 : hatMap (le_refl L) ⟨⁅(a' : G), (b' : G)⁆, hkL⟩ = 1 :=
    (hatMap_eq_one_iff (le_refl L) _).mpr hcomm
  have h2 : (⟨⁅(a' : G), (b' : G)⁆, hkL⟩ : ↥L) = ⁅a', b'⁆ := rfl
  rw [h2] at h1
  have h3 : hatMap (le_refl L) ⁅a', b'⁆ = ⁅(QuotientGroup.mk a' : ↥L ⧸ pPrimeCore 2 ↥L), QuotientGroup.mk b'⁆ := by
    exact map_commutatorElement (hatMap (le_refl L)) a' b'
  rw [h3] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1)


theorem trivial_pumpup_data {x z : G} {K L : Subgroup G} (hlt : PumpUpLT 2 x K z L)
    (hxN : x ∈ normalizer (L : Set G)) (hle : hatCard L ≤ hatCard K) :
    ∃ Λ : Subgroup G, IsLam x z K Λ ∧ bar z Λ = bar z L ∧ Λ ≤ L := by
  have hxY : x ∈ centralizer ({z} : Set G) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ, hLc, -, -, -, hcases⟩ := rigid_step hlt hxY hle
  have hbar : bar z Λ = bar z L := (hcases.resolve_right (fun h => h.1 hxN)).2
  refine ⟨Λ, hΛ, hbar, ?_⟩
  have hperf : Group.IsPerfect ↥(Λ.subgroupOf (centralizer ({z} : Set G))) :=
    Subgroup.isPerfect_iff.mpr (lam_perfect_Y hΛ)
  have hM2 : TwoComponents.IsTwoComponent (L.subgroupOf (centralizer ({z} : Set G))) :=
    (isPCompIn_two_iff.mp hLc).2
  intro a ha
  have haY : a ∈ centralizer ({z} : Set G) := (Subgroup.mem_inf.mp (hΛ.le ha)).2
  have := le_of_perfect_map_le hperf hM2 hbar.le
    (Subgroup.mem_subgroupOf.mpr ha : (⟨a, haY⟩ : ↥(centralizer ({z} : Set G))) ∈ _)
  exact Subgroup.mem_subgroupOf.mp this

theorem T1_of_terminal {x z : G} {K L : Subgroup G} (hterm : IsTwoTerminal x K)
    (hlt : PumpUpLT 2 x K z L) {Q : Subgroup G} (hQ : IsSylowOf 2 Q (CxK x K))
    (hzc : ∀ q ∈ Q, z * q = q * z) (hQL : IsSylowOf 2 Q (CxK z L)) (hzL : z ∈ L)
    (hzK : z ∈ K) (Λz : Subgroup G) (hΛz : IsLam x z K Λz) (hΛzL : Λz ≤ L) : T1 z L := by
  have hx2 : orderOf x = 2 := hterm.1.1
  have hz2 : orderOf z = 2 := hlt.2.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hterm.1.2.2
  have hLc : IsPCompIn 2 (centralizer ({z} : Set G)) L := hlt.2.1.2.2
  obtain ⟨-, ⟨eLK⟩⟩ := hterm.2.1 z L hlt
  have hΛzK : Λz ≤ K := hΛz.le.trans inf_le_left
  have hzx : z ∈ centralizer ({x} : Set G) := hKc.1 hzK
  have hxz : x * z = z * x := (Subgroup.mem_centralizer_singleton_iff.mp hzx).symm
  have aux : ∀ (t : G) (J : Subgroup G), PumpUpLT 2 z L t J → t ∈ Q →
      z ∈ normalizer (J : Set G) ∧ Nonempty (kBar J ≃* kBar L) := by
    intro t J hltJ htQ
    refine ⟨mem_normalizer_of_intrinsic hltJ hzL, ?_⟩
    have htKC : t ∈ CxK x K := hQ.le htQ
    have ht2 : orderOf t = 2 := hltJ.2.1.1
    have htx : t ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.mp htKC).1
    have htKs : t ∈ centralizerSection K (pPrimeCoreOf 2 K) := (Subgroup.mem_inf.mp htKC).2
    have htz : t ∈ centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hzc t htQ).symm
    have htLs : t ∈ centralizerSection L (pPrimeCoreOf 2 L) := hltJ.2.2.2.1
    have htN : t ∈ normalizer (Λz : Set G) := mem_normalizer_lam hΛz htz htKs.1
    have htΛz : t ∈ centralizerSection Λz (pPrimeCoreOf 2 Λz) :=
      mem_cSec_of_cover hΛzK hΛz.cover htN htKs
    have hΛzq : IsQuasisimple (↥Λz ⧸ pPrimeCore 2 ↥Λz) := isQuasisimple_hat hΛz.pcW
    obtain ⟨Θ, hΘX, hΘpc, -, -, -, -⟩ := cover_data (inf_le_left : Λz ⊓ centralizer ({t} : Set G) ≤ Λz)
      (exists_centralizer_mul_pPrimeCore htΛz ht2) hΛzq
    have hΘΛz : Θ ≤ Λz := hΘX.trans inf_le_left
    have hΘt : Θ ≤ centralizer ({t} : Set G) := hΘX.trans inf_le_right
    have hΘ2 := (isPCompIn_two_iff.mp hΘpc).2
    have hΘperf : ⁅Θ, Θ⁆ = Θ := commutator_self_of_isTwoComponent hΘX hΘ2
    have hΘne : Θ ≠ ⊥ := ne_bot_of_isTwoComponent hΘ2
    obtain ⟨ΛA, hΛA⟩ := exists_isLam (z := x) ht2 hKc htKs
    obtain ⟨ΛB, hΛB⟩ := exists_isLam (z := z) ht2 hLc htLs
    have hΘA : Θ ≤ pLayerOf 2 (K ⊓ centralizer ({t} : Set G)) := by
      refine le_of_forall_two_elt hΘpc (fun w hw hw2 => ?_)
      rw [hΛA.layer]
      exact hΛA.twoElt w (Subgroup.mem_inf.mpr ⟨hΛzK (hΘΛz hw), hΘt hw⟩) hw2
    have hΘB : Θ ≤ pLayerOf 2 (L ⊓ centralizer ({t} : Set G)) := by
      refine le_of_forall_two_elt hΘpc (fun w hw hw2 => ?_)
      rw [hΛB.layer]
      exact hΛB.twoElt w (Subgroup.mem_inf.mpr ⟨hΛzL (hΘΛz hw), hΘt hw⟩) hw2
    have hJK : IsPCompIn 2 (pumpUp 2 K t) J :=
      isPCompIn_pumpUp_of_common (s := t) (a := x) (b := z) (A := K) (B := L) (Θ := Θ) ht2 hx2 hz2
        (mem_centralizer_symm htx) (mem_centralizer_symm htz) hxz hKc hLc htKs htLs
        (Subgroup.le_normalizer hzK) hΘperf hΘne hΘA hΘB hltJ.2.1.2.2 hltJ.2.2.2.2
    have hltK : PumpUpLT 2 x K t J := ⟨hterm.1, hltJ.2.1, htx, htKs, hJK⟩
    obtain ⟨-, ⟨eJK⟩⟩ := hterm.2.1 t J hltK
    exact ⟨eJK.trans eLK.symm⟩
  intro t J hltJ
  have htC : t ∈ CxK z L := mem_CxK_of_pumpUpLT hltJ
  have ht2 : orderOf t = 2 := hltJ.2.1.1
  obtain ⟨g, hg, hgt⟩ := exists_conj_mem_sylow hQL htC ht2
  have hgY : g ∈ centralizer ({z} : Set G) := (Subgroup.mem_inf.mp hg).1
  have hgN : g ∈ normalizer (L : Set G) := (Subgroup.mem_inf.mp hg).2.1
  have hgL : cmap g L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hlt' := pumpUpLT_cmap hltJ g
  rw [conj_fix_of_mem_centralizer hgY, hgL] at hlt'
  obtain ⟨hN', ⟨e'⟩⟩ := aux _ _ hlt' hgt
  refine ⟨?_, ?_⟩
  · have := (mem_normalizer_cmap_iff' (c := g) (y := z) (K := J))
    rw [conj_fix_of_mem_centralizer hgY] at this
    exact this.mp hN'
  · obtain ⟨e1⟩ := nonempty_quot_cmap g J
    exact ⟨e1.symm.trans e'⟩


theorem KLcore {z : G} {L : Subgroup G} (hP : GoodPair z L) {t s : G} {J I : Subgroup G}
    (h1 : PumpUpLT 2 z L t J) (h2 : PumpUpLT 2 t J s I) (hzs : z * s = s * z) :
    PumpUpLT 2 z L s I := by
  obtain ⟨hILo, hzL, hT1⟩ := hP
  obtain ⟨hzN, ⟨eJL⟩⟩ := hT1 t J h1
  have hz2 : orderOf z = 2 := h1.1.1
  have ht2 : orderOf t = 2 := h1.2.1.1
  have hs2 : orderOf s = 2 := h2.2.1.1
  have hLc : IsPCompIn 2 (centralizer ({z} : Set G)) L := h1.1.2.2
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := h1.2.1.2.2
  have hzt : t ∈ centralizer ({z} : Set G) := h1.2.2.1
  have hzY : z ∈ centralizer ({t} : Set G) := mem_centralizer_symm hzt
  have hst : s ∈ centralizer ({t} : Set G) := h2.2.2.1
  have hsJs : s ∈ centralizerSection J (pPrimeCoreOf 2 J) := h2.2.2.2.1
  have htLs : t ∈ centralizerSection L (pPrimeCoreOf 2 L) := h1.2.2.2.1
  have hsz : s ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hzs.symm
  have hle : hatCard J ≤ hatCard L := (Nat.card_congr eJL.toEquiv).le
  obtain ⟨Λ, hΛ, -, -, -, -, hcases⟩ := rigid_step h1 hzY hle
  have hD : bar t Λ = bar t J := (hcases.resolve_right (fun h => h.1 hzN)).2
  have hscen : ∀ w ∈ bar t J, sbar s hst * w * (sbar s hst)⁻¹ = w :=
    centralizes_of_mem_CxK hJc hst (Subgroup.mem_inf.mpr ⟨hst, hsJs⟩)
  have hscenΛ : ∀ w ∈ bar t Λ, sbar s hst * w * (sbar s hst)⁻¹ = w := by
    rw [hD]; exact hscen
  have hΛX : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) Λ := hΛ.pcW
  have hΛL : Λ ≤ L := (hΛ.le).trans inf_le_left
  have hΛt : Λ ≤ centralizer ({t} : Set G) := (hΛ.le).trans inf_le_right
  have hsX : s ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hsz, hst⟩
  have hcmapX : cmap s (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) =
      centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsX)
  have hcΛ : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) (cmap s Λ) := by
    have := isPCompIn_cmap hΛX s
    rwa [hcmapX] at this
  have hbarΛ : bar t (cmap s Λ) = bar t Λ := by
    rw [bar_cmap hst]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have := hscenΛ u hu
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [this]; exact hu
    · intro hw
      exact ⟨w, hw, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hscenΛ w hw⟩
  have hΛs : cmap s Λ = Λ := eq_of_bar_eq (inf_le_right) hcΛ hΛX hbarΛ
  have hsNΛ : s ∈ normalizer (Λ : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hΛs
  have hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := isQuasisimple_hat hLc
  have hcmapC : cmap s (centralizer ({z} : Set G)) = centralizer ({z} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsz)
  have hLs : cmap s L = L := by
    by_contra hne
    have hL'c : IsPCompIn 2 (centralizer ({z} : Set G)) (cmap s L) := by
      have := isPCompIn_cmap hLc s
      rwa [hcmapC] at this
    have hΛL' : Λ ≤ cmap s L := by
      rw [← hΛs]
      exact Subgroup.map_mono hΛL
    have hcs : cmap s L ≤ cSec L := le_cSec_of_ne hL'c hLc hne
    exact false_of_cover_le_cSec hΛL hΛ.cover hLq (fun a ha => hcs (hΛL' ha))
  have hsNL : s ∈ normalizer (L : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLs
  have hsΛc : s ∈ centralizerSection Λ (pPrimeCoreOf 2 Λ) := mem_cSec_of_bar hΛt hst hsNΛ hscenΛ
  have hsLc : s ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
    mem_cSec_of_cover' hΛL hΛ.cover hsNL hsΛc
  have hΛq : IsQuasisimple (↥Λ ⧸ pPrimeCore 2 ↥Λ) := isQuasisimple_hat hΛX
  obtain ⟨Θ, hΘX, hΘpc, -, -, -, -⟩ := cover_data (inf_le_left : Λ ⊓ centralizer ({s} : Set G) ≤ Λ)
    (exists_centralizer_mul_pPrimeCore hsΛc hs2) hΛq
  have hΘΛ : Θ ≤ Λ := hΘX.trans inf_le_left
  have hΘs : Θ ≤ centralizer ({s} : Set G) := hΘX.trans inf_le_right
  have hΘ2 := (isPCompIn_two_iff.mp hΘpc).2
  have hΘperf : ⁅Θ, Θ⁆ = Θ := commutator_self_of_isTwoComponent hΘX hΘ2
  have hΘne : Θ ≠ ⊥ := ne_bot_of_isTwoComponent hΘ2
  obtain ⟨ΛA, hΛA⟩ := exists_isLam (z := z) hs2 hLc hsLc
  obtain ⟨ΛB, hΛB⟩ := exists_isLam (z := t) hs2 hJc hsJs
  have hΘA : Θ ≤ pLayerOf 2 (L ⊓ centralizer ({s} : Set G)) := by
    refine le_of_forall_two_elt hΘpc (fun w hw hw2 => ?_)
    rw [hΛA.layer]
    exact hΛA.twoElt w (Subgroup.mem_inf.mpr ⟨hΛL (hΘΛ hw), hΘs hw⟩) hw2
  have hΘJ : Θ ≤ J := by
    have hperf : Group.IsPerfect ↥(Θ.subgroupOf (centralizer ({t} : Set G))) :=
      isPerfect_subgroupOf hΘperf (hΘΛ.trans hΛt)
    have hM2 : TwoComponents.IsTwoComponent (J.subgroupOf (centralizer ({t} : Set G))) :=
      (isPCompIn_two_iff.mp hJc).2
    have hmap : (Θ.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) ≤
        (J.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) := by
      rintro _ ⟨p, hp, rfl⟩
      have hpΘ : (p : G) ∈ Θ := Subgroup.mem_subgroupOf.mp hp
      have : barMk ↥(centralizer ({t} : Set G)) p ∈ bar t Λ :=
        ⟨p, Subgroup.mem_subgroupOf.mpr (hΘΛ hpΘ), rfl⟩
      rw [hD] at this
      exact this
    intro a ha
    have haY : a ∈ centralizer ({t} : Set G) := hΘΛ.trans hΛt ha
    have := le_of_perfect_map_le hperf hM2 hmap
      (Subgroup.mem_subgroupOf.mpr ha : (⟨a, haY⟩ : ↥(centralizer ({t} : Set G))) ∈ _)
    exact Subgroup.mem_subgroupOf.mp this
  have hΘB : Θ ≤ pLayerOf 2 (J ⊓ centralizer ({s} : Set G)) := by
    refine le_of_forall_two_elt hΘpc (fun w hw hw2 => ?_)
    rw [hΛB.layer]
    exact hΛB.twoElt w (Subgroup.mem_inf.mpr ⟨hΘJ hw, hΘs hw⟩) hw2
  have hpump : IsPCompIn 2 (pumpUp 2 L s) I :=
    isPCompIn_pumpUp_of_common (s := s) (a := z) (b := t) (A := L) (B := J) (Θ := Θ) hs2 hz2 ht2
      (mem_centralizer_symm hsz) (mem_centralizer_symm hst)
      (Subgroup.mem_centralizer_singleton_iff.mp hzt).symm hLc hJc hsLc hsJs htLs.1 hΘperf hΘne hΘA hΘB
      h2.2.1.2.2 h2.2.2.2.2
  exact ⟨hILo, h2.2.1, hsz, hsLc, hpump⟩


theorem KL {z : G} {L : Subgroup G} (hP : GoodPair z L) {t s : G} {J I : Subgroup G}
    (h1 : PumpUpLT 2 z L t J) (h2 : PumpUpLT 2 t J s I) :
    ∃ c : G, PumpUpLT 2 (c * z * c⁻¹) (cmap c L) s I := by
  have hP' := hP
  obtain ⟨hILo, hzL, hT1⟩ := hP
  obtain ⟨hzN, ⟨eJL⟩⟩ := hT1 t J h1
  have hz2 : orderOf z = 2 := h1.1.1
  have ht2 : orderOf t = 2 := h1.2.1.1
  have hs2 : orderOf s = 2 := h2.2.1.1
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := h1.2.1.2.2
  have hzt : t ∈ centralizer ({z} : Set G) := h1.2.2.1
  have hzY : z ∈ centralizer ({t} : Set G) := mem_centralizer_symm hzt
  have hst : s ∈ centralizer ({t} : Set G) := h2.2.2.1
  have hsJs : s ∈ centralizerSection J (pPrimeCoreOf 2 J) := h2.2.2.2.1
  have hle : hatCard J ≤ hatCard L := (Nat.card_congr eJL.toEquiv).le
  obtain ⟨Λ, hΛ, -, -, -, -, hcases⟩ := rigid_step h1 hzY hle
  have hD : bar t Λ = bar t J := (hcases.resolve_right (fun h => h.1 hzN)).2
  have hscen : ∀ w ∈ bar t J, sbar s hst * w * (sbar s hst)⁻¹ = w :=
    centralizes_of_mem_CxK hJc hst (Subgroup.mem_inf.mpr ⟨hst, hsJs⟩)
  have hzz : z ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, ← pow_one 2] at this
  have hzΛ : z ∈ Λ := hΛ.twoElt z (Subgroup.mem_inf.mpr ⟨hzL, hzY⟩) ⟨1, hzz⟩
  have hzmem : sbar z hzY ∈ bar t J := by
    rw [← hD]
    exact ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hzΛ, rfl⟩
  have hzs_bar := hscen _ hzmem
  have hzsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hssq : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs2, pow_two] at this
  have hcY : z * s * z⁻¹ * s⁻¹ ∈ centralizer ({t} : Set G) :=
    mul_mem (mul_mem (mul_mem hzY hst) (inv_mem hzY)) (inv_mem hst)
  have hc1 : barMk ↥(centralizer ({t} : Set G)) ⟨z * s * z⁻¹ * s⁻¹, hcY⟩ = 1 := by
    have h2' : (⟨z * s * z⁻¹ * s⁻¹, hcY⟩ : ↥(centralizer ({t} : Set G))) =
        ⟨z, hzY⟩ * ⟨s, hst⟩ * ⟨z, hzY⟩⁻¹ * ⟨s, hst⟩⁻¹ := rfl
    rw [h2']
    simp only [map_mul, map_inv]
    change sbar z hzY * sbar s hst * (sbar z hzY)⁻¹ * (sbar s hst)⁻¹ = 1
    generalize sbar z hzY = α at hzs_bar ⊢
    generalize sbar s hst = β at hzs_bar ⊢
    have h3 : β * α = α * β := by
      calc β * α = (β * α * β⁻¹) * β := by group
        _ = α * β := by rw [hzs_bar]
    calc α * β * α⁻¹ * β⁻¹ = (β * α) * α⁻¹ * β⁻¹ := by rw [h3]
      _ = 1 := by group
  have hcP : (⟨z * s * z⁻¹ * s⁻¹, hcY⟩ : ↥(centralizer ({t} : Set G))) ∈
      pPrimeCore 2 ↥(centralizer ({t} : Set G)) := (QuotientGroup.eq_one_iff _).mp hc1
  have hodd : Odd (orderOf (z * s * z⁻¹ * s⁻¹)) := by
    have h1' := Odd.of_dvd_nat (odd_card_pPrimeCore ↥(centralizer ({t} : Set G)))
      (Subgroup.orderOf_dvd_natCard _ hcP)
    rwa [Subgroup.orderOf_mk] at h1'
  obtain ⟨k, hk⟩ := exists_pow_conj_commute hzsq hssq hodd
  have hc₀Y : (z * s * z⁻¹ * s⁻¹) ^ k ∈ centralizer ({t} : Set G) := pow_mem hcY k
  have hc₀1 : barMk ↥(centralizer ({t} : Set G)) ⟨(z * s * z⁻¹ * s⁻¹) ^ k, hc₀Y⟩ = 1 := by
    have : (⟨(z * s * z⁻¹ * s⁻¹) ^ k, hc₀Y⟩ : ↥(centralizer ({t} : Set G))) =
        (⟨z * s * z⁻¹ * s⁻¹, hcY⟩ : ↥(centralizer ({t} : Set G))) ^ k := rfl
    rw [this, map_pow, hc1, one_pow]
  have hc₀N : (z * s * z⁻¹ * s⁻¹) ^ k ∈ normalizer (J : Set G) := by
    refine mem_normalizer_of_map_normalizes hJc.1 (isPCompIn_two_iff.mp hJc).2 hc₀Y ?_
    rw [hc₀1]
    have h1 : (MulAut.conj (1 : barQ ↥(centralizer ({t} : Set G)))).toMonoidHom =
        MonoidHom.id (barQ ↥(centralizer ({t} : Set G))) := by
      ext x; simp
    rw [h1, Subgroup.map_id]
  have hcJ : cmap ((z * s * z⁻¹ * s⁻¹) ^ k) J = J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hc₀N
  have h1' : PumpUpLT 2 ((z * s * z⁻¹ * s⁻¹) ^ k * z * ((z * s * z⁻¹ * s⁻¹) ^ k)⁻¹)
      (cmap ((z * s * z⁻¹ * s⁻¹) ^ k) L) t J := by
    have := pumpUpLT_cmap h1 ((z * s * z⁻¹ * s⁻¹) ^ k)
    rwa [conj_fix_of_mem_centralizer hc₀Y, hcJ] at this
  exact ⟨(z * s * z⁻¹ * s⁻¹) ^ k, KLcore (GoodPair_cmap hP' _) h1' h2 hk⟩

@[expose] def Reach (z : G) (L : Subgroup G) (p : G × Subgroup G) : Prop :=
  ∃ c : G, PumpUpLT 2 (c * z * c⁻¹) (cmap c L) p.1 p.2

theorem Reach.iso {z : G} {L : Subgroup G} (hP : GoodPair z L) {p : G × Subgroup G}
    (h : Reach z L p) : Nonempty (kBar p.2 ≃* kBar L) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨-, ⟨e⟩⟩ := (GoodPair_cmap hP c).2.2 p.1 p.2 hc
  obtain ⟨e2⟩ := nonempty_quot_cmap c L
  exact ⟨e.trans e2⟩

theorem Reach.step {z : G} {L : Subgroup G} (hP : GoodPair z L) {p q : G × Subgroup G}
    (h : Reach z L p) (hpq : PumpUpLT 2 p.1 p.2 q.1 q.2) : Reach z L q := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := KL (GoodPair_cmap hP c) hc hpq
  refine ⟨c' * c, ?_⟩
  have e1 : c' * c * z * (c' * c)⁻¹ = c' * (c * z * c⁻¹) * c'⁻¹ := by group
  rw [e1, ← cmap_cmap]
  exact hc'

theorem Reach.chain {z : G} {L : Subgroup G} (hP : GoodPair z L) {p q : G × Subgroup G}
    (h : Reach z L p)
    (hc : Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT 2 a.1 a.2 b.1 b.2) p q) :
    Reach z L q := by
  induction hc with
  | refl => exact h
  | tail _ hstep ih => exact Reach.step hP ih hstep

theorem isPRigid_of_goodPair {z : G} {L : Subgroup G} (hP : GoodPair z L) : IsPRigid 2 z L := by
  refine ⟨hP.1, fun x' K' hl => ?_⟩
  obtain ⟨-, hchain⟩ := hl
  rcases Relation.ReflTransGen.cases_head hchain with h | ⟨p, hp, hpq⟩
  · have hz : z = x' := congrArg Prod.fst h
    have hL : L = K' := congrArg Prod.snd h
    subst hz hL
    exact ⟨MulEquiv.refl _⟩
  · have hreach : Reach z L p := ⟨1, by
      have : PumpUpLT 2 z L p.1 p.2 := hp
      rwa [one_mul, inv_one, mul_one, cmap_one']⟩
    exact Reach.iso hP (Reach.chain hP hreach hpq)


theorem exists_goodPair (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K : Subgroup G} (hterm : IsTwoTerminal x K)
    (hZ : center (↥K ⧸ pPrimeCore 2 ↥K) ≠ ⊥) :
    ∃ (z : G) (L : Subgroup G), GoodPair z L ∧ Nonempty (kBar L ≃* kBar K) := by
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hterm.1.2.2
  obtain ⟨Q, hQ, z, hzQ, hzc, hzcl, hz2⟩ := exists_sylow_central_lift' hKc hZ
  have hzK : z ∈ K := centralLift_le K hzcl
  have hzC : z ∈ CxK x K := hQ.le hzQ
  obtain ⟨L, hlt⟩ := exists_pumpUpLT hterm.1 hz2 hzC (hR z hz2)
  obtain ⟨hxN, ⟨eLK⟩⟩ := hterm.2.1 z L hlt
  have hQL : IsSylowOf 2 Q (CxK z L) := hterm.2.2 Q hQ z L hlt hzQ hzc
  have hle : hatCard L ≤ hatCard K := (Nat.card_congr eLK.toEquiv).le
  obtain ⟨Λz, hΛz, -, hΛzL⟩ := trivial_pumpup_data hlt hxN hle
  have hzz : z ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, ← pow_one 2] at this
  have hzΛ : z ∈ Λz := hΛz.twoElt z (Subgroup.mem_inf.mpr ⟨hzK, mem_centralizer_singleton_iff.mpr rfl⟩) ⟨1, hzz⟩
  have hzL : z ∈ L := hΛzL hzΛ
  exact ⟨z, L, ⟨hlt.2.1, hzL, T1_of_terminal hterm hlt hQ hzc hQL hzL hzK Λz hΛz hΛzL⟩, ⟨eLK⟩⟩

end CFSG.GH74.GLS.Bg.Iii2.L41
