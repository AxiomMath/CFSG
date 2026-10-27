module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnThin
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinH1

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner

section Hself

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hself_R (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) :
    ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → UAt Ω u L := by
  intro L hL u hu
  obtain ⟨C, hCL, hCc, hCcard⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isPGroup hL (h2 L hL))).exists_cyclic_index_two
  refine TwinSecXg.uAt_of_cyclic_index_two hΩ h2 hL hu ⟨C, hCL, hCc, ?_⟩
  have h1 := Subgroup.relIndex_mul_card C L
  rw [inf_eq_left.mpr hCL, hCcard] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

end Hself

section Thin

variable {G : Type} [Group G] [Finite G] {K₀ : Subgroup G}

theorem twin_thin_of_tightInO2_R (hs : TwinGraphStd K₀)
    (hO2 : ∀ P : Subgroup G, P.Normal → IsPGroup 2 ↥P → P = ⊥)
    {K : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀) {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K) (hH1 : NoCentralInv π)
    {z : G} (hz : IsUniqueInvolution K z) {g : G} (hg : conjSub g K ∈ π)
    (hKX : K ≤ conjSub g (piGen π))
    (hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥)
    (h : TightInO2 (secInv (conjSub g (piGen π)) ⟨z, hKX hz.mem⟩)) :
    ∀ M N : Subgroup G, MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) M N →
      ThinAt (CoreAssembly.conjClass K₀) M N := by
  have hos := hs.orbitStd
  have hself := hself_R hs.hyp hs.two
  have hE := TwinSecXg.e2At_of_tightInO2 hos hK hπ hH1 hz hKX hO h
  have hmax := TwinSecXg.maxAdj_conj_left hos hπ hg
  rcases TC.inO2_or_thinAt hs.hyp hs.two hs.sep hK (TwinSecXg.conj_trans_of_mem_conjClass hK)
      (iSup_conjClass_eq_top hs.gen) hs.conn hself hmax hE hz with ⟨P, hPn, hP2, hzP⟩ | hthin
  · exfalso
    have := hO2 P hPn hP2
    rw [this, Subgroup.mem_bot] at hzP
    exact hz.ne_one hzP
  · exact hthin

end Thin

section SectionIH


section Quotient
variable {H : Type} [Group H] [Finite H]

theorem datumInO2_quotient {r n : ℕ} (hr : 4 ≤ r) (hT : Thm1RTwinInO2 r n)
    (hlt : Nat.card H < n) (N₀ : Subgroup H) [N₀.Normal] (hNodd : Odd (Nat.card N₀))
    (hO : classicalInvolutionOddCore (H ⧸ N₀) = ⊥) {J₀ : Subgroup H}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass J₀)) (h2 : IsPGroup 2 J₀)
    (hA : AEmpty (CoreAssembly.conjClass J₀) J₀)
    (hq8 : Nonempty (↥J₀ ≃* QuaternionGroup (2 ^ (r - 2))))
    (hgen : (⨆ g : H, conjSub g J₀) = ⊤) {t : H} (ht : IsUniqueInvolution J₀ t)
    (S : Sylow 2 ↥(J₀.map (QuotientGroup.mk' N₀)))
    (htw : HasTwin (J₀.map (QuotientGroup.mk' N₀))) : TightInO2 (QuotientGroup.mk' N₀ t) := by
  have hmem : ∀ K ∈ CoreAssembly.conjClass J₀, IsPGroup 2 K := by
    rintro _ ⟨g, rfl⟩
    exact isPGroup_conjSub g h2
  have hJN : J₀ ⊓ N₀ = ⊥ :=
    OddQuot.inf_eq_bot_of_mem hmem hNodd (CoreAssembly.mem_conjClass_self J₀)
  have hfam : quotFamily (CoreAssembly.conjClass J₀) N₀ =
      CoreAssembly.conjClass (J₀.map (QuotientGroup.mk' N₀)) :=
    image_conjClass (N := N₀) J₀
  have hR2 : IsPGroup 2 (J₀.map (QuotientGroup.mk' N₀)) := h2.map _
  have htc : tightCore (J₀.map (QuotientGroup.mk' N₀)) = J₀.map (QuotientGroup.mk' N₀) :=
    PhilipHall.Frame.tightCore_eq_self_of_isPGroup hR2
  have hq := OddQuot.hypOmegaGen_quotFamily hΩ hmem hNodd
  have hAall := aEmpty_forall_of_transitive hΩ.conjInvariant (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) hA
  have hAq := OddQuot.aEmpty_quotFamily hΩ hmem hNodd hAall (J₀.map (QuotientGroup.mk' N₀))
    (map_mem_quotFamily (CoreAssembly.mem_conjClass_self J₀))
  rw [hfam] at hq hAq
  have hut : IsUniqueInvolution (J₀.map (QuotientGroup.mk' N₀)) (QuotientGroup.mk' N₀ t) :=
    AscQuot.isUniqueInvolution_map_mk hJN ht
  obtain ⟨hd, hSq⟩ := qTwinDatum_of_isPGroupK (by omega : 3 ≤ r) hR2 S hut
    ⟨(AscQuot.quotRestrictEquiv hJN).symm.trans hq8.some⟩
  have hgen' : TightSelfGen (J₀.map (QuotientGroup.mk' N₀)) := by
    show (⨆ g : H ⧸ N₀, conjSub g (tightCore (J₀.map (QuotientGroup.mk' N₀)))) = ⊤
    rw [htc, eq_top_iff, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N₀),
      ← hgen, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [TwistQ.conjSub_map]
    exact le_iSup (fun g : H ⧸ N₀ => conjSub g (J₀.map (QuotientGroup.mk' N₀)))
      (QuotientGroup.mk' N₀ g)
  have hcard : Nat.card (H ⧸ N₀) < n :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)) hlt
  refine hT (H ⧸ N₀) hcard _ S _ hd hSq hgen' hO ?_ ?_ htw
  · rw [htc]; exact hq
  · rw [htc]; exact hAq

end Quotient

section Main

variable {G : Type} [Group G] [Finite G]

theorem sectionInO2_of_IH {r n : ℕ} (hr : 4 ≤ r) (hT : Thm1RTwinInO2 r n)
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K)
    {J : Subgroup G} (hJ : J ∈ Ω) (hq8 : Nonempty (↥J ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : AEmpty Ω J) {X : Subgroup G} (hJX : J ≤ X) (hXn : Nat.card X < n)
    (hgen : (⨆ x : X, conjSub (x : G) J) = X) {t : G} (ht : IsUniqueInvolution J t)
    (htw : ∃ K ∈ twinSet {L | ∃ x : X, conjSub (x : G) J = L} J, K ≠ J) :
    TightInO2 (secInv X ⟨t, hJX ht.mem⟩) := by
  have hconj : ∀ g : ↥X, (conjSub g (J.subgroupOf X)).map X.subtype = conjSub (g : G) J := by
    intro g
    have hle : conjSub (g : G) J ≤ X := by
      have := conjSub_mono (n := (g : G)) hJX
      rwa [conjSub_eq_self_of_mem g.2] at this
    rw [conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hle
  have hgenX : (⨆ g : ↥X, conjSub g (J.subgroupOf X)) = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [hconj]
    exact hgen
  have hJ2 : IsPGroup 2 (J.subgroupOf X) := (h2 J hJ).comap_subtype
  have hq8X : Nonempty (↥(J.subgroupOf X) ≃* QuaternionGroup (2 ^ (r - 2))) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hJX).trans hq8.some⟩
  have htX : IsUniqueInvolution (J.subgroupOf X) (⟨t, hJX ht.mem⟩ : X) :=
    isUniqueInvolution_subgroupOf ht hJX
  exact datumInO2_quotient hr hT hXn (classicalInvolutionOddCore ↥X)
    (CFSG.ComponentClassification.OddCore.odd_card ↥X)
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥X)
    (hypOmegaGen_conjClass_section hΩ hJ hJX) hJ2 (aEmpty_conjClass_section hΩ h2 hJ hA hJX)
    hq8X hgenX htX (Classical.choice inferInstance)
    ((hasTwin_secImage_iff hΩ h2 hJ hJX).mpr htw)

end Main

end SectionIH

section Conn


theorem card_quaternion_pow {r : ℕ} (hr : 2 ≤ r) :
    Nat.card (QuaternionGroup (2 ^ (r - 2))) = 2 ^ r := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add]
  ring

structure TwinConnPreR (r : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) : Prop where
  oddCent : ∀ K ∈ CoreAssembly.conjClass (tightCore R), ∀ z : Y, IsUniqueInvolution K z →
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)) = ⊥
  mem : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J ∧
    Nonempty (↥J ≃* QuaternionGroup (2 ^ (r - 2)))
  gs : TwinGraphStd (tightCore R)

theorem false_of_conn_R {r n : ℕ} (hr : 4 ≤ r) (hT : Thm1RTwinInO2 r n) {Y : Type} [Group Y]
    [Finite Y] {R : Subgroup Y} {t : Y} (hcard : Nat.card Y ≤ n)
    (hS : IsSimpleGroup ↥(genFittingFStar Y))
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a)
    (hA : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht : IsUniqueInvolution (tightCore R) t)
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R)
    (hpre : TwinConnPreR r R) : False := by
  classical
  have hZ : Subgroup.center Y = ⊥ := PhilipHall.InductionBridge.center_eq_bot_of_fstar_simple hS hnab
  have hK₀Ω : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hgs := hpre.gs
  have hos := hgs.orbitStd
  have hq : Nonempty (↥(tightCore R) ≃* QuaternionGroup (2 ^ (r - 2))) := (hpre.mem _ hK₀Ω).2
  obtain ⟨K', hK', hne⟩ := htw
  obtain ⟨π, hmax, -, hH1⟩ := twin_noCentralInv hgs hZ hK₀Ω hK'.1 hne ht
  have hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) := by
    rw [hmax]
    rfl
  obtain ⟨g, hg⟩ := TwinSecXg.exists_conj_mem hos hK₀Ω hπ
  have hKX : tightCore R ≤ conjSub g (piGen π) := hos.le_conj_piGen hπ hg
  have hw : IsUniqueInvolution (conjSub g (tightCore R)) (g * t * g⁻¹) := ht.conj g
  have hXw := (hos.conj_piGen_le_centralizer hK₀Ω hπ hH1 ht g).1
  have hXn := hos.conj_piGen_normal hK₀Ω hπ hH1 ht g
  have hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥ :=
    TwinSecXg.oddCore_eq_bot_of_normal hXn hXw (hpre.oddCent _ ⟨g, rfl⟩ _ hw)
  have hcardX := TwinSecXg.card_conj_lt hos hK₀Ω hπ hH1 hZ ht g
  have hSec := TwinSecXg.twinSection_conj hos hK₀Ω hπ hH1 hg hK' hne
  have hE2 : TightInO2 (secInv (conjSub g (piGen π)) ⟨t, hKX ht.mem⟩) :=
    sectionInO2_of_IH hr hT hgs.hyp hgs.two hK₀Ω hq hA hSec.le_left
      (lt_of_lt_of_le hcardX hcard) hSec.gen ht ⟨K', hSec.twin, hSec.ne⟩
  have hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 ↥P → P = ⊥ := fun _ hPn hP =>
    TwinSecXg.normalTwo_eq_bot_of_fstar_simple hS hnab hPn hP
  have hthin := twin_thin_of_tightInO2_R hgs hO2 hK₀Ω hπ hH1 ht hg hKX hO hE2
  have hcardJ : ∀ J ∈ CoreAssembly.conjClass (tightCore R), Nat.card J = 2 ^ r := by
    intro J hJ
    rw [Nat.card_congr (hpre.mem J hJ).2.some.toEquiv]
    exact card_quaternion_pow (by omega)
  exact ThinSettingR.false_of_four_le
    ⟨hgs, hK₀Ω, hK', hne, hcardJ, hA, ht, hπ, hH1, hg, hO, hthin⟩ hr

end Conn

end CFSG.CGT.PushingUpLit.SolKNA.R4
