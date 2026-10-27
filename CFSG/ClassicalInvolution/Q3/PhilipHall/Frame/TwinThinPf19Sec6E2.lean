module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6E4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

set_option linter.unusedSectionVars false

namespace TwinThin

section Core

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_tightInO2 {X : Subgroup G} {t : ↥X} (h : TightInO2 t) :
    (t : G) ∈ pCoreOf 2 X := by
  obtain ⟨P, hPn, hP2, htP⟩ := h
  have hQ2 : IsPGroup 2 ↥(P.map X.subtype) := hP2.map X.subtype
  have hQX : P.map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hQn : ∀ x ∈ X, ∀ q ∈ P.map X.subtype, x * q * x⁻¹ ∈ P.map X.subtype := by
    intro x hx q hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹, hPn.conj_mem q' hq' ⟨x, hx⟩, rfl⟩
  exact Cross.le_pCoreOf_of_inv hQX hQn hQ2 ⟨t, htP, rfl⟩

end Core

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem e2_Yu {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) (hE4 : E4SplitModel) (hG : Nat.card G ≤ n)
    (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {m : ℕ} (hm : 5 ≤ m)
    (hAut : TwinThinPf8.AEAut m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {u : G} (hu : PairInv K K' z π g u)
    (hO : classicalInvolutionOddCore ↥(centLayer (CoreAssembly.conjClass K₀) u) = ⊥)
    (horb : ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u,
      ∃ x ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub x (conjSub g K) = L)
    (hnb : conjSub g K' ∈ π) :
    ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u, ∀ t : G, IsUniqueInvolution L t →
      t ∈ pCoreOf 2 (centLayer (CoreAssembly.conjClass K₀) u) := by
  classical
  set Yu := centLayer (CoreAssembly.conjClass K₀) u with hYu
  have hX := S.pairInv_commute hu
  have hΩ0 : HypOmegaGen (CoreAssembly.conjClass K₀) := S.hs.hyp
  have hKgΩ : conjSub g K ∈ CoreAssembly.conjClass K₀ := S.hos.graph.conjMem K S.hK g
  have hKg'Ω : conjSub g K' ∈ CoreAssembly.conjClass K₀ := S.hos.graph.conjMem K' S.hK'.1 g
  have hKgY : conjSub g K ≤ Yu := le_centLayer (S.mem_centMembers_of_pi hX S.hg)
  have hKg'Y : conjSub g K' ≤ Yu := le_centLayer (S.mem_centMembers_of_pi hX hnb)
  have hzY : g * z * g⁻¹ ∈ Yu := S.zg_mem_centLayer hX
  have hcard : Nat.card ↥Yu < n :=
    lt_of_lt_of_le (natCard_lt_of_ne_top (S.centLayer_ne_top hS hnab hu.2.2.2.1)) hG
  set R : Subgroup ↥Yu := (conjSub g K).subgroupOf Yu with hR
  set R' : Subgroup ↥Yu := (conjSub g K').subgroupOf Yu with hR'
  set t : ↥Yu := ⟨g * z * g⁻¹, hzY⟩ with ht_def
  have hR2 : IsPGroup 2 ↥R := (S.hs.two _ hKgΩ).comap_subtype
  have htc : tightCore R = R := tightCore_eq_self_of_isPGroup hR2
  have ht : IsUniqueInvolution R t := isUniqueInvolution_subgroupOf (S.hz.conj g) hKgY
  have ht' : IsUniqueInvolution R' t := isUniqueInvolution_subgroupOf (S.hz'.conj g) hKg'Y
  have hRmem : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have hR'conj : R' ∈ CoreAssembly.conjClass R := by
    obtain ⟨x, hx, hxe⟩ := horb _ (S.mem_centMembers_of_pi hX hnb)
    refine ⟨⟨x, hx⟩, ?_⟩
    show conjSub (⟨x, hx⟩ : ↥Yu) R = R'
    rw [hR, conjSub_subgroupOf, hxe]
  have hne : R' ≠ R := by
    refine subgroupOf_ne_of_ne hKgY hKg'Y ?_
    intro hh
    apply S.hne
    have := congrArg (conjSub g⁻¹) hh
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hqR : Nonempty (↥R ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hKgY).trans (S.iso_q8 hKgΩ).some⟩
  have hq'R' : Nonempty (↥R' ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hKg'Y).trans (S.iso_q8 hKg'Ω).some⟩
  have hgenG : (⨆ x : ↥Yu, conjSub (x : G) (conjSub g K)) = Yu := by
    apply le_antisymm
    · refine iSup_le fun x => ?_
      have := conjSub_mono (n := (x : G)) hKgY
      rwa [conjSub_eq_self_of_mem x.2] at this
    · refine centLayer_le fun L hL => ?_
      obtain ⟨x, hx, rfl⟩ := horb L hL
      exact le_iSup (fun x : ↥Yu => conjSub (x : G) (conjSub g K)) ⟨x, hx⟩
  have hconj : ∀ y : ↥Yu, (conjSub y R).map Yu.subtype = conjSub (y : G) (conjSub g K) := by
    intro y
    have hle : conjSub (y : G) (conjSub g K) ≤ Yu := by
      have := conjSub_mono (n := (y : G)) hKgY
      rwa [conjSub_eq_self_of_mem y.2] at this
    rw [hR, conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hle
  have hgenR : (⨆ y : ↥Yu, conjSub y R) = ⊤ := by
    apply Subgroup.map_injective Yu.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [hconj]
    exact hgenG
  have hΩR : HypOmegaGen (CoreAssembly.conjClass R) :=
    hypOmegaGen_conjClass_section hΩ0 hKgΩ hKgY
  have hAR : AEmpty (CoreAssembly.conjClass R) R :=
    aEmpty_conjClass_section hΩ0 S.hs.two hKgΩ (S.aEmpty _ hKgΩ) hKgY
  obtain ⟨Sy⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  obtain ⟨hd, hqS⟩ := q8TwinDatum_of_isPGroup hR2 Sy ht hqR
  have hg' : TightSelfGen R := by
    show (⨆ g : ↥Yu, conjSub g (tightCore R)) = ⊤
    rw [htc]
    exact hgenR
  have hΩt : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := by rw [htc]; exact hΩR
  have hAt : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [htc]; exact hAR
  have htwin : ∃ K'' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K'' ≠ tightCore R := by
    rw [htc]
    exact ⟨R', ⟨hR'conj, t, ht, ht'⟩, hne⟩
  have hcore : g * z * g⁻¹ ∈ pCoreOf 2 Yu := by
    rcases (hP.twin rfl) ↥Yu hcard R Sy t hd hqS hg' hO hΩt hAt htwin with hin | hE4' | hlift
    · exact mem_pCoreOf_of_tightInO2 hin
    · obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := hE4'
      by_cases htN : t ∈ f.ker
      · exact mem_pCoreOf_of_tightInO2 ⟨f.ker, f.normal_ker, hf2, htN⟩
      · exfalso
        obtain ⟨w, hw3, hwR, hwR', r, hr, hwr⟩ := exists_split_of_twinE4 hE4 hqR hq'R' hR2 ht
          hR'conj ht' hne hΩR hgenR f hfs hf2 hQ htN
        have hwz : (w : G) * (g * z * g⁻¹) = (g * z * g⁻¹) * (w : G) := by
          have := ht.conj_eq hwR
          have h2 : w * t = t * w := by
            calc w * t = (w * t * w⁻¹) * w := by group
              _ = t * w := by rw [this]
          exact congrArg Subtype.val h2
        have hwKg : conjSub (w : G) (conjSub g K) = conjSub g K := by
          have h1 := hwR
          rw [hR, conjSub_subgroupOf] at h1
          have hyL : conjSub (w : G) (conjSub g K) ≤ Yu := by
            have := conjSub_mono (n := (w : G)) hKgY
            rwa [conjSub_eq_self_of_mem w.2] at this
          have h2 := Subgroup.subgroupOf_inj.mp h1
          rwa [inf_of_le_left hyL, inf_of_le_left hKgY] at h2
        have hwK' : ∀ y ∈ conjSub g K', (w : G) * y = y * (w : G) := by
          intro y hy
          have hyR : (⟨y, hKg'Y hy⟩ : ↥Yu) ∈ R' := Subgroup.mem_subgroupOf.mpr hy
          have := congrArg Subtype.val (hwR' _ hyR)
          simpa using this
        have hnt : ∃ r' ∈ conjSub g K, (w : G) * r' ≠ r' * (w : G) :=
          ⟨(r : G), Subgroup.mem_subgroupOf.mp hr, fun hh => hwr (Subtype.ext (by simpa using hh))⟩
        have hw3' : (w : G) ^ 3 = 1 := by
          have := congrArg Subtype.val hw3
          simpa using this
        exact S.false_of_split_Yu hm hAut htw J hw3' hwz hwKg hwK' hnt
    · exact (S.false_of_longFundSetE3 hm hAut htw J hodd hu horb hnb hzY hlift).elim
  intro L hL t' ht'L
  obtain ⟨x, hx, rfl⟩ := horb L hL
  have heq : x * (g * z * g⁻¹) * x⁻¹ = t' := ((S.hz.conj g).conj x).eq ht'L
  have hN := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 Yu Yu le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have h1 := hN.conj_mem ⟨g * z * g⁻¹, hzY⟩ (Subgroup.mem_subgroupOf.mpr hcore) ⟨x, hx⟩
  rw [← heq]
  exact Subgroup.mem_subgroupOf.mp h1

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
