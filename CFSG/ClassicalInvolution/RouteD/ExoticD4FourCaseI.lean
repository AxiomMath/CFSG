module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourComp
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourTwins
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Local
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourLift
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Balance

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Aux

theorem range_hom_normal {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) : ((D.hom i).range).Normal := by
  have key : ∀ g ∈ (⨆ k, (D.hom k).range : Subgroup X), ∀ n ∈ (D.hom i).range,
      g * n * g⁻¹ ∈ (D.hom i).range := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact (D.hom k).range.mul_mem ((D.hom k).range.mul_mem hy hn)
          ((D.hom k).range.inv_mem hy)
      · have := commutes_range D hki y hy n hn
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  refine ⟨fun n hn g => key g ?_ n hn⟩
  rw [D.generate]
  trivial

omit [Finite G] in
theorem conjSub_mem_compMembers_of_mem_layer (hΩ : ConjInvariant Ω) {u : G}
    {D : LieSystemData p f (locQuot Ω u) (locFamily Ω u)} {i : Fin D.card} {N : Subgroup G}
    (hN : N ∈ compMembers Ω u D i) {c : G} (hc : c ∈ locLayer Ω u) :
    conjSub c N ∈ compMembers Ω u D i := by
  have hcC : c ∈ Subgroup.centralizer ({u} : Set G) := centralizingLayer_le_centralizer Ω {u} hc
  refine ⟨⟨hΩ c N hN.1.1, ?_⟩, ?_⟩
  · intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := hN.1.2 hy
    have e : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC h1) (Subgroup.inv_mem _ hcC)
  · rw [locImg_conjSub_layer N ⟨c, hc⟩]
    rintro _ ⟨a, ha, rfl⟩
    exact (range_hom_normal D i).conj_mem a (hN.2 ha) (locMk Ω u ⟨c, hc⟩)

theorem locMk_eq_of_involutions (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    {N N' : Subgroup G} (hN : N ∈ centralizingMembers Ω {x})
    (hN' : N' ∈ centralizingMembers Ω {x}) (himg : locImg Ω x N = locImg Ω x N') {w w' : G}
    (hw : IsClassicalMember p f N w) (hw' : IsClassicalMember p f N' w')
    (hwY : w ∈ locLayer Ω x) (hw'Y : w' ∈ locLayer Ω x) :
    locMk Ω x ⟨w, hwY⟩ = locMk Ω x ⟨w', hw'Y⟩ := by
  obtain ⟨e⟩ := G2D4.nonempty_mulEquiv_locImg hΩ hex hN
  obtain ⟨hwY₀, hwA, hw2, hw1, hwc⟩ := G2D4.image_involution_facts hN hw
  obtain ⟨hw'Y₀, hwA', hw2', hw1', hwc'⟩ := G2D4.image_involution_facts hN' hw'
  have key : ∀ (a : locQuot Ω x) (ha : a ∈ locImg Ω x N), (∀ y ∈ locImg Ω x N, a * y = y * a) →
      a ≠ 1 → e ⟨a, ha⟩ = -1 := by
    intro a ha hc h1
    have hcen : (⟨a, ha⟩ : locImg Ω x N) ∈ Subgroup.center (locImg Ω x N) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hc y y.2).symm
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp
      ((CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e _).mp hcen) with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm) :
        (⟨a, ha⟩ : locImg Ω x N) = 1)) h1
    · exact h
  have hwA'' : locMk Ω x ⟨w', hw'Y⟩ ∈ locImg Ω x N := himg ▸ hwA'
  have h1 := key _ hwA hwc hw1
  have h2 := key _ hwA'' (fun y hy => hwc' y (himg ▸ hy)) hw1'
  exact congrArg Subtype.val (e.injective (h1.trans h2.symm))

end Aux

section Main

variable [IsSimpleGroup G] {K : Subgroup G} {z : G}

local notation "Ω'" => conjClass K

omit [IsSimpleGroup G] in
theorem not_mem_comp_of_outer (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f 4 .POmegaPlus 4 (conjClass K) z) {N : Subgroup G}
    (hN : N ∈ conjClass K) {z₀ : G} (hz₀ : IsClassicalMember p f N z₀) {u : G}
    (D : LieSystemData p f (locQuot (conjClass K) u) (locFamily (conjClass K) u))
    {i : Fin D.card} (hNi : N ∈ compMembers (conjClass K) u D i)
    (H1 : ∀ L ∈ outerSet (conjClass K) N, L ≤ Subgroup.centralizer ({u} : Set G))
    (H3 : ∃ T ∈ conjClass K, cnbhd (conjClass K) T = cnbhd (conjClass K) N ∧
      ∃ g ∈ T, u * g ≠ g * u)
    {M' : Subgroup G} (hM' : M' ∈ outerSet (conjClass K) N) :
    M' ∉ compMembers (conjClass K) u D i := by
  classical
  intro hM'i
  have hΩ : InClass p f Ω' := S.inClass
  have hex : ExactMembers Ω' := S.exact
  have hM'Ω' : M' ∈ Ω' := hM'.1.1
  have hNM' : N ∈ outerSet Ω' M' := mem_outerSet_symm hN hM'
  have hθ : outerGen Ω' N ≤ locLayer Ω' u :=
    iSup₂_le fun L hL => le_centralizingLayer ⟨hL.1.1, H1 L hL⟩
  have hall : ∀ L ∈ outerSet Ω' N, L ∈ compMembers Ω' u D i := by
    intro L hL
    obtain ⟨y, hy, hyL⟩ := exists_conj_of_shape S hloc hN hM' hL
    rw [← hyL]
    exact conjSub_mem_compMembers_of_mem_layer hΩ.conjInvariant hM'i (hθ hy)
  obtain ⟨T₂, T₃, T₄, h23, h24, h34, h2M, h3M, h4M, hT⟩ := exists_three_twins S hloc hM'Ω'
  have hTmem : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) →
      T ∈ Ω' ∧ cnbhd Ω' T = cnbhd Ω' M' := fun T h => (hT T).mpr (Or.inr h)
  have hTout : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ outerSet Ω' N := fun T h =>
    twin_mem_outerSet (hTmem T h).1 (hTmem T h).2 hNM'
  have h2' : T₂ = T₂ ∨ T₂ = T₃ ∨ T₂ = T₄ := Or.inl rfl
  have h3' : T₃ = T₂ ∨ T₃ = T₃ ∨ T₃ = T₄ := Or.inr (Or.inl rfl)
  have h4' : T₄ = T₂ ∨ T₄ = T₃ ∨ T₄ = T₄ := Or.inr (Or.inr rfl)
  have hct : ∀ {T T'}, (T = T₂ ∨ T = T₃ ∨ T = T₄) → (T' = T₂ ∨ T' = T₃ ∨ T' = T₄) → T ≠ T' →
      Commutes T T' := fun hT1 hT2 hne =>
    commutes_of_twins (hTmem _ hT1).1 (hTmem _ hT1).2 (hTmem _ hT2).2 hne
  obtain ⟨hG2, hD4⟩ := G2D4.tag_ne_of_commuting_triple S.odd hΩ hex D (hall T₂ (hTout T₂ h2'))
    (hall T₃ (hTout T₃ h3')) (hall T₄ (hTout T₄ h4')) (hct h2' h3' h23) (hct h2' h4' h24)
    (hct h3' h4' h34)
  have hsc := fundamentalSingleClass_of_ne D i hG2 hD4
  obtain ⟨RN, hRN⟩ := exists_corr_left hΩ hex D hNi
  obtain ⟨RM, hRM⟩ := exists_corr_left hΩ hex D hM'i
  obtain ⟨g, hg⟩ := hsc RN hRN.2.1 RM hRM.2.1
  obtain ⟨ĝ, hĝ⟩ := QuotientGroup.mk_surjective (D.hom i g)
  have hĝY : (ĝ : G) ∈ locLayer Ω' u := ĝ.2
  have hK₁c : conjSub (ĝ : G) N ∈ compMembers Ω' u D i :=
    conjSub_mem_compMembers_of_mem_layer hΩ.conjInvariant hNi hĝY
  have himg1 : locImg Ω' u (conjSub (ĝ : G) N) = locImg Ω' u M' := by
    rw [locImg_conjSub_layer N ĝ, hRN.2.2, show locMk Ω' u ĝ = D.hom i g from hĝ, hRM.2.2, hg]
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp
  obtain ⟨zM, hzM⟩ := hΩ.classical M' hM'Ω'
  have hz₁ : IsClassicalMember p f (conjSub (ĝ : G) N) ((ĝ : G) * z₀ * (ĝ : G)⁻¹) :=
    hz₀.conj ĝ
  have hz₁Y : (ĝ : G) * z₀ * (ĝ : G)⁻¹ ∈ locLayer Ω' u := le_centralizingLayer hK₁c.1 hz₁.mem
  have hzMY : zM ∈ locLayer Ω' u := le_centralizingLayer hM'i.1 hzM.mem
  have heq := locMk_eq_of_involutions hΩ hex hK₁c.1 hM'i.1 himg1 hz₁ hzM hz₁Y hzMY
  have hz₁sq := mul_self_of_isClassicalMember hz₁
  have hzMsq := mul_self_of_isClassicalMember hzM
  have hzMi : zM⁻¹ = zM := inv_eq_of_mul_eq_one_right hzMsq
  have hmemO : (⟨zM, hzMY⟩⁻¹ * ⟨(ĝ : G) * z₀ * (ĝ : G)⁻¹, hz₁Y⟩ : ↥(locLayer Ω' u)) ∈
      classicalInvolutionOddCore ↥(locLayer Ω' u) := QuotientGroup.eq.mp heq.symm
  have hn : zM * ((ĝ : G) * z₀ * (ĝ : G)⁻¹) ∈ oddCoreIn (locLayer Ω' u) :=
    ⟨_, hmemO, by simp [hzMi]⟩
  obtain ⟨o, ho, hoeq⟩ := DeltaClosure.exists_conj_of_mul_mem hz₁sq hzMsq
    (odd_card_oddCoreIn (locLayer Ω' u)) hn
  have hoY : o ∈ locLayer Ω' u := oddCoreIn_le _ ho
  have hoO : (⟨o, hoY⟩ : ↥(locLayer Ω' u)) ∈ classicalInvolutionOddCore ↥(locLayer Ω' u) := by
    obtain ⟨o', ho', hoo'⟩ := ho
    have : o' = ⟨o, hoY⟩ := Subtype.ext hoo'
    rw [← this]
    exact ho'
  have hK₂c := conjSub_mem_compMembers_of_mem_layer hΩ.conjInvariant hK₁c hoY
  have himg2 : locImg Ω' u (conjSub o (conjSub (ĝ : G) N)) = locImg Ω' u (conjSub (ĝ : G) N) := by
    rw [locImg_conjSub_layer _ ⟨o, hoY⟩]
    have h1 : locMk Ω' u ⟨o, hoY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hoO
    rw [h1]
    ext a
    simp
  have hz₂ : IsClassicalMember p f (conjSub o (conjSub (ĝ : G) N)) zM := by
    have := hz₁.conj o
    rwa [← hoeq] at this
  rcases Bootstrap.members_eq_or_commute hz₂ hzM
    (Bootstrap.isQuasisimple_of_mem_exactMembers S.five hΩ hex hK₂c.1.1)
    (Bootstrap.isQuasisimple_of_mem_exactMembers S.five hΩ hex hM'Ω') with hK₂M | hcomm
  ·
    have hM'eq : M' = conjSub (o * (ĝ : G)) N := by
      rw [conjSub_mul]
      exact hK₂M.symm
    have hcY : o * (ĝ : G) ∈ locLayer Ω' u := (locLayer Ω' u).mul_mem hoY hĝY
    have hcC : o * (ĝ : G) ∈ Subgroup.centralizer ({u} : Set G) :=
      centralizingLayer_le_centralizer Ω' {u} hcY
    obtain ⟨T, hTΩ, hTN, g₀, hg₀T, hg₀⟩ := H3
    have hTM' : T ∈ outerSet Ω' M' := twin_mem_outerSet hTΩ hTN hM'
    have hTX : T ≤ outerGen Ω' M' := le_outerGen hTM'
    rw [hM'eq, outerGen_conj hΩ.conjInvariant (o * (ĝ : G)) N] at hTX
    have hg₀' := hTX hg₀T
    rw [mem_conjSub_iff] at hg₀'
    have hΘ : outerGen Ω' N ≤ Subgroup.centralizer ({u} : Set G) := iSup₂_le fun L hL => H1 L hL
    have hX : Commute u ((o * (ĝ : G))⁻¹ * g₀ * (o * (ĝ : G))) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hΘ hg₀')).symm
    have hcu : Commute u (o * (ĝ : G)) := (Subgroup.mem_centralizer_singleton_iff.mp hcC).symm
    have e : g₀ = (o * (ĝ : G)) * ((o * (ĝ : G))⁻¹ * g₀ * (o * (ĝ : G))) * (o * (ĝ : G))⁻¹ := by
      group
    apply hg₀
    rw [e]
    exact ((hcu.mul_right hX).mul_right hcu.inv_right).eq
  · exfalso
    refine locImg_not_commutative hΩ hex hM'i.1 ?_
    intro a ha b hb
    have ha' : a ∈ locImg Ω' u (conjSub o (conjSub (ĝ : G) N)) := by
      rw [himg2, himg1]
      exact ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha'
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    show locMk Ω' u a₀ * locMk Ω' u b₀ = locMk Ω' u b₀ * locMk Ω' u a₀
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcomm _ (Subgroup.mem_subgroupOf.mp ha₀) _ (Subgroup.mem_subgroupOf.mp hb₀)

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic
