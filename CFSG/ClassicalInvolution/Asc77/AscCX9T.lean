module

public import CFSG.ClassicalInvolution.Asc77.AscCX9S
public import CFSG.ClassicalInvolution.Asc77.AscCX9R

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Gen

variable {G : Type} [Group G] [Finite G]

theorem oddCore_eq_bot_of_simple {T : Type} [Group T] [Finite T] [IsSimpleGroup T] {t : T}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : classicalInvolutionOddCore T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (classicalInvolutionOddCore T) with h | h
  · exact h
  · exfalso
    have htO : t ∈ classicalInvolutionOddCore T := by
      rw [h]
      exact Subgroup.mem_top t
    exact ht1 (T7H.eq_one_of_mem_odd_of_sq (CFSG.ComponentClassification.OddCore.odd_card T)
      htO ht2)

theorem odd_natCard_ker_toLayer {X H : Subgroup G} (hHX : H ≤ X) :
    Odd (Nat.card ((QuotientGroup.mk' (classicalInvolutionOddCore ↥X)).comp
      (Subgroup.inclusion hHX)).ker) := by
  have hle : ((QuotientGroup.mk' (classicalInvolutionOddCore ↥X)).comp
      (Subgroup.inclusion hHX)).ker.map H.subtype ≤ oddCoreOf X := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hHX m) =
        1 := hm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm'
    exact Subgroup.mem_map_of_mem X.subtype hm'
  have hO : Odd (Nat.card (oddCoreOf X)) := by
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥X
  rw [← Subgroup.card_map_of_injective H.subtype_injective]
  exact hO.of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem exists_equiv_of_ker_eq {H T T' : Type} [Group H] [Group T] [Group T'] (ρ : H →* T)
    (ρ' : H →* T') (hρ : Function.Surjective ρ) (hρ' : Function.Surjective ρ')
    (hker : ρ.ker = ρ'.ker) : ∃ φ : T ≃* T', ∀ h, φ (ρ h) = ρ' h := by
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ' hρ')), fun h => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm (ρ h) =
      (QuotientGroup.mk h : H ⧸ ρ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  rfl

end Gen

section Pkg

variable {G : Type} [Group G] [Finite G]

structure LayerPkg (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z w : G) : Prop where
  zY : z ∈ exactLayer Ω w
  tq : K ∈ tqMembers Ω w
  tq' : K' ∈ tqMembers Ω w
  odd : oddCoreOf (T7H.exactImg Ω w K) = ⊥
  odd' : oddCoreOf (T7H.exactImg Ω w K') = ⊥
  cov : ∀ x ∈ K, ∃ i ∈ exactCore w K, ∃ n ∈ oddCoreIn K, x = i * n
  cov' : ∀ x ∈ K', ∃ i ∈ exactCore w K', ∃ n ∈ oddCoreIn K', x = i * n

noncomputable abbrev vtx {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z w : G}
    (P : LayerPkg Ω K K' z w)
    (β : MulAut (↥(exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w)))
    (hA : T7H.exactImg Ω w K ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : T7H.exactImg Ω w K' ≤ Goldschmidt75.perfRes (fixSubgroup β)) :
    TwinGroup (↥K ⧸ classicalInvolutionOddCore ↥K) (↥K' ⧸ classicalInvolutionOddCore ↥K') :=
  (centTG _ _ β hA hA').rebase (twinEquiv P.tq P.cov P.odd) (twinEquiv P.tq' P.cov' P.odd')

theorem perfRes_normalizes {Ω : Set (Subgroup G)} (hc : ConjInvariant Ω) {w w' n h : G}
    (hn : n ∈ Goldschmidt75.perfRes (exactLayer Ω w ⊓ Subgroup.centralizer ({w'} : Set G)))
    (hh : h ∈ Goldschmidt75.perfRes (exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G))) :
    n * h * n⁻¹ ∈
      Goldschmidt75.perfRes (exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G)) := by
  have hn' := Goldschmidt75.perfRes_le _ hn
  have hnC' : n ∈ Subgroup.centralizer ({w'} : Set G) := hn'.2
  have hnC : n ∈ Subgroup.centralizer ({w} : Set G) := exactLayer_le_centralizer Ω w hn'.1
  have hconj : conjSub n (exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G)) =
      exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G) := by
    unfold conjSub
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective]
    change conjSub n (exactLayer Ω w') ⊓ conjSub n (Subgroup.centralizer ({w} : Set G)) = _
    rw [conjSub_exactLayer hc hnC', conjSub_eq_self_of_mem hnC]
  have hnN := Goldschmidt75.normalizer_le_normalizer_perfRes _
    (mem_normalizer_iff_conjSub_eq.mpr hconj)
  exact (Subgroup.mem_normalizer_iff.mp hnN h).mp hh

end Pkg

section Bad

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem layerPkg_of_bad (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {w : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G))) :
    LayerPkg Ω K K' z w := by
  have hs := hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hzY, hK₂, hK₂', -, hO, hO', -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  have hc₁ : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hs.stand.mem hs.hz
  have hc₂ : IsClassicalMember p f K' z :=
    isClassicalMember_of_twin hΩ hs.hK'.1 (isUniqueInvolution_of_mem_twinSet hs.hz hs.hK')
  have hw2' := isPGroup_zpowers_of_sq_eq_one hw2
  exact ⟨hzY, hK₂, hK₂', hO, hO', exactCore_cover hc₁ hw2' hK₂.2,
    exactCore_cover hc₂ hw2' hK₂'.2⟩

theorem twinIso_vtx (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {w w' : G}
    (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw'A : w' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw'2 : w' * w' = 1) (hw'C : w' ∈ Subgroup.centralizer ({w} : Set G))
    (hwC : w ∈ Subgroup.centralizer ({w'} : Set G)) (P : LayerPkg Ω K K' z w)
    (P' : LayerPkg Ω K K' z w')
    {β : MulAut (↥(exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w))}
    (hβ : β = actW hyp.std.setting.stand.hyp.conjInvariant w ⟨w', hw'C⟩)
    {β' : MulAut (↥(exactLayer Ω w') ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w'))}
    (hβ' : β' = actW hyp.std.setting.stand.hyp.conjInvariant w' ⟨w, hwC⟩)
    (hA : T7H.exactImg Ω w K ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : T7H.exactImg Ω w K' ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : T7H.exactImg Ω w' K ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : T7H.exactImg Ω w' K' ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (h5 : IsOm5 p f (centTG _ _ β hA hA')) (h5' : IsOm5 p f (centTG _ _ β' hB hB')) :
    TwinIso p (vtx P β hA hA') (vtx P' β' hB hB') := by
  classical
  subst hβ hβ'
  have hs := hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hz1 : z ≠ 1 := hs.hz.ne_one
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  set F := Subgroup.closure ({w, w'} : Set G) with hF
  have hFA := closure_pair_le hwA hw'A
  have hF2 : IsPGroup 2 F := S.isPGroup'.to_le (hFA.trans inf_le_left)
  have hwF : w ∈ F := Subgroup.subset_closure (Set.mem_insert w _)
  have hw'F : w' ∈ F := Subgroup.subset_closure (Set.mem_insert_of_mem w rfl)
  have hcK : ⁅F, K⁆ ≤ oddCoreOf K := Subgroup.commutator_le.mpr fun a ha x hx =>
    (mem_trivialOnQuot_of_mem_A hyp (hFA ha)).1.2 x hx
  have hcK' : ⁅F, K'⁆ ≤ oddCoreOf K' := Subgroup.commutator_le.mpr fun a ha x hx =>
    (mem_trivialOnQuot_of_mem_A hyp (hFA ha)).2.2 x hx
  have hw2' := isPGroup_zpowers_of_sq_eq_one hw2
  have hw'2' := isPGroup_zpowers_of_sq_eq_one hw'2
  set N := Goldschmidt75.perfRes (exactLayer Ω w ⊓ Subgroup.centralizer ({w'} : Set G))
    with hN
  set N' := Goldschmidt75.perfRes (exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G))
    with hN'
  have hNX : N ≤ exactLayer Ω w := (Goldschmidt75.perfRes_le _).trans inf_le_left
  have hN'X : N' ≤ exactLayer Ω w' := (Goldschmidt75.perfRes_le _).trans inf_le_left
  have hsec : ∀ {J : Subgroup G}, J ∈ Ω → ⁅F, J⁆ ≤ oddCoreOf J →
      AscE184Sect.secMember F J ≤ exactCore w J → AscE184Sect.secMember F J ≤ exactCore w' J →
      J ∈ tqMembers Ω w → J ∈ tqMembers Ω w' → AscE184Sect.secMember F J ≤ N ⊓ N' := by
    intro J hJ hcJ h1 h2 hq1 hq2
    have hperf : ⁅AscE184Sect.secMember F J, AscE184Sect.secMember F J⁆ =
        AscE184Sect.secMember F J :=
      Subgroup.isPerfect_iff.mp (AscE184Sect.secMember_perfect hΩ hF2 hJ hcJ)
    have hC := AscE184Sect.secMember_le_centralizer F J
    exact le_inf (Goldschmidt75.le_perfRes (le_inf (h1.trans (exactCore_le_exactLayer hq1))
        (hC.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw'F)))) hperf)
      (Goldschmidt75.le_perfRes (le_inf (h2.trans (exactCore_le_exactLayer hq2))
        (hC.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwF)))) hperf)
  have hKw := secMember_le_exactCore hΩ hwF hw2' hKΩ P.tq.2
  have hKw' := secMember_le_exactCore hΩ hw'F hw'2' hKΩ P'.tq.2
  have hLw := secMember_le_exactCore hΩ hwF hw2' hK'Ω P.tq'.2
  have hLw' := secMember_le_exactCore hΩ hw'F hw'2' hK'Ω P'.tq'.2
  have hsecK := hsec hKΩ hcK hKw hKw' P.tq P'.tq
  have hsecK' := hsec hK'Ω hcK' hLw hLw' P.tq' P'.tq'
  have hzH : z ∈ N ⊓ N' :=
    hsecK (AscE184Sect.isUniqueInvolution_secMember hs.stand.odd hΩ hF2 hKΩ hcK hs.hz).mem
  have hHX : N ⊓ N' ≤ exactLayer Ω w := inf_le_left.trans hNX
  have hHX' : N ⊓ N' ≤ exactLayer Ω w' := inf_le_right.trans hN'X
  have hNT : (N.subgroupOf (exactLayer Ω w)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w))) =
      Goldschmidt75.perfRes
        (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w ⟨w', hw'C⟩)) :=
    map_perfRes_fix_eq hw'2 (conjSub_exactLayer hΩ.conjInvariant hw'C)
  have hNT' : (N'.subgroupOf (exactLayer Ω w')).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w'))) =
      Goldschmidt75.perfRes
        (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w' ⟨w, hwC⟩)) :=
    map_perfRes_fix_eq hw2 (conjSub_exactLayer hΩ.conjInvariant hwC)
  have hρmem : ∀ h : ↥(N ⊓ N'),
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w)) (Subgroup.inclusion hHX h) ∈
        Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w ⟨w', hw'C⟩)) := by
    intro h
    rw [← hNT]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h.2.1)
  have hρmem' : ∀ h : ↥(N ⊓ N'),
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w'))
          (Subgroup.inclusion hHX' h) ∈
        Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w' ⟨w, hwC⟩)) := by
    intro h
    rw [← hNT']
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h.2.2)
  set ρ := ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w))).comp
    (Subgroup.inclusion hHX)).codRestrict _ hρmem with hρ
  set ρ' := ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w'))).comp
    (Subgroup.inclusion hHX')).codRestrict _ hρmem' with hρ'
  have hTs : IsSimpleGroup ↥(Goldschmidt75.perfRes
      (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w ⟨w', hw'C⟩))) := by
    obtain ⟨Φ, z', a₀, b₀, hd⟩ := h5
    exact isSimpleGroup_of_om5Data hd
  have hT's : IsSimpleGroup ↥(Goldschmidt75.perfRes
      (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w' ⟨w, hwC⟩))) := by
    obtain ⟨Φ, z', a₀, b₀, hd⟩ := h5'
    exact isSimpleGroup_of_om5Data hd
  have hzz : (⟨z, hzH⟩ : ↥(N ⊓ N')) * ⟨z, hzH⟩ = 1 := Subtype.ext hz2
  have hρz : ρ ⟨z, hzH⟩ ≠ 1 := fun h =>
    mk_ne_one_of_involution P.zY hz2 hz1 (congrArg Subtype.val h)
  have hρ'z : ρ' ⟨z, hzH⟩ ≠ 1 := fun h =>
    mk_ne_one_of_involution P'.zY hz2 hz1 (congrArg Subtype.val h)
  have hρsurj : Function.Surjective ρ := by
    have hnorm : ρ.range.Normal := by
      constructor
      rintro _ ⟨h, rfl⟩ g
      have hg : (g : ↥(exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w)) ∈
          (N.subgroupOf (exactLayer Ω w)).map
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w))) := by
        rw [hNT]
        exact g.2
      obtain ⟨x₀, hx₀, hx₀g⟩ := Subgroup.mem_map.mp hg
      have hx₀N : (x₀ : G) ∈ N := Subgroup.mem_subgroupOf.mp hx₀
      have hmem : (x₀ : G) * h * (x₀ : G)⁻¹ ∈ N ⊓ N' :=
        ⟨N.mul_mem (N.mul_mem hx₀N h.2.1) (N.inv_mem hx₀N),
          perfRes_normalizes hΩ.conjInvariant hx₀N h.2.2⟩
      refine ⟨⟨_, hmem⟩, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hx₀g]
      change QuotientGroup.mk' _ (Subgroup.inclusion hHX ⟨_, hmem⟩) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w)) x₀ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w))
            (Subgroup.inclusion hHX h) *
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w)) x₀)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.range with h | h
    · exfalso
      have h1 : ρ ⟨z, hzH⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact hρz h1
    · exact MonoidHom.range_eq_top.mp h
  have hρ'surj : Function.Surjective ρ' := by
    have hnorm : ρ'.range.Normal := by
      constructor
      rintro _ ⟨h, rfl⟩ g
      have hg : (g : ↥(exactLayer Ω w') ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w')) ∈
          (N'.subgroupOf (exactLayer Ω w')).map
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w'))) := by
        rw [hNT']
        exact g.2
      obtain ⟨x₀, hx₀, hx₀g⟩ := Subgroup.mem_map.mp hg
      have hx₀N : (x₀ : G) ∈ N' := Subgroup.mem_subgroupOf.mp hx₀
      have hmem : (x₀ : G) * h * (x₀ : G)⁻¹ ∈ N ⊓ N' :=
        ⟨perfRes_normalizes hΩ.conjInvariant hx₀N h.2.1,
          N'.mul_mem (N'.mul_mem hx₀N h.2.2) (N'.inv_mem hx₀N)⟩
      refine ⟨⟨_, hmem⟩, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hx₀g]
      change QuotientGroup.mk' _ (Subgroup.inclusion hHX' ⟨_, hmem⟩) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w')) x₀ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w'))
            (Subgroup.inclusion hHX' h) *
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w')) x₀)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ'.range with h | h
    · exfalso
      have h1 : ρ' ⟨z, hzH⟩ ∈ ρ'.range := ⟨_, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact hρ'z h1
    · exact MonoidHom.range_eq_top.mp h
  have hO1 := oddCore_eq_bot_of_simple (t := ρ ⟨z, hzH⟩) (by rw [← map_mul, hzz, map_one]) hρz
  have hO2 := oddCore_eq_bot_of_simple (t := ρ' ⟨z, hzH⟩) (by rw [← map_mul, hzz, map_one]) hρ'z
  have hk1 : ρ.ker = classicalInvolutionOddCore ↥(N ⊓ N') :=
    ker_eq_oddCore_of_surjective ρ hρsurj hO1 (by
      rw [hρ, MonoidHom.ker_codRestrict]
      exact odd_natCard_ker_toLayer hHX)
  have hk2 : ρ'.ker = classicalInvolutionOddCore ↥(N ⊓ N') :=
    ker_eq_oddCore_of_surjective ρ' hρ'surj hO2 (by
      rw [hρ', MonoidHom.ker_codRestrict]
      exact odd_natCard_ker_toLayer hHX')
  obtain ⟨φ, hφ⟩ := exists_equiv_of_ker_eq ρ ρ' hρsurj hρ'surj (hk1.trans hk2.symm)
  refine twinIso_of_compat φ (fun k => ?_) (fun k => ?_)
  · obtain ⟨m, rfl⟩ := AscE184Sect.secQuotMap_surjective hΩ hF2 hKΩ hcK k
    have e1 : ((vtx P _ hA hA').ι (AscE184Sect.secQuotMap F K m) : (vtx P _ hA hA').X) =
        ρ ⟨m, hsecK m.2⟩ := by
      apply Subtype.ext
      exact twinEquiv_mk P.tq P.cov P.odd (hKw m.2)
    have e2 : ((vtx P' _ hB hB').ι (AscE184Sect.secQuotMap F K m) : (vtx P' _ hB hB').X) =
        ρ' ⟨m, hsecK m.2⟩ := by
      apply Subtype.ext
      exact twinEquiv_mk P'.tq P'.cov P'.odd (hKw' m.2)
    exact (congrArg φ e1).trans ((hφ ⟨m, hsecK m.2⟩).trans e2.symm)
  · obtain ⟨m, rfl⟩ := AscE184Sect.secQuotMap_surjective hΩ hF2 hK'Ω hcK' k
    have e1 : ((vtx P _ hA hA').ι' (AscE184Sect.secQuotMap F K' m) : (vtx P _ hA hA').X) =
        ρ ⟨m, hsecK' m.2⟩ := by
      apply Subtype.ext
      exact twinEquiv_mk P.tq' P.cov' P.odd' (hLw m.2)
    have e2 : ((vtx P' _ hB hB').ι' (AscE184Sect.secQuotMap F K' m) : (vtx P' _ hB hB').X) =
        ρ' ⟨m, hsecK' m.2⟩ := by
      apply Subtype.ext
      exact twinEquiv_mk P'.tq' P'.cov' P'.odd' (hLw' m.2)
    exact (congrArg φ e1).trans ((hφ ⟨m, hsecK' m.2⟩).trans e2.symm)

end Bad

end CFSG.ClassicalInvolution.Asc77.CX
