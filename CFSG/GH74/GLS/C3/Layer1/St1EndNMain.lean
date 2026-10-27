module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNBarB
public import CFSG.GH74.GLS.C3.Layer1.St1EndNComp
public import CFSG.GH74.GLS.C3.Layer1.St1EndN
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
public import CFSG.GH74.GLS.C3.Layer1.St1EndNLeaves

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.Th2.IV26 CFSG.GH74.GLS.C3.Layer1.EndN
open scoped commutatorElement

theorem b_st1_prop71_endN_of_leaves
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) (hW : B_st1_prop71_lemma710)
    (hX : B_st1_prop71_lemma711) : B_st1_prop71_endN := by
  intro G _ _ hG hNoU T7 P41 T4 A M S hA hcore hM hMN hS hAS hMP x y K hxyK hT hy hKM hL29 h1 hc
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  obtain ⟨hstar, -, -, -⟩ := terminallyUnbalancing_L29 h102 h14 hL34 hadd hG hNoU P41 hxyK
  have hunb : IsUnbalancingTriple x y K := hxyK.unbalancing
  have hxK : IsIL2Pair x K := hunb.1
  have hx2 : orderOf x = 2 := hxK.1
  have hy2 : orderOf y = 2 := hunb.2.1
  have hyx : y * x = x * y := mem_centralizer_singleton_iff.1 hunb.2.2.1
  have hLodd : HasL2Model (kBar K) Odd :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => by rw [hq]; exact ⟨4, rfl⟩) hL29
  have hxS : x ∈ S := by
    refine (C3.Layer1.Iv251.mem_of_isSylowOf_of_central hT (mem_centralizer_singleton_iff.2 rfl) hx2
      (fun c hc' => (mem_centralizer_singleton_iff.1 hc').symm) : x ∈ S ⊓ centralizer ({x} : Set G)).1
  have hSM : S ≤ M := hS.le
  have hxM : x ∈ M := hSM hxS
  have hyM : y ∈ M := hSM hy
  have hMtop : M ≠ ⊤ := hM.1
  have hx'2 : orderOf (eb M hxM) = 2 := orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2)
  have hy'2 : orderOf (eb M hyM) = 2 := orderOf_barMk ((Subgroup.orderOf_mk y hyM).trans hy2)
  have hxy' : eb M hxM * eb M hyM = eb M hyM * eb M hxM := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyx.symm
  have hxcomm : ∀ k ∈ imgM M K, eb M hxM * k = k * eb M hxM := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hk
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hxK.2.1 hm)).symm
  have hMb : IsKGroupNative (Mb M) := isKGroupNative_Mb hG.kproper hMtop
  have hcoreMb : pPrimeCore 2 (Mb M) = ⊥ := pPrimeCore_Mb_eq_bot M
  have hKcomp : IsCompIn (centralizer ({eb M hxM} : Set (Mb M))) (imgM M K) :=
    isCompIn_imgM_at_x hxM hx2 hKM hxK.2 (isComponent_of_B2 hB2 (gen4_Mb hG.gen4 M) hMb hcoreMb hx'2)
  have hKq : CFSG.IsQuasisimple ↥(imgM M K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKcomp.1) hKcomp.2.1
  have hL9 := hasL2Model_imgM hKM hL29
  have hhform := hform_Mb hr4.le hxK hLodd h1.le hxM hKM
  have hterminal : IsTerminalSub (imgM M K) :=
    isTerminalSub_of_unique_involution hx'2 hxcomm hKcomp hhform
  have hW' := hW G hG hNoU T7 P41 T4 A M S hA hcore hM hMN hS hAS hMP x y K hxyK hT hy hKM hL29 h1
  have h2 := unbal_Mb hr4.le hxK hLodd hxM hyM hy2 hKM hW'
  obtain ⟨h3, h4'⟩ := rank_facts hr4 hxM hSM hT hstar
  have h4 : pRank 2 ↥(centralizer ({eb M hxM} : Set (Mb M))) = pRank 2 (Mb M) →
      eb M hxM ∈ ⁅(⊤ : Subgroup (Mb M)), (⊤ : Subgroup (Mb M))⁆ :=
    fun _ => eb_mem_commutator_top hxM (hMP.comm_star x hxM hx2 h4')
  have hgen4 : Gen4 (Mb M) := Gen4.quotient _ (Gen4.subgroup M hG.gen4)
  have hGH : ∀ L : Subgroup (Mb M), IsSimpleSocle L ⊤ → GHList ↥L := by
    intro L hL
    have hnc : ∃ a b : ↥L, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have := hL.simple
      obtain ⟨a, ha1⟩ := exists_ne (1 : ↥L)
      apply ha1
      apply Subtype.ext
      exact hL.centralizer_trivial a (Subgroup.mem_top _)
        (fun h hh => congrArg Subtype.val (hcon a ⟨h, hh⟩))
    exact IVK.ghList_of_subgroup_of_quotient hG.kgh hMtop (barMk ↥M) barMk_surjective L hL.simple hnc
  by_cases hsub : (imgM M K).IsSubnormal
  · have hP : IsPGroup 2 ↥(imgM M S) := by
      obtain ⟨e⟩ := equiv_imgM hSM hS.isPGroup
      exact hS.isPGroup.of_equiv e
    have hxP : eb M hxM ∈ imgM M S := mem_imgM_iff.2 ⟨⟨x, hxM⟩, hxS, rfl⟩
    have hcen := central_of_subnormal_component hP hxP hx'2 hKq hsub hxcomm (two_le_pRank_imgM hKM hL29)
      (no_involution_center_imgM hKM hL29) hhform
    obtain ⟨s, hsS, hxs⟩ := hc
    apply hxs
    have hsM : s ∈ M := hSM hsS
    have h' := hcen (barMk ↥M ⟨s, hsM⟩) (mem_imgM_iff.2 ⟨⟨s, hsM⟩, hsS, rfl⟩)
    have h'' : barMk ↥M ((⟨x, hxM⟩ : ↥M) * ⟨s, hsM⟩) = barMk ↥M ((⟨s, hsM⟩ : ↥M) * ⟨x, hxM⟩) := by
      rw [map_mul, map_mul]
      exact h'
    have hker : (((⟨x, hxM⟩ : ↥M) * ⟨s, hsM⟩)⁻¹ * (⟨s, hsM⟩ * ⟨x, hxM⟩) : ↥M) ∈ pPrimeCore 2 ↥M := by
      rw [← ker_barMk (Y := ↥M), MonoidHom.mem_ker, map_mul, map_inv, h'', inv_mul_cancel]
    have hw : (x * s)⁻¹ * (s * x) ∈ S ⊓ pPrimeCoreOf 2 M := by
      refine ⟨S.mul_mem (S.inv_mem (S.mul_mem hxS hsS)) (S.mul_mem hsS hxS), ⟨_, hker, rfl⟩⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot M hS.isPGroup, Subgroup.mem_bot] at hw
    exact inv_mul_eq_one.1 hw
  · exact hsub (hX (Mb M) hgen4 hMb hcoreMb hGH (imgM M K) (eb M hxM) (eb M hyM) hx'2 hy'2 hxy'
      hKcomp hL9 hterminal hhform h2 h3 h4)

theorem b_st1_prop71_endB_of_leaves
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) (hW : B_st1_prop71_lemma710)
    (hX : B_st1_prop71_lemma711) : B_st1_prop71_endB :=
  b_st1_prop71_endB_of_endN h102 h14 hL34 hadd
    (b_st1_prop71_endN_of_leaves h102 h14 hL34 hadd hB2 hW hX)

end CFSG.GH74.GLS
