module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmE189Red
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmE189Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace ThmE

section Nine


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.e189_false_of_swap (hr : 4 ≤ r) (hNo : NoQ16E4) (c : MinCex r Ω K S R W H) {z t k : G}
    (hz : IsUniqueInvolution K z) (htk : t = k * z * k⁻¹) (hkH : k ∈ H) (hzt : z * t = t * z)
    (htS : t ∈ (S : Subgroup G)) (hne : conjSub t K ≠ K) : False := by
  classical
  obtain ⟨Y, hYH, hKY, ⟨y₀, hy₀Y, hy₀⟩, hgenY⟩ := c.e189_exists_minimal hz htk hkH htS hne
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3 G Ω K S R W H c) c.stand.aEmpty
  have hHn : Nat.card H < Nat.card G := natCard_lt_of_ne_top c.proper
  have hlt : Nat.card Y < Nat.card G := lt_of_le_of_lt (Subgroup.card_le_of_le hYH) hHn
  have hT : Thm1RTwinInO2 r (Nat.card G) := thm1RTwinInO2_of_below hr hNo c.stand.ih.twin
  have hconjY : ∀ y : Y, conjSub (y : G) K ≤ Y := fun y => by
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  have hJY : conjSub k K ≤ Y := by
    rw [← hy₀]
    exact hconjY ⟨y₀, hy₀Y⟩
  have hmap : ∀ y : ↥Y, (conjSub y (K.subgroupOf Y)).map Y.subtype = conjSub (y : G) K := by
    intro y
    rw [conjSub_subgroupOf Y y K, Subgroup.map_subgroupOf_eq_of_le (hconjY y)]
  set Λ : Set (Subgroup ↥Y) := Set.range (fun y : ↥Y => conjSub y (K.subgroupOf Y)) with hΛdef
  have hΛsub : Λ ⊆ restrictFamily Ω Y := by
    rintro _ ⟨y, rfl⟩
    show conjSub y (K.subgroupOf Y) ∈ restrictFamily Ω Y
    rw [conjSub_subgroupOf]
    exact subgroupOf_mem_restrictFamily (hΩ.conjInvariant (y : G) K hK) (hconjY y)
  have hΛc : ConjInvariant Λ := by
    rintro g _ ⟨y, rfl⟩
    exact ⟨g * y, conjSub_mul _ _ _⟩
  have hΦ : HypOmegaGen (restrictFamily Ω Y) := hypOmegaGen_restrict hΩ Y
  have hΛ : HypOmegaGen Λ := TwinThmEW.hypOmegaGen_of_sub hΦ hΛsub hΛc
  have hq := fun L (hL : L ∈ Λ) => quat_restrict c.stand.quat Y L (hΛsub hL)
  have h2 := fun L (hL : L ∈ Λ) => TwinThmE.two_restrict c.stand.two Y L (hΛsub hL)
  have hA : ∀ L ∈ Λ, AEmpty Λ L :=
    TwinThmEW.aEmpty_of_sub hΦ hΛsub fun L hL => by
      obtain ⟨L₀, hL₀, hL₀Y, rfl⟩ := hL
      exact TwinThmEW.AEmpty.restrict hΩ hL₀Y (hAΩ L₀ hL₀)
  have hgen : (⨆ L ∈ Λ, L) = ⊤ := by
    have hmapΛ : (⨆ L ∈ Λ, L).map Y.subtype = ⨆ L ∈ Λ, L.map Y.subtype := by
      rw [Subgroup.map_iSup]
      congr 1
      funext L
      rw [Subgroup.map_iSup]
    apply Subgroup.map_injective Y.subtype_injective
    rw [hmapΛ, Subgroup.map_top, Subgroup.range_subtype]
    apply le_antisymm
    · refine iSup₂_le fun L hL => ?_
      obtain ⟨y, rfl⟩ := hL
      rw [hmap y]
      exact hconjY y
    · exact hgenY.symm.le.trans (iSup_le fun y => le_iSup₂_of_le (conjSub y (K.subgroupOf Y))
        ⟨y, rfl⟩ (le_of_eq (hmap y).symm))
  have hKΛ : K.subgroupOf Y ∈ Λ := ⟨1, conjSub_one _⟩
  have htr : ∀ L ∈ Λ, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = L := by
    rintro L ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have hzY : z ∈ Y := hKY hz.mem
  have hz' := isUniqueInvolution_subgroupOf hz hKY
  have hzJ : IsUniqueInvolution (conjSub k K) t := by
    have := hz.conj k
    rwa [← htk] at this
  have htY : t ∈ Y := hJY hzJ.mem
  have ht' := isUniqueInvolution_subgroupOf hzJ hJY
  have hzt' : (⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨z, hzY⟩ := Subtype.ext hzt
  have hJΛ : (conjSub k K).subgroupOf Y ∈ Λ := by
    refine ⟨⟨y₀, hy₀Y⟩, ?_⟩
    show conjSub (⟨y₀, hy₀Y⟩ : ↥Y) (K.subgroupOf Y) = (conjSub k K).subgroupOf Y
    rw [conjSub_subgroupOf]
    show (conjSub y₀ K).subgroupOf Y = _
    rw [hy₀]
  have hnorm := e189_section_no_swap hr hT hlt hΛ h2 hq hA hgen hKΛ htr hz' hJΛ ht' hzt'
  apply hne
  rw [conjSub_subgroupOf] at hnorm
  have hle : conjSub t K ≤ Y := by
    have := conjSub_mono (n := t) hKY
    rwa [conjSub_eq_self_of_mem htY] at this
  have := Subgroup.subgroupOf_inj.mp hnorm
  rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hKY] at this

theorem e18_9_of (hr : 4 ≤ r) (hNo : NoQ16E4) (h7 : E18_7 r) : E18_9 r := by
  intro G _ _ Ω K S R W H c z hz h htS htz hzt
  set t : G := h⁻¹ * z * h with ht
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hzH : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hz
  have ht2 : t * t = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [hz.sq]; group
  have hJ : conjSub h⁻¹ K ∈ Ω := hΩ.conjInvariant h⁻¹ K hK
  have hJt : IsUniqueInvolution (conjSub h⁻¹ K) t := by
    have := hz.conj h⁻¹
    simpa [ht] using this
  have hzt' : z * t = t * z := hzt
  have ha2 : (z * t) * (z * t) = 1 := mul_involution_of_commute hz.sq ht2 hzt'
  have ha1 : z * t ≠ 1 := by
    intro h1
    apply htz
    have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, inv_eq_of_mul_eq_one_right hz.sq]
  have hzfix : FixesUniqueCoset z H :=
    fixesUniqueCoset_of_centralizer_le hzH (h7 G Ω K S R W H c z hz.ne_one hz.sq hzH)
  have htH : t ∈ H := hzH (Subgroup.mem_centralizer_singleton_iff.mpr hzt'.symm)
  by_cases hnorm : conjSub t K = K
  · rcases TwinThmEW.e189_caseA hΩ hK hJ hz hJt htz hzt' hnorm with ⟨g, hg⟩ | hperp
    · have e : g * t * g⁻¹ = (g * h⁻¹) * z * (g * h⁻¹)⁻¹ := by rw [ht]; group
      rw [← hg, e]
      exact fixesUniqueCoset_conj hzfix _
    · have hne : conjSub h⁻¹ K ≠ K := fun h' => htz (hJt.eq (by rw [h']; exact hz))
      have hnbr : conjSub h⁻¹ K ∈ omegaNbr Ω K := hperp.resolve_left hne
      have hca := TwinThmEW.centralizer_le_mul_of_omegaNbr hΩ hK c.hyp.trans hz hzH
        c.stand.hR.1 c.stand.hR.2.1 c.stand.hR.2.2 c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2
        c.hyp.cent hnbr hJt ha1 ha2
      exact fixesUniqueCoset_of_centralizer_le hca (h7 G Ω K S R W H c _ ha1 ha2 hca)
  · obtain ⟨k, hkH, hk⟩ := h7 G Ω K S R W H c z hz.ne_one hz.sq hzH h⁻¹
      (by simpa [ht] using htH)
    have hkt : k * z * k⁻¹ = t := by rw [hk, ht]; simp
    exact (c.e189_false_of_swap hr hNo hz hkt.symm hkH hzt' htS hnorm).elim

end Nine

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
