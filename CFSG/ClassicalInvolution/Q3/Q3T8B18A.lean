module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

section E4World


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_rep_of_meets_sylow (hP : PartIHyp Ω) {S₂ : Sylow 2 G} {η₂ : Set (Subgroup G)}
    (hη₂ : η₂ ∈ etaSet Ω (S₂ : Subgroup G))
    (hinv₂ : ∀ s ∈ (S₂ : Subgroup G), ∀ U ∈ η₂, conjSub s U ∈ η₂)
    {L : Subgroup G} (hL : L ∈ Ω) (hcard : 2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G))) :
    ∃ ρ : Rep Ω (⨆ U ∈ η₂, U : Subgroup G), ρ.K = L := by
  have hΩ : HypOmegaMod Ω := hP.hyp
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  have hW₂ : (⨆ U ∈ η₂, U : Subgroup G) ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup G) := fun V hV => (hη₂.1 hV).2
  have c₂ : Q3CL.Thompson.Ctx Ω (⨆ U ∈ η₂, U : Subgroup G) := MuTab.muTabCtx hP hW₂
  have h611 : L ⊓ (⨆ U ∈ η₂, U : Subgroup G) ∈ η₂ :=
    l6_11_proved G Ω hΩ S₂ η₂ hη₂G hηS L hL hcard
  have hV₀U : L ⊓ (⨆ U ∈ η₂, U : Subgroup G) ∈ USet Ω := (hη₂.1 h611).1
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hL
  have hV₀2 : IsPGroup 2 ↥(L ⊓ (⨆ U ∈ η₂, U : Subgroup G)) := hΩ.isPGroup_of_mem_USet hV₀U
  have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ (⨆ U ∈ η₂, U : Subgroup G)) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hV₀U
    exact h4
  have hzLV : zL ∈ L ⊓ (⨆ U ∈ η₂, U : Subgroup G) :=
    T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
  exact c₂.exists_rep_of_involution_mem hP.cls hL hzL hzLV.2

theorem muIsoE4_of_mem_WSet (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W) {W₂ : Subgroup G}
    (hW₂ : W₂ ∈ WSet Ω) : MuIsoE4 Ω W₂ := by
  obtain ⟨φ⟩ := hE
  obtain ⟨e⟩ := l7_5_2_proved G Ω hs.stand.modU W₂ hW₂ W hs.hW.1
  exact ⟨e.trans φ⟩

theorem omegaStarNbr_imp_omegaNbr_E4 (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {X M : Subgroup G} (hX : X ∈ Ω) (hM : M ∈ omegaStarNbr Ω X) : M ∈ omegaNbr Ω X := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hP : PartIHyp Ω := T8.partIHyp_of_std8 hs
  obtain ⟨hMΩ, hMX, U, hU, hUM, hUN⟩ := hM
  have hU2 : IsPGroup 2 ↥U := hΩ.isPGroup_of_mem_USet hU
  have hU4 : 4 ≤ Nat.card ↥U := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
    exact h4
  obtain ⟨R₀, hR₀, hR₀fix⟩ := exists_sylow_normalized hU2 hUN
  have hR₀set : R₀ ∈ RSet Ω := mem_RSet_of_isSylow2In hX hR₀
  have hUn : U ≤ Subgroup.normalizer (R₀ : Set G) := fun a ha =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₀fix a ha)
  have hUR : IsPGroup 2 ↥(U ⊔ R₀) := hU2.to_sup_of_normal_right' hR₀.2.1 hUn
  obtain ⟨S₂, hS₂⟩ := hUR.exists_le_sylow
  obtain ⟨η₂, hη₂, hinv₂⟩ := Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΩ S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  have hW₂ : (⨆ U ∈ η₂, U : Subgroup G) ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hE₂ := muIsoE4_of_mem_WSet hs hE hW₂
  have hcardX : 2 < Nat.card ↥(X ⊓ (S₂ : Subgroup G)) := by
    have h8 := hΩ.eight_le_of_mem_RSet hR₀set
    have h1 := Subgroup.card_le_of_le (le_inf hR₀.1 (le_sup_right.trans hS₂))
    omega
  have hcardM : 2 < Nat.card ↥(M ⊓ (S₂ : Subgroup G)) := by
    have h1 := Subgroup.card_le_of_le (le_inf hUM (le_sup_left.trans hS₂))
    omega
  obtain ⟨ρX, hρX⟩ := exists_rep_of_meets_sylow hP hη₂ hinv₂ hX hcardX
  obtain ⟨ρM, hρM⟩ := exists_rep_of_meets_sylow hP hη₂ hinv₂ hMΩ hcardM
  have hcomm : ∀ x y : ↥(muGroup Ω (⨆ U ∈ η₂, U : Subgroup G)), x * y = y * x := by
    obtain ⟨φ⟩ := hE₂
    intro x y
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hne : ρX.K ≠ ρM.K := by
    rw [hρX, hρM]
    exact fun h => hMX h.symm
  have h := (MuTab.muTab_commute_iff hP hW₂ ρX ρM hne).mp (hcomm _ _)
  rwa [hρX, hρM] at h

theorem no_common_nbr_E4 (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    (h28 : ∀ {L : Subgroup G} {u : G}, L ∈ omegaNbr Ω K → L ∈ omegaNbr Ω J →
      IsUniqueInvolution L u → u = z * t)
    {L : Subgroup G} (hLK : L ∈ omegaNbr Ω K) (hLJ : L ∈ omegaNbr Ω J) : False := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hP : PartIHyp Ω := T8.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hLK.1
  have huzt : u = z * t := h28 hLK hLJ hu
  have hzW : z ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hK (T8.stdRepK hs).hR
    (T8.stdRepK hs).hRK hs.hz).2
  have htW : t ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hs.hJ.1 (T8.stdRepJ hs).hR
    (T8.stdRepJ hs).hRK hs.ht).2
  have hztW : z * t ∈ W := W.mul_mem hzW htW
  have c : Q3CL.Thompson.Ctx Ω W := MuTab.muTabCtx hP hW
  obtain ⟨ρL, hρL⟩ := c.exists_rep_of_involution_mem hs.stand.cls hLK.1 hu (huzt ▸ hztW)
  refine T8W.no_three_reps_E4 hP hW hE (T8.stdRepK hs) (T8.stdRepJ hs) ρL ?_ ?_ ?_
  · exact fun h => hs.hJ.2.1 h.symm
  · rw [hρL]
    exact fun h => hLK.2.1 h.symm
  · rw [hρL]
    exact fun h => hLJ.2.1 h.symm

end E4World

end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
