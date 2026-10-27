module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB2z
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Layer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y}

private theorem nf5_pCore_le_F (h : NF5 F Γ B R₀ x) : CFSG.pCore 5 Y ≤ F := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, hP, hdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff (p := 5)).mp h.sylow
  rw [Subgroup.relIndex_top_right] at hdvd
  have hS : ((hP.toSylow hdvd : Sylow 5 Y) : Subgroup Y) = F := IsPGroup.toSylow_coe hP hdvd
  rw [← hS]
  exact (CFSG.pCore_isPGroup (p := 5) (G := Y)).le_sylow_of_normal _

private theorem nf5_comp_le_centralizer_pCore {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    L ≤ Subgroup.centralizer (CFSG.pCore 5 Y : Set Y) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hRn : (CFSG.pCore 5 Y).Normal := CFSG.pCore_normal
  haveI : Group.IsNilpotent (CFSG.pCore 5 Y) := (CFSG.pCore_isPGroup (p := 5)).isNilpotent
  haveI : Group.IsSolvable (CFSG.pCore 5 Y) := inferInstance
  have hsub : IsSubnormal (CFSG.pCore 5 Y) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hRn.isSubnormal
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal L
      (CFSG.pCore 5 Y) hL hsub)

theorem nf5_pCore_bot (h : NF5 F Γ B R₀ x)
    (hZ : ∀ L : Subgroup Y, IsComponentOf L ⊤ → Subgroup.center ↥L = ⊥) {z : Y} (hz : NF5Z F z)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : CFSG.pCore 5 Y = ⊥ := by
  by_contra hne
  haveI hRn : (CFSG.pCore 5 Y).Normal := CFSG.pCore_normal
  have hzP : z ∈ CFSG.pCore 5 Y :=
    nf5_normal_contains h hz (nf5_pCore_le_F h) (fun f _ n hn => hRn.conj_mem n hn f) hne
  have hLC := nf5_comp_le_centralizer_pCore hL
  have hzL : z ∈ L := nf5_z_mem_comp h hZ hz hL
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := hLC g.2
    rw [Subgroup.mem_centralizer_iff] at hg
    exact Subtype.ext (hg z hzP).symm
  rw [hZ L hL, Subgroup.mem_bot] at hzc
  have hz1 : z = 1 := congrArg Subtype.val hzc
  have hord := hz.order
  rw [hz1, orderOf_one] at hord
  norm_num at hord

private theorem nf5_normal_of_unique {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) : L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc : IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  have hmem : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
  rw [hall _ hc] at hmem
  exact hmem

private theorem nf5_layer_comp_eq {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) : CFSG.layer Y = L := by
  rw [CFSG.layer.eq_sSup]
  apply le_antisymm
  · apply sSup_le
    intro K hK
    exact (hall K ((CFSG.isComponent_iff_open K).mp hK)).le
  · exact le_sSup ((CFSG.isComponent_iff_open L).mpr hL)

private theorem nf5_centralizer_eq_bot (hcore : primeComplementCore (G := Y) 5 = ⊥)
    (hbot : CFSG.pCore 5 Y = ⊥) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) :
    Subgroup.centralizer (L : Set Y) = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc := CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.centralizer_layer_inf_centralizer_pCore_le
    (Y := Y) (p := 5) hcore
  rw [hbot, nf5_layer_comp_eq hL hall] at hc
  rw [eq_bot_iff]
  intro g hg
  have h2 : g ∈ Subgroup.centralizer ((⊥ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : y = 1 := by simpa using hy
    rw [this]; simp
  exact hc ⟨hg, h2⟩

theorem nf5_cfg (h6 : KFactI6103Five) (h : NF5 F Γ B R₀ x) (hex : ∃ L : Subgroup Y, IsComponentOf L ⊤) :
    ∃ (L : Subgroup Y) (z : Y), NF5Cfg F Γ B R₀ x L z := by
  obtain ⟨L, hL⟩ := hex
  have hZ : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → Subgroup.center ↥L' = ⊥ :=
    fun L' hL' => nf5_center_bot h6 h hL'
  obtain ⟨z, hz⟩ := nf5_exists_z h
  have hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L :=
    fun L' hL' => nf5_comp_unique h hZ hz hL' hL
  have hbot : CFSG.pCore 5 Y = ⊥ := nf5_pCore_bot h hZ hz hL
  have hzL : z ∈ L := nf5_z_mem_comp h hZ hz hL
  have hcen : Subgroup.center ↥L = ⊥ := hZ L hL
  have hnorm : L.Normal := nf5_normal_of_unique hL hall
  have hcent : Subgroup.centralizer (L : Set Y) = ⊥ := nf5_centralizer_eq_bot h.core hbot hL hall
  exact ⟨L, z, ⟨h, hL, hall, hz, hzL, hcen, hnorm, hcent⟩⟩

theorem nf5_layer_eq {L : Subgroup Y} {z : Y} (hc : NF5Cfg F Γ B R₀ x L z) :
    GLALayer (⊤ : Subgroup Y) = L := by
  unfold GLALayer
  apply le_antisymm
  · exact sSup_le fun K hK => (hc.uniq K hK).le
  · exact le_sSup hc.comp

theorem nf5_layer_bot (hno : ∀ L : Subgroup Y, ¬ IsComponentOf L ⊤) : GLALayer (⊤ : Subgroup Y) = ⊥ := by
  unfold GLALayer
  rw [eq_bot_iff]
  apply sSup_le
  intro K hK
  exact absurd hK (hno K)

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
