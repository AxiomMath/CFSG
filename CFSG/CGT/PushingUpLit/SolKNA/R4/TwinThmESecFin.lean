module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESecFour
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189b

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open scoped commutatorElement

namespace ThmE

section Fin


variable {r : ℕ}




theorem MinCex.e18_5 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex r Ω K S R W H)
    (hT4 : Thm4RTwinBelow r (Nat.card G)) : (⨆ J ∈ Ω, J) = ⊤ := by
  by_contra hX
  set Y : Subgroup G := ⨆ J ∈ Ω, J with hYdef
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hEA : EtaAbelian Ω := TwinThmEW.etaAbelian_of_gen hΩ
  have hEM : EtaMeet Ω := TwinThmEW.etaMeet_of_gen hΩ
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK : K ∈ Ω := c.stand.mem
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hKY : K ≤ Y := le_iSup₂_of_le K hK le_rfl
  have hK'Y : K' ≤ Y := le_iSup₂_of_le K' hK'Ω le_rfl
  have hnorm : Y.Normal := omegaGen_normal hΩ.conjInvariant
  have hYtop : Y ≠ ⊤ := hX
  have hRY : R ≤ Y := hRK.trans hKY
  have hR'Y : R' ≤ Y := hR'K'.trans hK'Y
  have hSY : IsSylow2In ((S : Subgroup G) ⊓ Y) Y := by
    refine isSylow2In_inf_of_le_normalizer ?_ le_top ?_
    · exact ⟨le_top, S.isPGroup', fun V' _ hV'2 hSV' => (S.is_maximal' hV'2 hSV')⟩
    · intro x _
      exact mem_normalizer_iff_conjSub_eq.mpr (AscQuot.conjSub_eq_of_normal _ x)
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK
  have hR'syl : IsSylow2In R' K' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hR' hR'K'
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3 G Ω K S R W H c) c.stand.aEmpty
  have hNH : oddCoreOf Y ≤ H :=
    c.oddCoreOf_le hEA hEM hK'tw hK'ne hR' hR'K' hR'S (sup_le hRY hR'Y)
  have hΛ : HypOmegaGen (restrictFamily Ω Y) := hypOmegaGen_restrict hΩ Y
  have hgen : Y ≤ ⨆ L ∈ restrictFamily Ω Y, L.map Y.subtype := by
    refine iSup₂_le fun J hJ => ?_
    have hJY : J ≤ Y := le_iSup₂_of_le J hJ le_rfl
    refine le_iSup₂_of_le (J.subgroupOf Y) (subgroupOf_mem_restrictFamily hJ hJY) ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJY]
  have hYH : Y ≤ H :=
    c.section_le_H hT4 hYtop hΛ (classicalClause_restrict c.stand.cls Y)
      (quat_restrict c.stand.quat Y) (two_restrict c.stand.two Y) (AscQuot.sylowOfIsSylow2In' hSY)
      (subgroupOf_mem_restrictFamily hK hKY) (twinSet_subgroupOf hKY hK'Y hK'tw)
      (subgroupOf_ne_of_ne hKY hK'Y hK'ne)
      (mem_RSet_restrict hK hKY hRsyl) (Subgroup.subgroupOf_mono _ hRK)
      (Subgroup.subgroupOf_mono _ (le_inf hRS hRY))
      (mem_RSet_restrict hK'Ω hK'Y hR'syl) (Subgroup.subgroupOf_mono _ hR'K')
      (Subgroup.subgroupOf_mono _ (le_inf hR'S hR'Y)) hNH hgen (c.trans_restrict hKY)
      (TwinThmEW.exists_W_restrict hΩ c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent
        (S₁ := AscQuot.sylowOfIsSylow2In' hSY)
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := hx
          exact (Subgroup.mem_subgroupOf.mp hy).1)) (restrictGood Ω Y K) ⟨K, hK, hKY, rfl, Relation.ReflTransGen.refl⟩
      (fun L _ L' hL' hg hadj => restrictGood_step hL' hg hadj)
      (fun L _ hg => c.restrictGood_le_H hg)
      (fun _ L hL => by
        obtain ⟨J, hJ, hJY, rfl⟩ := hL
        exact AEmpty.restrict hΩ hJY (hAΩ J hJ))
  obtain ⟨u, huR, hu4⟩ := exists_orderOf_eq_four_of_mem_RSet_gen hΩ hRR
  refine c.proper (eq_top_iff.mpr fun g _ => ?_)
  have hle : conjSub g K ≤ Y :=
    le_iSup₂_of_le (conjSub g K) (hΩ.conjInvariant g K hK) le_rfl
  exact e18_2 G Ω K S R W H c u (hRK huR) hu4 g (hYH (hle (conj_mem_conjSub (hRK huR))))

theorem e18_5 : E18_5 r :=
  fun G _ _ Ω K S R W H c => c.e18_5 c.stand.ih.t4

theorem e18_4C : E18_4C r :=
  fun G _ _ Ω K S R W H c K' hK' hne R' hR' hR'K' h2 w hw1 hw2 hRw hw =>
    c.e18_4C c.stand.ih.t4 hK' hne hR' hR'K' h2 hw1 hw2 hRw hw


end Fin

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
