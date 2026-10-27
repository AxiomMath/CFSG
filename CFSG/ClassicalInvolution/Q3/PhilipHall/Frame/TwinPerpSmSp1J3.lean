module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSp1Wit
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16J3
public import Certificates.Certificate397506

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (qGens)
open Certificates.TwinPerpSmSp1

set_option linter.unusedSectionVars false

theorem j3Wit_xg_mem : ∀ l < j3Wit.xg.size,
    permOfArr 6156 j3Wit.xg[l]! ∈ CFSG.Sporadic.Schreier.j3P := by
  intro l hl
  have hxg : j3Wit.xg = #[CFSG.Sporadic.Schreier.j3StrongArrs[0]!,
      CFSG.Sporadic.Schreier.j3StrongArrs[1]!] := rfl
  have key : ∀ a b : Array ℕ, (#[a, b] : Array (Array ℕ))[0]! = a ∧
      (#[a, b] : Array (Array ℕ))[1]! = b := fun _ _ => ⟨rfl, rfl⟩
  rw [hxg] at hl ⊢
  have hl2 : l < 2 := hl
  interval_cases l
  · rw [(key _ _).1]
    exact Subgroup.subset_closure (Set.mem_insert (CFSG.Sporadic.Schreier.j3Gen 0) _)
  · rw [(key _ _).2]
    exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_singleton (CFSG.Sporadic.Schreier.j3Gen 1)))


theorem leaf_j3 {n : ℕ} :
    NoTwinS n (fun F _ => CFSG.Blueprint.NativeSporadic.IsSporadic F .J3) := by
  have h := Certificates.certificate397506
  refine noTwinS_of_q8Wit CFSG.Sporadic.SmallOddCore.j3_autModel
    (Subgroup.closure (permsA 6156 (qGens j3Wit.syl)))
    (syl_le_of_q8WitCheck j3Wit h _ fun l hl =>
      CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.j3Q16_pg_mem l hl)
    (k := 8) (m := 392445) (card_syl_of_q8WitCheck j3Wit h) (by decide)
    (by rw [CFSG.ComponentClassification.RankTwoSporadic.J3.card_j3R]; norm_num)
    (hwit_of_q8WitCheck j3Wit rfl h _ j3Wit_xg_mem) ?_
  intro Y _ _ R' S t hP hF
  obtain ⟨ψ⟩ := hF
  haveI := hP.core.simple
  haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  refine ⟨⟨ψ.trans CFSG.Sporadic.Schreier.j3PermEquiv⟩, ?_⟩
  exact isPGroup_core_of_oddCore hP
    (CFSG.Sporadic.SmallOddCore.ctuc_j3_almost_simple_involution_centralizer_odd_core_trivial
      (genFittingFStar Y) ⟨ψ⟩ (Nobq.centralizer_genFittingFStar_eq_bot hP.core.nonab) t
      hP.core.datum.order)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1
