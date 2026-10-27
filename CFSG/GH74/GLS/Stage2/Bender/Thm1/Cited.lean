module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

theorem ig_11_23_thm : IG_11_23 := by
  intro G _ _ p hp V Y hV hcard hcop hVn
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p ↥V := hV
  have hY : ¬ p ∣ Nat.card ↥Y := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  let _ : MulDistribMulAction ↥V ↥Y := MulDistribMulAction.compHom ↥Y (Subgroup.inclusion hVn)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := ↥V) (H := ↥Y)
    (by rw [hcard]) hY
  have hle : (⨆ (a : ↥V) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥Y) ≤
      (⨆ (v : G) (_ : v ∈ V ∧ v ≠ 1), Y ⊓ centralizer ({v} : Set G)).comap Y.subtype := by
    refine iSup₂_le fun a ha => fun x hx => ?_
    have hfix := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have hc : (a : G) * x * (a : G)⁻¹ = x := congrArg Subtype.val hfix
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    refine Subgroup.mem_iSup_of_mem (a : G) (Subgroup.mem_iSup_of_mem ⟨a.2, ha1⟩
      (Subgroup.mem_inf.2 ⟨x.2, ?_⟩))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * a = (a : G) * x * (a : G)⁻¹ * a := by rw [hc]
      _ = a * x := by rw [inv_mul_cancel_right]
  intro h hh
  have hmem : (⟨h, hh⟩ : ↥Y) ∈
      ⨆ (a : ↥V) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥Y := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle hmem

theorem oddNoncyclicPlane_thm : OddNoncyclicPlane := by
  intro G _ _ r hr hr2 R hR hnc
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (IsPGroup r ↥R) := ⟨hR⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hr2 hnc
  have : IsElementaryAbelian r ↥S := hSel
  refine ⟨S.map R.subtype, Subgroup.map_subtype_le S, IsElementaryAbelian.map_subtype, ?_⟩
  rw [Subgroup.card_map_of_injective R.subtype_injective, hScard]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
