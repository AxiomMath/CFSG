module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b

section Card

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

set_option linter.unusedSectionVars false

theorem valG_mem_HcG {w : List (Fin 5 × Bool)} (h : commT (tblW w) (tblW wJ) = true) :
    valG e₀ w ∈ HcG e₀ := by
  have hσ := commJ_of_commT (T := tblW w) (a := (wordVal w).1) (τ := (wordVal w).2)
    (by exact rep_tblW w) h
  exact jH_mem_Hc e₀ (wordVal w).1 (wordVal w).2 hσ

theorem commT_of_commute_valG {y : G} {T : Table} {a : Multiplicative (ZMod 2)} {σ : G12}
    (hy : y = jH e₀ (a, σ)) (hT : Rep 14 T (kapP (a, (σ : Equiv.Perm (Fin 12)))))
    {w : List (Fin 5 × Bool)} (h : y * valG e₀ w = valG e₀ w * y) : commT T (tblW w) = true := by
  rw [hy] at h
  unfold valG at h
  rw [← map_mul, ← map_mul] at h
  have h2 := jH_injective e₀ h
  have h3 : kapM ((a, σ) * wordVal w) = kapM (wordVal w * (a, σ)) := by rw [h2]
  rw [map_mul, map_mul] at h3
  exact (tblEq_iff_eq (Rep.compT hT (rep_tblW w)) (Rep.compT (rep_tblW w) hT)).2 h3

theorem eq_valG_of_tblEq {y : G} {T : Table} {a : Multiplicative (ZMod 2)} {σ : G12}
    (hy : y = jH e₀ (a, σ)) (hT : Rep 14 T (kapP (a, (σ : Equiv.Perm (Fin 12)))))
    {w : List (Fin 5 × Bool)} (h : tblEq 14 T (tblW w) = true) : y = valG e₀ w := by
  have h5 := (tblEq_iff_eq hT (rep_tblW w)).1 h
  have h6 : (a, σ) = wordVal w := kapM_injective h5
  rw [hy, h6]
  rfl

end Card

end CFSG.EvenSporadicStandard.M12Std.Yosh
