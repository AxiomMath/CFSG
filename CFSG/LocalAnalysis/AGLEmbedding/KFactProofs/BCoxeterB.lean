module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BThreeTc
public import CFSG.Sporadic.Bridge.BSurj
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoxeterRels
import all CFSG.Sporadic.Bridge.BSurj

public section

namespace CFSG.AGLEmbedding.BCox

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.B CFSG.Blueprint
open CFSG.RankThree.PartOne.CTP.Fus

theorem tB_rel {i j : Fin 11} (hij : i ≤ j) : (tB i.val * tB j.val) ^ cm i j = 1 := by
  have h := bridgeFacts.rels _ (cox_mem i j hij)
  rw [wordProd_flatten_replicate] at h
  simpa [wordProd] using h

private theorem comm_of_sq {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : (x * y) ^ 2 = 1) : x * y = y * x := by
  have h1 : y * x = (x * y)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  rw [h1]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_two]
  exact h

theorem tB_comm_of_lt {i j : Fin 11} (h : i < j) (hij : adj i j = false) :
    tB i.val * tB j.val = tB j.val * tB i.val := by
  have hi : tB i.val * tB i.val = 1 := bridgeFacts.inv i.val i.isLt
  have hj : tB j.val * tB j.val = 1 := bridgeFacts.inv j.val j.isLt
  have h1 := tB_rel h.le
  rw [cm_two i j h hij] at h1
  exact comm_of_sq (x := tB i.val) (y := tB j.val) hi hj h1

theorem tB_braid_of_lt {i j : Fin 11} (h : i < j) (hij : adj i j = true) :
    (tB i.val * tB j.val) ^ 3 = 1 := by
  have h1 := tB_rel h.le
  rwa [cm_three i j h hij] at h1

noncomputable def gensB : Gens NativeSporadic.B where
  t i := tB i.val
  sq i := bridgeFacts.inv i.val i.isLt
  comm_lt i j h hij := tB_comm_of_lt h hij
  braid_lt i j h hij := tB_braid_of_lt h hij
  gen := by
    rw [eq_top_iff, ← range_eq_top, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of,
      MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    show tB i.val = φ (PresentedGroup.of i)
    rw [← presGen_eq_of i]
    exact (presHom_presGen pres tB bridgeFacts.rels i.isLt).symm

theorem three_le_pRank_B [Finite NativeSporadic.B] (hc : 2 < Nat.card NativeSporadic.B) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup NativeSporadic.B) :=
  three_le_pRank_of_gens gensB hc

theorem tcGenDatum_B_three [Finite NativeSporadic.B] (hc : 2 < Nat.card NativeSporadic.B) :
    TCGenDatum NativeSporadic.B 3 :=
  tcGenDatum_of_gens gensB hc

theorem coverPointDatum_B_three (hc : 2 < Nat.card NativeSporadic.B) :
    CoverPointDatum NativeSporadic.B 3 :=
  coverPointDatum_of_gens gensB hc

theorem fusionGenerationOf_B_three (hc : 2 < Nat.card NativeSporadic.B) :
    FusionGenerationOf NativeSporadic.B 3 :=
  fusionGenerationOf_of_gens gensB hc

theorem sporCaseThreePrimeData_B_three [Finite NativeSporadic.B]
    (hc : 2 < Nat.card NativeSporadic.B) [Fact (Nat.Prime 3)] :
    SporCaseThreePrimeData NativeSporadic.B 3 :=
  sporCaseThreePrimeData_of_gens gensB hc

end CFSG.AGLEmbedding.BCox
