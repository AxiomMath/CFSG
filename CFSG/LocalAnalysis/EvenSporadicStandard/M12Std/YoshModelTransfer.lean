module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshPresModel

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.CosetTable CFSG.EvenSporadicStandard.Fin76b

@[expose] def modelT (n k : ℕ) (g : Array Table) (w : List (Fin k × Bool)) : Table :=
  evalT n (fun i : Fin k => g[i.val]!) (fun i : Fin k => (g.map (invT n))[i.val]!) w

theorem rep_modelT {n m k size : ℕ} (hn : n < 2 ^ 32) {g : Array Table} (hk : g.size = k)
    {ws : List (List (Fin k × Bool))} (h : ModelOK n m k g ws size)
    (w : List (Fin k × Bool)) :
    Rep n (modelT n k g w) (FreeGroup.lift (modelGens n k g) (FreeGroup.mk w)) := by
  obtain ⟨hs, -⟩ := modelCheck_spec hn hk h
  exact rep_evalT hn (modelGens n k g) hs.rep hs.repInv w

theorem lift_eq_of_modelEq {n m k size : ℕ} (hn : n < 2 ^ 32) {g : Array Table}
    (hk : g.size = k) {ws : List (List (Fin k × Bool))}
    (h : ModelOK n m k g ws size) {H : Type*} [Group H] (x : Fin k → H)
    (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1) {w₁ w₂ : List (Fin k × Bool)}
    (hw : tblEq n (modelT n k g w₁) (modelT n k g w₂) = true) :
    FreeGroup.lift x (FreeGroup.mk w₁) = FreeGroup.lift x (FreeGroup.mk w₂) := by
  obtain ⟨hs, -⟩ := modelCheck_spec hn hk h
  have h1 := (tblEq_iff_eq (rep_modelT hn hk h w₁) (rep_modelT hn hk h w₂)).1 hw
  have h2 : FreeGroup.lift (modelGens n k g) (FreeGroup.mk (mkRel w₁ w₂)) = 1 :=
    lift_mkRel_eq_one _ h1
  have hle : Nat.card (PG k ws) ≤ Nat.card (closure (Set.range (modelGens n k g))) :=
    hs.card_pg.trans (le_of_eq hs.card_group.symm)
  have h3 := lift_eq_one_of_presModel ws (modelGens n k g) hs.rel hs.fin hle x hx _ h2
  rw [lift_mk_mkRel] at h3
  exact mul_inv_eq_one.1 h3

theorem lift_eq_one_of_modelTrivial {n m k size : ℕ} (hn : n < 2 ^ 32) {g : Array Table}
    (hk : g.size = k) {ws : List (List (Fin k × Bool))}
    (h : ModelOK n m k g ws size) {H : Type*} [Group H] (x : Fin k → H)
    (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1) {w : List (Fin k × Bool)}
    (hw : tblEq n (modelT n k g w) (idT n) = true) :
    FreeGroup.lift x (FreeGroup.mk w) = 1 := by
  have := lift_eq_of_modelEq hn hk h x hx (w₁ := w) (w₂ := []) hw
  rw [this]
  simp

end CFSG.EvenSporadicStandard.M12Std.Yosh
