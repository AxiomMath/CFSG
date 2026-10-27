module

public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteIso
public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteSearch

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Six

open Equiv

@[expose] def K4Ok (V : List (Perm (Fin 6))) : Prop :=
  V.length = 3 ∧
  (∀ a ∈ oneT 6 :: V.map tab, ∀ b ∈ oneT 6 :: V.map tab, mulT a b ∈ oneT 6 :: V.map tab) ∧
  (∀ a ∈ V.map tab, mulT a a = oneT 6) ∧ (∀ a ∈ V.map tab, suppT 6 a = 4)

structure Cfg where
  mkCfg ::
  V : List (Perm (Fin 6))
  reps : List (Perm (Fin 6))
  l1 : List (Perm (Fin 6))
  l2 : List (Perm (Fin 6))
  R1 : List (Perm (Fin 6))
  R2 : List (Perm (Fin 6))

@[expose] def Cfg.Ok (c : Cfg) : Prop :=
  SearchOk c.V c.reps c.l1 c.l2 ∧ IsoOk (mk c.V c.l1) c.R1 ∧ IsoOk (mk c.V c.l2) c.R2 ∧ K4Ok c.V

@[expose] def RA1 : List (Perm (Fin 6)) :=
  [dt 0 1 2 3, dt 1 2 3 4, dt 0 3 2 4, dt 0 2 3 5, dt 1 3 2 5]

@[expose] def RA2 : List (Perm (Fin 6)) :=
  [dt 0 1 2 3, dt 1 2 3 5, dt 0 3 2 5, dt 0 2 3 4, dt 1 3 2 4]

@[expose] def RB1 : List (Perm (Fin 6)) :=
  [dt 0 1 2 3, dt 1 2 3 4, dt 0 3 2 4, dt 0 3 1 4, dt 0 4 1 2]

@[expose] def RB2 : List (Perm (Fin 6)) :=
  [dt 0 1 2 3, dt 1 2 3 5, dt 0 3 2 5, dt 0 3 1 5, dt 0 5 1 2]

theorem isoOk_A1 : IsoOk (mk VA selA1) RA1 := by
  unfold IsoOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem isoOk_A2 : IsoOk (mk VA selA2) RA2 := by
  unfold IsoOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem isoOk_B1 : IsoOk (mk VB selB1) RB1 := by
  unfold IsoOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem isoOk_B2 : IsoOk (mk VB selB2) RB2 := by
  unfold IsoOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem k4Ok_A : K4Ok VA := by
  unfold K4Ok
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem k4Ok_B : K4Ok VB := by
  unfold K4Ok
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

@[expose] def cfgA : Cfg := ⟨VA, repsA, selA1, selA2, RA1, RA2⟩

@[expose] def cfgB : Cfg := ⟨VB, repsB, selB1, selB2, RB1, RB2⟩

theorem cfgA_ok : cfgA.Ok := ⟨searchOk_A, isoOk_A1, isoOk_A2, k4Ok_A⟩

theorem cfgB_ok : cfgB.Ok := ⟨searchOk_B, isoOk_B1, isoOk_B2, k4Ok_B⟩

end CFSG.GF2Type.Aschbacher1976Full.HS.Six
