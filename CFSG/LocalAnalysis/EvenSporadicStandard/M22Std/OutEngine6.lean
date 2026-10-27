module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngineGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsExtra2

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std
  CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def AutS6Quot (Y : Type) [Group Y] (F : Subgroup Y) : Prop :=
  NormQuot (Equiv.Perm (Fin 6))
    (normalizer ((innerImage Y F : Subgroup (MulAut Y)) : Set (MulAut Y))) (innerImage Y F)

theorem AutS6Quot.map_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {F : Subgroup X}
    (h : AutS6Quot X F) : AutS6Quot Y (F.map e.toMonoidHom) := by
  have h1 := NormQuot.map (φ := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective h
  rwa [Subgroup.map_equiv_normalizer_eq, innerImage_map' e (MulAut.congr e) (congr_conj e)] at h1

structure EngineData6 (Y : Type) [Group Y] (F : Subgroup Y) : Prop where
  engine : EngineData Y F
  s6 : AutS6Quot Y F

theorem EngineData6.map_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {F : Subgroup X}
    (D : EngineData6 X F) : EngineData6 Y (F.map e.toMonoidHom) :=
  ⟨D.engine.map_equiv e, D.s6.map_equiv e⟩

theorem EngineData6.isoInv : IsoInv (fun Y _ F => EngineData6 Y F) :=
  fun e _ D => D.map_equiv e

@[expose] def AutSylowEngine6 (Y : Type) [Group Y] : Prop :=
  AutSylowWith (fun Y _ F => EngineData6 Y F) Y

theorem AutSylowEngine6.of_sylow {Y : Type} [Group Y] [Finite (MulAut Y)]
    {S₀ : Subgroup (MulAut Y)} (hp : IsPGroup 2 S₀) (hidx : ¬ 2 ∣ S₀.index) {t : Y}
    {F : Subgroup Y} (W : SylowWitness Y S₀ t F) (E : EngineData6 Y F) : AutSylowEngine6 Y :=
  AutSylowWith.of_sylow EngineData6.isoInv hp hidx W E

theorem AutSylowEngine6.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : AutSylowEngine6 X) : AutSylowEngine6 Y :=
  AutSylowWith.of_mulEquiv EngineData6.isoInv e h

theorem autSylowEngine6_m22 :
    AutSylowEngine6 (Carrier .M22) := by
  obtain ⟨S₀, t, F1, hp, hidx, hmem1, W⟩ := sylowWitness_m22_pinned
  exact AutSylowEngine6.of_sylow hp hidx W ⟨engineData_pinned hmem1, normQuot_aut hmem1 W.nd⟩

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

namespace OutData

variable (D : OutData L z t T₁ F tb)

include D in
theorem engine6 [Finite G] (hcZ : center (L ⧸ center L) = ⊥)
    (hEng : AutSylowEngine6 (L ⧸ center L)) : EngineData6 (L ⧸ center L) F :=
  D.property (P := fun Y _ F => EngineData6 Y F) hcZ hEng

end OutData

end CFSG.EvenSporadicStandard.M22Std
