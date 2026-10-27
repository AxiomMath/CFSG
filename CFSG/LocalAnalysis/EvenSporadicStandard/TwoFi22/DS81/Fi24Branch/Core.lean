module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ChoiceZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.JR

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t z : G}

structure FiniteFacts : Prop where
  cocode : CocodeFacts
  K : KFacts
  U42 : U42Facts

structure Core0 (E : Subgroup G) (t z : G) : Prop where
  m24 : M24Out G E t
  isZ : IsZ E t z
  klein : KleinPair t z
  cocode : CocodeData E t z
  kdata : KData t z
  zdata : ZData E t z
  u42 : U42Facts

theorem core0 (hF : FiniteFacts)
    (h : Std G L E t) (hz : IsZ E t z) : Core0 E t z :=
  ⟨h.m24, hz, h.klein hz, hF.cocode.data G E t z h.m24 hz, hF.K G L E t z h hz,
    zData hF.cocode hF.K h hz, hF.U42⟩

structure Core1 (E : Subgroup G) (t z : G) : Prop extends Core0 E t z where
  jr : JRData t z

theorem core1 (c : Core0 E t z) : Core1 E t z :=
  have hJ : JBasic t z := jBasic c.klein c.zdata.notConj c.zdata.conj_tz
    (let ⟨y, hy, hyt⟩ := c.cocode.swap; ⟨y, (Subgroup.mem_inf.mp hy).2, hyt⟩)
  have hS : RSplit t z := rSplit hJ c.kdata c.u42
  ⟨c, jrData c.klein hJ hS c.kdata⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
