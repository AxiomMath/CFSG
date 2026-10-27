module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Transport
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndSection4

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup

variable {G : Type} [Group G] {L : Subgroup G}
  (e : L ≃* T46)

@[expose] def yamWord (w : List ℕ) : SUJ := (w.map yamGen).prod

@[expose] noncomputable def sS : Subgroup G := toG e chS.grp

@[expose] noncomputable def sX₁ : Subgroup G := toG e chX1.grp

@[expose] noncomputable def sX₂ : Subgroup G := toG e chX2.grp

@[expose] noncomputable def sX₃ : Subgroup G := toG e chX3.grp

@[expose] noncomputable def sA₁ : Subgroup G := toG e chA1.grp

@[expose] noncomputable def sA₂ : Subgroup G := toG e chA2.grp

@[expose] noncomputable def sK₁ : Subgroup G := toG e chK1.grp

@[expose] noncomputable def sK₂ : Subgroup G := toG e chK2.grp

@[expose] noncomputable def sw (i : ℕ) : G := phiG e (yamGen (15 + i))

@[expose] noncomputable def sj₀ : G := phiG e (yamWord [15, 1, 15, 0, 1, 15, 1])

@[expose] noncomputable def sJ : Subgroup G := zpowers (sj₀ e)

@[expose] noncomputable def sec3Data (t : G) (V₁ D₁ D₂ N₁ N₂ P : Subgroup G) :
    YamadaEnd.YamadaData G where
  L := L
  t := t
  S := sS e
  A₁ := sA₁ e
  A₂ := sA₂ e
  K₁ := sK₁ e
  K₂ := sK₂ e
  X₁ := sX₁ e
  X₂ := sX₂ e
  X₃ := sX₃ e
  J := sJ e
  V₁ := V₁
  D₁ := D₁
  D₂ := D₂
  N₁ := N₁
  N₂ := N₂
  P := P
  w₁ := sw e 0
  w₂ := sw e 1
  w₃ := sw e 2

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
