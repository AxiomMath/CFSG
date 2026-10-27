module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDPsi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open Subgroup Equiv CFSG.ComponentClassification.HSFLit

structure SDCtx (X : Type) [Group X] [Finite X] (t : X) (L : Subgroup X) where
  M : SDModel ↥L
  A : SDData t L
  compat : SDPsi.ModelCompat M A
  C : A.CaseKD
  S : SD.Gens A
  isPGroup_ker : IsPGroup 2 ↥(centralizer ({t} : Set X) ⊓ centralizer (L : Set X))

namespace SDCtx

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

include ctx

theorem L_le_centralizer : L ≤ centralizer ({t} : Set X) := ctx.A.config.le_centralizer

theorem conj_injective : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) :=
  ctx.M.conj_injective

@[expose] noncomputable def act : ↥(centralizer ({t} : Set X)) →* MulAut ↥L :=
  SDAct.actC ctx.A.config.le_normalizer

@[expose] noncomputable def actX (g : X) : MulAut ↥L :=
  open Classical in if h : g ∈ centralizer ({t} : Set X) then ctx.act ⟨g, h⟩ else 1

theorem actX_of_mem {g : X} (hg : g ∈ centralizer ({t} : Set X)) :
    ctx.actX g = ctx.act ⟨g, hg⟩ := by
  simp [actX, hg]

theorem actX_mul {g h : X} (hg : g ∈ centralizer ({t} : Set X))
    (hh : h ∈ centralizer ({t} : Set X)) : ctx.actX (g * h) = ctx.actX g * ctx.actX h := by
  rw [ctx.actX_of_mem (mul_mem hg hh), ctx.actX_of_mem hg, ctx.actX_of_mem hh, ← map_mul]
  rfl

theorem actX_one : ctx.actX 1 = 1 := by
  rw [ctx.actX_of_mem (one_mem _)]
  exact map_one ctx.act

theorem actX_inv {g : X} (hg : g ∈ centralizer ({t} : Set X)) :
    ctx.actX g⁻¹ = (ctx.actX g)⁻¹ := by
  rw [ctx.actX_of_mem (inv_mem hg), ctx.actX_of_mem hg, ← map_inv]
  rfl

theorem actX_apply {g : X} (hg : g ∈ centralizer ({t} : Set X)) (l : ↥L) :
    ((ctx.actX g l : ↥L) : X) = g * l * g⁻¹ := by
  rw [ctx.actX_of_mem hg]
  exact SDAct.coe_actC_apply ctx.A.config.le_normalizer ⟨g, hg⟩ l

theorem actX_of_mem_L (l : ↥L) : ctx.actX (l : X) = MulAut.conj l := by
  rw [ctx.actX_of_mem (ctx.L_le_centralizer l.2)]
  exact SDAct.actC_of_mem ctx.A.config.le_normalizer ctx.L_le_centralizer l

theorem actX_mem_P {g : X} (hg : g ∈ ctx.A.T) : ctx.actX g ∈ SDAutP.P ctx.M.F := by
  obtain ⟨c, hc, rfl⟩ := hg
  show ctx.actX (c : X) ∈ _
  rw [ctx.actX_of_mem c.2]
  exact ctx.compat.act_mem c hc

theorem ψ_eq {g : X} (hg : g ∈ ctx.A.T) :
    ctx.A.ψ ⟨g, hg⟩ =
      (SDAutP.phi ctx.M.F ⟨ctx.actX g, ctx.actX_mem_P hg⟩ : Perm (ZMod 8)) := by
  obtain ⟨c, hc, rfl⟩ := hg
  have h3 : (⟨ctx.actX (c : X), ctx.actX_mem_P ⟨c, hc, rfl⟩⟩ : ↥(SDAutP.P ctx.M.F)) =
      ⟨SDAct.actC ctx.A.config.le_normalizer c, ctx.compat.act_mem c hc⟩ :=
    Subtype.ext (ctx.actX_of_mem c.2)
  show ctx.A.ψ ⟨(c : X), ⟨c, hc, rfl⟩⟩ =
    (SDAutP.phi ctx.M.F ⟨ctx.actX (c : X), ctx.actX_mem_P ⟨c, hc, rfl⟩⟩ : Perm (ZMod 8))
  rw [h3]
  exact ctx.compat.ψ_eq c hc

end SDCtx

end CFSG.OddStandard.SmallF3.L33.KD
