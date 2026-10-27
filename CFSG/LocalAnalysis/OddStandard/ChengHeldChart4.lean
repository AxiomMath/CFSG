module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartFrame
public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartStd

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

section Assembly

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {d : Datum A}
  {P : Pos d} {α : ℕ} (F : FrameData P α)

theorem t_mem_Z2 (h : Hyp G A) :
    ((F.p 0 : ↥d.S) : G) ∈ d.X ⊓ A ⊓ centralizer (A : Set G) := by
  have hker : jS d (F.p 0) ∈ center (Jhat A) := by
    rw [F.hp 0, ← P.isQ.ker]
    exact nfM_frM_zero_mem_ker P.isQ α
  have hz : ((F.p 0 : ↥d.S) : G) ∈ zStarIn A :=
    (mem_zStarIn_iff (d.S_le_A (F.p 0).2)).2 hker
  rw [zStarIn_eq h] at hz
  exact ⟨⟨d.S_le_X (F.p 0).2, hz.1⟩, hz.2⟩

theorem orderOf_t (h : Hyp G A)
    (hkle : ∀ e ∈ P.q.ker, e ∈ zpowers (nfM P.l (frM α 0))) :
    orderOf ((F.p 0 : ↥d.S) : G) = Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) := by
  rw [← (ker_card d P h).1, card_ker_eq_orderOf P.isQ hkle, Subgroup.orderOf_coe,
    ← F.hp 0]
  exact (orderOf_injective (jS d) (jS_injective d) (F.p 0)).symm

theorem act_S (hC : ChCoverParts) (hα : α ≤ 1)
    (hstd : ∀ a b : ZMod 4, zz P.l a b = 1 ↔ inK (kapOf α) a b) {k : ℕ} (hk : k < 3) {y : G}
    {hy : y ∈ d.X} (hp : Pure d P.l (k + 1) y hy) :
    ∀ e ∈ actRels α k, cS d y hy (F.p e.1) = evalE F.p e.2 := by
  intro e he
  apply jS_injective d
  rw [jS_cS, F.hp, jS_evalE F]
  exact act_nfM hC.act4 P.isQ hα hstd hk (β := betaHat A (d.X_sylow.le hy)) hp e he

theorem act_G (hC : ChCoverParts) (hα : α ≤ 1)
    (hstd : ∀ a b : ZMod 4, zz P.l a b = 1 ↔ inK (kapOf α) a b) {k : ℕ} (hk : k < 3) {y : G}
    {hy : y ∈ d.X} (hp : Pure d P.l (k + 1) y hy) :
    ∀ e ∈ actRels α k,
      cj (((F.p e.1 : ↥d.S)) : G) y = evalE (fun i => ((F.p i : ↥d.S) : G)) e.2 := by
  intro e he
  have h1 := evalE_map d.S.subtype F.p e.2
  simp only [Subgroup.coe_subtype] at h1
  rw [cj_coe d y hy (F.p e.1), act_S F hC hα hstd hk hp e he, h1]

end Assembly

end CFSG.OddStandard.ChengHeld.M1b

