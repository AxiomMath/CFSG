module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Quiet
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Basic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPerp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf8Class

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

namespace Perp22

section Inputs

@[expose] def ThmER (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → ∀ K H : Subgroup Y, K ∈ CoreAssembly.conjClass (tightCore R) →
      EHyp (CoreAssembly.conjClass (tightCore R)) K ⊥ H → H = ⊤

@[expose] def ThreeTwinsExclR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t →
      (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 3 → False

@[expose] def WylD4ExclR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → ¬ TwinPerp.TwoTwins R →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          (∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
            MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W) → False

end Inputs

section BranchI

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem layer_mem {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃) :
    ∃ htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y),
      (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
        coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
  have hmem := TwinPerpV3.tq_of_hyp22G d
  have htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * t = u₁ * (u₂ * t) := by group
      _ = u₁ * (t * u₂) := by rw [← d.comm_z₂]
      _ = (u₁ * t) * u₂ := by group
      _ = (t * u₁) * u₂ := by rw [← d.comm_z₁]
      _ = t * (u₁ * u₂) := by group
  have htcore : t ∈ TwinADescent.coreAt (u₁ * u₂) K₃ := by
    have hle : Subgroup.zpowers t ≤ K₃ ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
      Subgroup.zpowers_le.mpr ⟨d.hzK₃.mem, htC⟩
    exact le_tightCore_of_isPGroup hle
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.hz.sq)
      (Subgroup.mem_zpowers t)
  exact ⟨htC, le_coreHull hmem (Subgroup.mem_subgroupOf.mpr htcore)⟩

theorem ncard_twinSet_eq_four_of_wyl (h : PerpHypR r n Y R S t) (h3 : ¬ TwinPerp.TwoTwins R)
    (hWyl : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W) :
    (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 4 := by
  obtain ⟨K', K₃, u₁, u₂, u₃, hd⟩ := h.exists_hyp22G h3
  exact ncard_twins_eq_four h.partIHypG hd (h.kPerp_datum hd.mem hd.hz) hWyl

theorem false_of_not_wyl (hE : ThmER r n) (h : PerpHypR r n Y R S t) (h3 : ¬ TwinPerp.TwoTwins R)
    {W₀ : Subgroup Y} (hW₀ : W₀ ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hnW : ¬ MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W₀)
    (h51 : ∀ {L L' L₃ : Subgroup Y} {x y w : Y},
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) L L' L₃ t x y w →
        Hyp51 (Subgroup.closure ({x * y, t, y * w} : Set Y)))
    (hzs : ∀ {L L' L₃ : Subgroup Y} {x y w : Y},
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) L L' L₃ t x y w →
        t ∈ zStarOf (Subgroup.centralizer ({x * y} : Set Y))) : False := by
  obtain ⟨K', K₃, u₁, u₂, u₃, hd⟩ := h.exists_hyp22G h3
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hP := h.partIHypG
  have hperp := h.kPerp_datum hd.mem hd.hz
  have hα : A7T22.AlphaConst (CoreAssembly.conjClass (tightCore R)) t :=
    A7T22.alphaConst_of_hyp51 fun L L' L₃ x y w d' => h51 d'
  refine TwinPerpV3.false_of_thmE' hα hd h.perp ?_ ?_ ?_
    (TwinPerpV3.dstarComp_subset_twinSet_of_not_wyl hP hd hperp hW₀ hnW) ?_ ?_
  · intro A hAn hAodd
    have hle : A ≤ classicalInvolutionOddCore Y := le_sSup ⟨hAn, hAodd⟩
    rw [h.core.oddFree] at hle
    exact le_bot_iff.mp hle
  · intro c hc
    have : c ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => hc g
    rw [h.center_eq_bot] at this
    exact Subgroup.mem_bot.mp this
  · intro J ⟨g, hg⟩
    exact ⟨g, hg⟩
  · intro L L' L₃ x y w hd'
    exact hd'.cent_of_zstar (hzs hd')
  · intro H hstd htrans
    exact hE Y R S t h _ H (CoreAssembly.mem_conjClass_self _)
      ⟨htrans, TwinDisc.centralizersSylowPairs_of_stdCent_gen h.core.hyp hU hstd⟩

end BranchI

end Perp22

end CFSG.CGT.PushingUpLit.SolKNA.R4
