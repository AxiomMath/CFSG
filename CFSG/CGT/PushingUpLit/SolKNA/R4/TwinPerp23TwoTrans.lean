module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoFrame
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinWToolBasic
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H03

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace Perp23

namespace Two

section Trans

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}

theorem conj_mem_DSet (hΩ : ConjInvariant Ω) {W T : Subgroup Y} (hT : T ∈ DSet Ω W) (c : Y) :
    conjSub c T ∈ DSet Ω (conjSub c W) := by
  refine ⟨RSet.conj hΩ hT.1 c, ?_⟩
  have := conjSub_mono (n := c) hT.2
  rwa [conjSub_normalizer] at this

theorem trans_of_mgrp (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P J → 16 ≤ Nat.card P)
    {K W H : Subgroup Y} {t : Y} (hK : K ∈ Ω) (hz : IsUniqueInvolution K t) (hW : W ∈ WSet Ω)
    (htW : t ∈ W) (hCt : Subgroup.centralizer ({t} : Set Y) ≤ H) (hM : MGrp Ω W ≤ H)
    (hMtr : ∀ σ : Thompson.Rep Ω W, ∃ m ∈ MGrp Ω W, conjSub m K = σ.K) :
    ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J := by
  intro J hJ
  have key : ∀ W₁ ∈ WSet Ω, t ∈ W₁ → ∀ J' ∈ Ω, (∃ T ∈ DSet Ω W₁, IsSylow2In T J') →
      ∃ h ∈ H, conjSub h K = J' := by
    intro W₁ hW₁ htW₁ J' hJ' ⟨T, hT, hTJ'⟩
    obtain ⟨c, hcC, hcW⟩ := WTool.exists_conj_of_mem_mem hΩ h16 hW hW₁ htW htW₁
    have hT' : conjSub c⁻¹ T ∈ DSet Ω W := by
      have := conj_mem_DSet hΩ.conjInvariant hT c⁻¹
      rwa [← hcW, conjSub_inv_conjSub] at this
    have hJ'' : conjSub c⁻¹ J' ∈ Ω := hΩ.conjInvariant c⁻¹ J' hJ'
    have hTJ'' : IsSylow2In (conjSub c⁻¹ T) (conjSub c⁻¹ J') := hTJ'.conj c⁻¹
    obtain ⟨σ, hσK, -⟩ :=
      CFSG.ClassicalInvolution.T7F25.Asc77.T7D.exists_rep hΩ hW hJ'' hTJ'' hT'
    obtain ⟨m, hmM, hmK⟩ := hMtr σ
    refine ⟨c * m, H.mul_mem (hCt hcC) (hM hmM), ?_⟩
    rw [conjSub_mul, hmK, hσK, conjSub_conjSub_inv]
  have step : ∀ J' : Subgroup Y, dstarAdj Ω K J' → ∃ h ∈ H, conjSub h K = J' := by
    rintro J' ⟨hJ'Ω, hadj⟩
    rcases hadj with h | h
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
        CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hK h
      have hzW₁ : t ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hR₁ hR₁K hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT, hTJ'⟩
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
        CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hJ'Ω h
      have hzW₁ : t ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT hTK hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨R₁, hR₁, hR₁J'⟩
  have hJ' : Relation.ReflTransGen (dstarAdj Ω) K J := hJ
  clear hJ
  induction hJ' with
  | refl => exact ⟨1, H.one_mem, conjSub_one K⟩
  | @tail J₁ J₂ _ hadj ih =>
    obtain ⟨h₁, hh₁, hJ₁⟩ := ih
    have hadj' : dstarAdj Ω K (conjSub h₁⁻¹ J₂) := by
      obtain ⟨hJ₂, h | h⟩ := hadj
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inl ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inr ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
    obtain ⟨h₂, hh₂, hJ₂⟩ := step _ hadj'
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
    rw [conjSub_mul, hJ₂, conjSub_conjSub_inv]

variable {W K K' : Subgroup Y} {t : Y}

namespace TwoFrame

variable (D : TwoFrame Ω W K K' t)

include D

theorem exists_conj_rep (c : Q3CL.Thompson.Ctx Ω W) (σ : Thompson.Rep Ω W) :
    ∃ m ∈ MGrp Ω W, conjSub m K = σ.K := by
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem D.he (T7D.imgQ_mem D.F.ρ) (T7D.imgQ_mem σ)
  obtain ⟨m', hm'M, hym'⟩ := CFSG.ClassicalInvolution.Asc77.T7E.exists_mem_MGrp_of_mem_muGroup y
  have hm'N : m' ∈ Subgroup.normalizer (W : Set Y) := Thompson.MGrp_le_normalizer Ω W hm'M
  have himg : Thompson.piG W m' * D.F.ρ.img * (Thompson.piG W m')⁻¹ = σ.img := by
    rw [← hym']
    exact congrArg Subtype.val hy
  have hKm : conjSub m' D.F.ρ.K = σ.K :=
    c.K_eq_of_img_eq (CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7D.conjRep c.hΩ hm'N D.F.ρ) σ
      (by rw [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7D.conjRep_img, himg])
  exact ⟨m', hm'M, by rw [← hKm, D.hρK]⟩

theorem mgrp_le (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (c : Q3CL.Thompson.Ctx Ω W)
    {H : Subgroup Y} (hr : D.F.ρ.r ∈ H) (hr' : D.F.ρ'.r ∈ H) (hs : D.F.ρ₃.r ∈ H)
    (hWH : W ⊔ OCW W ≤ H) : MGrp Ω W ≤ H := by
  refine iSup₂_le fun R hR => ?_
  obtain ⟨KR, hKR, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨σ, -, hσR⟩ := CFSG.ClassicalInvolution.T7F25.Asc77.T7D.exists_rep hΩ hW hKR hRK hR
  rw [← hσR]
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.rep_R_le c D.F D.he D.hab D.hcomm D.hac hr hr' hs
    hWH σ

end TwoFrame

end Trans

end Two

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
