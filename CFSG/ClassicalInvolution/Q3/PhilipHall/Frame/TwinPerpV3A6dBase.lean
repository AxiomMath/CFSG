module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6jB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dFive
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dKer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dThmD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

section Datum

variable (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
include H

theorem hypOf : HypOmegaGen Ω[R] := (CoreData.of_S H.ex.1.perp.core).hyp

theorem h2Of : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1

theorem h8Of : ∀ J ∈ Ω[R], Nat.card ↥J = 8 := by
  intro J hJ
  obtain ⟨e⟩ := members_q8_of_isPGroup H.ex.1.perp (h2Of H) J hJ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem aEmptyOf : ∀ J ∈ Ω[R], AEmpty Ω[R] J :=
  fun J hJ => (CoreData.of_S H.ex.1.perp.core).aEmpty_all J hJ

theorem tmemW : t ∈ W := H.ex.1.datum.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁

theorem K_le_M : K ≤ MGrp Ω[R] W :=
  le_iSup₂_of_le K H.hK le_rfl

theorem K₃_le_C : K₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
  have hd := H.ex.1.datum
  have hΩ := hypOf H
  have h2 := h2Of H
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := twin_comm hΩ h2 hd.hK₃.1 hd.mem hd.hK₃K hd.hzK₃ hd.hz x hx u₁ hd.hu₁.1
  have h2' := twin_comm hΩ h2 hd.hK₃.1 hd.hK'.1 hd.hK₃K' hd.hzK₃ hd.hzK' x hx u₂ hd.hu₂.1
  calc x * (u₁ * u₂) = (x * u₁) * u₂ := by group
    _ = (u₁ * x) * u₂ := by rw [h1]
    _ = u₁ * (x * u₂) := by group
    _ = u₁ * (u₂ * x) := by rw [h2']
    _ = u₁ * u₂ * x := by group


theorem exists_M_conj_of_mem_D {J₀ : Subgroup Y} (hJ₀ : J₀ ∈ DSet Ω[R] W) :
    ∃ m ∈ MGrp Ω[R] W, conjSub m K = J₀ := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g := h2Of H
  have hK : K ∈ Ω[R] := hd.mem
  have c : Q3CL.Thompson.Ctx Ω[R] W := Q3CL.T8.ctxOf hP H.hW
  have hKsyl : IsSylow2In K K := ⟨le_rfl, h2g K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Asc77.Thompson.Rep Ω[R] W, ρ.K = K :=
    ⟨Q3CL.T8.mkRep hP H.hW hK H.hK hKsyl, rfl⟩
  have hJ₀Ω : J₀ ∈ Ω[R] := by
    have := hJ₀.1
    rwa [rSet_eq_of_isPGroup h2g] at this
  have hJ₀syl : IsSylow2In J₀ J₀ :=
    ⟨le_rfl, h2g J₀ hJ₀Ω, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨σ, hσK⟩ : ∃ σ : Asc77.Thompson.Rep Ω[R] W, σ.K = J₀ :=
    ⟨Q3CL.T8.mkRep hP H.hW hJ₀Ω hJ₀ hJ₀syl, rfl⟩
  have hnc : ¬ DbarConnected Ω[R] W :=
    not_dbarConnected_of_wyl' hP hd (kPerp_datum hStd.perp hd.mem hd.hz) H.hW ρ hρK (hStd.wyl W H.hW)
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hP.cls hnc ρ σ
  exact ⟨m, hm, by rw [← hσK, ← hmK, hρK]⟩

theorem M_le_pSpan : MGrp Ω[R] W ≤ pSpan (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) := by
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨m, hm, rfl⟩ := exists_M_conj_of_mem_D H hJ
  exact le_pSpan (conjSub_mem_ae6ConjIn (M_le_ae6I _ _ _ hm))

theorem K₄_mem_D : K₄ ∈ DSet Ω[R] W := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have hF := H.ex.2.1
  have hz₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  exact twin_mem_DSet hP (h2Of H) H.hW (tmemW H) hF.1.1 hz₄

theorem fourTwins_of : FourTwins (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) t K K' K₃ K₄ := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hF := H.ex.2.1
  have hz₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  have mem : ∀ {J : Subgroup Y}, J ∈ DSet Ω[R] W →
      J ∈ ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K := by
    intro J hJ
    obtain ⟨m, hm, rfl⟩ := exists_M_conj_of_mem_D H hJ
    exact conjSub_mem_ae6ConjIn (M_le_ae6I _ _ _ hm)
  exact ⟨mem_ae6ConjIn_self, mem H.hK', mem H.hK₃, mem (K₄_mem_D H), hd.hz, hd.hzK', hd.hzK₃, hz₄,
    hd.hne.symm, hd.hK₃K.symm, hF.2.1.symm, hd.hK₃K'.symm, hF.2.2.1.symm, hF.2.2.2.1.symm⟩

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
