module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameConn

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TL4

namespace TwinFrame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem alphaOf_eq_bot_of_mem_frameSet_hyp51 (hO : componentClassificationOddCore G = ⊥)
    (hΩ : HypOmegaGen Ω) (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N)
    (hconn : DConnected Ω) (hhyp : ∀ A ∈ frameSet Ω, Hyp51 A) {B : Subgroup G}
    (hB : B ∈ frameSet Ω) : ∀ F ∈ signalizerFunctorEk 2 2 B, alphaOf F = ⊥ := by
  intro F hF
  have hbal : ∀ A ∈ frameSet Ω, RankThreeBalance A := fun A hA => lemma52 G A (hhyp A hA)
  exact alphaOf_eq_bot_of_alphaCore_eq_bot
    (Theorem5.alphaCore_eq_bot_of_connected_frames hO
      (fun A hA g => frameSet_conj hΩ.conjInvariant hA g) hbal
      (frameSet_connected hΩ htr hconn) B hB F hF)

theorem theorem5_twin_hyp51 (hO : componentClassificationOddCore G = ⊥) (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N) (hconn : DConnected Ω)
    (hhyp : ∀ A ∈ frameSet Ω, Hyp51 A) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) :
    alphaOf (Subgroup.closure ({z, u} : Set G)) = ⊥ ∧
      alphaOf (Subgroup.closure ({z, t} : Set G)) = ⊥ := by
  have key := alphaOf_eq_bot_of_mem_frameSet_hyp51 hO hΩ htr hconn hhyp (closure_mem_frameSet h)
  exact ⟨key _ (closure_zu_mem h), key _ (closure_zt_mem hΩ h)⟩

theorem alpha_edge_hyp51 (hO : componentClassificationOddCore G = ⊥) (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N) (hconn : DConnected Ω)
    (hgen : (⨆ J ∈ Ω, J) = ⊤) (hZ : Subgroup.center G = ⊥)
    (hhyp : ∀ A ∈ frameSet Ω, Hyp51 A) {K₀ K₀' : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hK₀' : K₀' ∈ twinSet Ω K₀) (hne₀ : K₀' ≠ K₀) {M N : Subgroup G} (hM : M ∈ Ω)
    (hMN : N ∈ omegaNbr Ω M) {zM zN : G} (hzM : IsUniqueInvolution M zM)
    (hzN : IsUniqueInvolution N zN) (hne : zM ≠ zN) :
    alphaOf (Subgroup.closure ({zM, zN} : Set G)) = ⊥ := by
  obtain ⟨M', hM', hM'ne⟩ := exists_twin_of_trans hΩ htr hK₀ hK₀' hne₀ hM
  obtain ⟨u, J, t, h⟩ := exists_frame hΩ hconn hgen hZ hM hzM hM' hM'ne
  have hNnot : N ∉ twinSet Ω M := by
    rintro ⟨-, z', hz'M, hz'N⟩
    exact hne ((hzM.eq hz'M).trans (hzN.eq hz'N).symm)
  have hNo : N ∈ omegaOfSet Ω (twinSet Ω M) :=
    A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ hM (Set.mem_insert_of_mem _ hMN) hNnot
  obtain ⟨u', h', -⟩ := exists_frame_at_J hΩ h hNo hzN
  exact (theorem5_twin_hyp51 hO hΩ htr hconn hhyp h').2

end TwinFrame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
