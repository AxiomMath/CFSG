module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TC.Thin

section Tri

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

structure Q8Pre (G : Type) [Group G] [Finite G] (Φ : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Φ
  two : ∀ L ∈ Φ, IsPGroup 2 L
  q8 : ∀ L ∈ Φ, Nonempty (↥L ≃* QuaternionGroup 2)
  aEmpty : ∀ L ∈ Φ, AEmpty Φ L
  gen : pSpan Φ = ⊤
  trans : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : G, conjSub g L = L'
  oddFree : classicalInvolutionOddCore G = ⊥

theorem Q8Pre.toFam (F : Q8Pre G Φ) (h : ∀ L ∈ Φ, ∀ u : G, IsUniqueInvolution L u →
    ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 ↥Q ∧ u ∈ Q) : TwinDisc.ExitO2.Q8Fam G Φ :=
  ⟨F.hyp, F.two, F.q8, F.aEmpty, F.gen, F.trans, F.oddFree, h⟩

theorem conjClass_eq (F : Q8Pre G Φ) {K : Subgroup G} (hK : K ∈ Φ) :
    CoreAssembly.conjClass K = Φ := by
  ext L
  constructor
  · rintro ⟨g, rfl⟩
    exact F.hyp.conjInvariant g K hK
  · intro hL
    obtain ⟨g, hg⟩ := F.trans K hK L hL
    exact ⟨g, hg⟩

theorem trichotomy_at {n : ℕ} (H : Thm1RTwinLiftSetEBelow n) (hlt : Nat.card G < n) (F : Q8Pre G Φ)
    {K K' : Subgroup G} (hK : K ∈ Φ) (hK' : K' ∈ twinSet Φ K) (hne : K' ≠ K) {t : G}
    (ht : IsUniqueInvolution K t) : TightInO2 t ∨ TwinE4 G ∨ LongFundSetE3 K t := by
  obtain S : Sylow 2 ↥K := Classical.choice inferInstance
  obtain ⟨hd, hSq⟩ := q8TwinDatum_of_isPGroup (F.two K hK) S ht (F.q8 K hK)
  have htc : tightCore K = K := tightCore_eq_self_of_isPGroup (F.two K hK)
  have hΦ := conjClass_eq F hK
  have hgen : TightSelfGen K := by
    unfold TightSelfGen
    rw [htc, eq_top_iff, ← F.gen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨g, hg⟩ := F.trans K hK L hL
    rw [← hg]
    exact le_iSup (fun g : G => conjSub g K) g
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore K)) := by
    rw [htc, hΦ]; exact F.hyp
  have hA : AEmpty (CoreAssembly.conjClass (tightCore K)) (tightCore K) := by
    rw [htc, hΦ]; exact F.aEmpty K hK
  have htw : ∃ K'' ∈ twinSet (CoreAssembly.conjClass (tightCore K)) (tightCore K),
      K'' ≠ tightCore K := by
    rw [htc, hΦ]; exact ⟨K', hK', hne⟩
  exact H G hlt K S t hd hSq hgen F.oddFree hΩ hA htw

end Tri

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
