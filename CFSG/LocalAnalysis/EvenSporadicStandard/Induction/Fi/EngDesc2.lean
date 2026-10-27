module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.EngDesc1
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.EngLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Step23
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.Eng

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {IsK : GroupClass}
  {S Up Lo : List TauCeti.SporadicName} {R : GroupClass}

theorem cqCard_le_card (X : Subgroup H) : cqCard X ≤ Nat.card H := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥X)
  have h2 : 0 < Nat.card (center ↥X) := Nat.card_pos
  have h3 := Subgroup.card_le_card_group X
  unfold cqCard
  nlinarith

theorem chain_down {m : ℕ} (Φ : ℕ → Prop) (htop : Φ m)
    (hstep : ∀ i, 1 ≤ i → i ≤ m → Φ i → Φ (i - 1)) : ∀ i, i ≤ m → Φ i := by
  have key : ∀ j, j ≤ m → Φ (m - j) := by
    intro j
    induction j with
    | zero => exact fun _ => htop
    | succ j ihj =>
      intro hj
      have := hstep (m - j) (by omega) (by omega) (ihj (by omega))
      have h : m - (j + 1) = m - j - 1 := by omega
      rw [h]
      exact this
  intro i hi
  have := key (m - i) (by omega)
  have h : m - (m - i) = i := by omega
  rwa [h] at this

theorem typeL_of_lt (junction : JunctionStmtAt H)
    (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H) (hUp : UpCtx S Up H)
    (rc : ReachFacts IsK S Up Lo R) (hKiso : IsK.IsoInv) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {K₁ A B : Subgroup H} (hK₁L : InL K₁) (hK₁ : KLike IsK K₁)
    (hKA : ReflTransGen Lt K₁ A) (hR : R (↥K₁ ⧸ center ↥K₁)) (hlt : cqCard K₁ < cqCard A)
    (hAB : Lt A B) (hB : ∃ s ∈ S, OddCover s B) : ∃ s ∈ S, OddCover s A := by
  by_cases hAB' : A = B
  · exact hAB' ▸ hB
  have hK₁' := hK₁
  obtain ⟨X, _, σ, hσ, hσk, hXK⟩ := hK₁'
  have : Group.IsPerfect ↥K₁ := hK₁L.isQuasisimple.1
  have hKX : Nonempty ((↥K₁ ⧸ center ↥K₁) ≃* (X ⧸ center X)) := cqEquiv_of_cover σ hσ hσk
  have hRA := reach_reflTransGen junction ih hUp rc hN hidx hkp hK₁L hK₁ hKA hR
  obtain ⟨m, L, T, s, hm, hch, h0, hT, -⟩ :=
    junction hkp N hN A B (lt_inL_left hAB) (lt_inL_right hAB) hAB hAB' (rc.not_exc _ hRA.1).1
      (rc.not_exc _ hRA.1).2
  have hL0 : InL (L 0) := by rw [h0]; exact lt_inL_left hAB
  have hRL := reach_chain ih hUp rc hN hidx hkp hch hT hL0 hK₁L hK₁ (by rw [h0]; exact hRA)
  have hmono : ∀ i, i ≤ m → cqCard A ≤ cqCard (L i) := fun i hi => by
    have := chain_zero_le hch i hi
    rwa [h0] at this
  have hlast : L m = B := hch.last
  have key := chain_down (m := m) (fun i => ∃ s ∈ S, OddCover s (L i)) (hlast ▸ hB) (by
    intro i hi him hLi
    rcases hch.link i hi him with h5a | h5b
    · obtain ⟨π, hπ, hk⟩ := chain_link5a_cover hch hi him h5a
      obtain ⟨s', hs', hcov⟩ := hLi
      exact ⟨s', hs', oddCover_of_cover hcov π hπ hk⟩
    · exfalso
      have hK := chain_link5b_isK ih hUp rc hKiso hN hidx hkp hch hT hL0 hK₁L hK₁ hi him h5b
        (hRL _ (by omega)) hLi
      have hPq : CFSG.IsQuasisimple ↥(L (i - 1)) := (hch.elem i hi him).2.2.2.isQuasisimple
      have : Group.IsPerfect ↥(L (i - 1)) := hPq.1
      obtain ⟨e₁⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥(L (i - 1))))
        (QuotientGroup.mk'_surjective _) (by
          rw [QuotientGroup.ker_mk']
          exact oddCore_le_center hPq)
      obtain ⟨e₂⟩ := rc.K_cq _ _ hK hXK
      obtain ⟨e₃⟩ := hKX
      have hP : cqCard (L (i - 1)) = cqCard K₁ :=
        Nat.card_congr (e₁.trans (e₂.trans e₃.symm)).toEquiv
      have := hmono (i - 1) (by omega)
      omega) 0 (Nat.zero_le _)
  rwa [h0] at key

theorem typeL_of_transGen (junction : JunctionStmtAt H)
    (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H) (hUp : UpCtx S Up H)
    (rc : ReachFacts IsK S Up Lo R) (hKiso : IsK.IsoInv) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {K₁ : Subgroup H} (hK₁L : InL K₁) (hK₁ : KLike IsK K₁)
    (hR : R (↥K₁ ⧸ center ↥K₁)) {A Y : Subgroup H} (hAY : TransGen Lt A Y)
    (hKA : ReflTransGen Lt K₁ A) (hlt : cqCard K₁ < cqCard A) (hY : ∃ s ∈ S, OddCover s Y) :
    ∃ s ∈ S, OddCover s A := by
  induction hAY using TransGen.head_induction_on with
  | single hlt' =>
    exact typeL_of_lt junction ih hUp rc hKiso hN hidx hkp hK₁L hK₁ hKA hR hlt hlt' hY
  | head hlt' hrest ihr =>
    rename_i a c
    have hKc : ReflTransGen Lt K₁ c := hKA.tail hlt'
    have hmono := (lt_step_data junction hkp hN hlt'
      (rc.not_exc _ (reach_reflTransGen junction ih hUp rc hN hidx hkp hK₁L hK₁ hKA hR).1)).1
    exact typeL_of_lt junction ih hUp rc hKiso hN hidx hkp hK₁L hK₁ hKA hR hlt hlt'
      (ihr hKc (by omega))

end CFSG.EvenSporadicStandard.Induction.Fi.Eng
