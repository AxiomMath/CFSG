module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem ctrQ_dvd_of_walterChain [Finite G] {X Y : Subgroup G} (h : WalterChain X Y) :
    ctrQ X ∣ ctrQ Y := by
  unfold WalterChain at h
  induction h with
  | refl => exact dvd_refl _
  | tail hab hbc ih =>
      rcases hbc with hstep | hstep
      · exact Nat.dvd_trans ih (ctrQ_dvd_of_walterArrow hstep).1
      · exact Nat.dvd_trans ih (ctrQ_dvd_of_walterArrowDiag hstep).1

theorem nonempty_equiv_of_walterChain [Finite G] {X Y : Subgroup G} (h : WalterChain X Y)
    (hc : ctrQ X = ctrQ Y) : Nonempty (X ⧸ center X ≃* Y ⧸ center Y) := by
  unfold WalterChain at h
  revert hc
  induction h with
  | refl =>
      intro _
      exact ⟨MulEquiv.refl _⟩
  | @tail Z W hab hbc ih =>
      intro hc
      rcases hbc with hstep | hstep
      · exfalso
        have h1 : ctrQ X ∣ ctrQ Z := ctrQ_dvd_of_walterChain hab
        have h2 : ctrQ Z ∣ ctrQ X := by
          rw [hc]
          exact (ctrQ_dvd_of_walterArrow hstep).1
        exact (ctrQ_dvd_of_walterArrow hstep).2
          ((Nat.dvd_antisymm h1 h2).symm.trans hc)
      · have h1 : ctrQ X ∣ ctrQ Z := ctrQ_dvd_of_walterChain hab
        have h2 : ctrQ Z ∣ ctrQ X := by
          rw [hc]
          exact (ctrQ_dvd_of_walterArrowDiag hstep).1
        have hYX : ctrQ X = ctrQ Z := Nat.dvd_antisymm h1 h2
        obtain ⟨e1⟩ := ih hYX
        obtain ⟨e2⟩ := (ctrQ_dvd_of_walterArrowDiag hstep).2 (hYX.symm.trans hc)
        exact ⟨e1.trans e2⟩

private theorem inC_of_walterChain {X Y : Subgroup G} (h : WalterChain X Y) (hX : InC X) :
    InC Y := by
  unfold WalterChain at h
  induction h with
  | refl => exact hX
  | tail _hab hbc _ih =>
      rcases hbc with hstep | hstep
      · unfold WalterArrow at hstep
        obtain ⟨_, y, -, hy, -, -, hYc, -, -⟩ := hstep
        exact ⟨y, hy, hYc⟩
      · unfold WalterArrowDiag at hstep
        obtain ⟨_, y, -, hy, -, -, hYc, -, -⟩ := hstep
        exact ⟨y, hy, hYc⟩

theorem inCStar_of_ctrQ_maximal [Finite G] (hA : AschA2 G) {X : Subgroup G} (hC : InC X)
    (hF : InFStar X)
    (hmax : ∀ Y : Subgroup G, InC Y → InFStar Y → ctrQ X ∣ ctrQ Y → ctrQ Y = ctrQ X) :
    InCStar X := by
  refine ⟨hC, fun Y hY => ?_⟩
  have hCY : InC Y := inC_of_walterChain hY hC
  have hFY : InFStar Y := inFStar_of_walterChain hA hY hF
  have hdvd : ctrQ X ∣ ctrQ Y := ctrQ_dvd_of_walterChain hY
  exact nonempty_equiv_of_walterChain hY (hmax Y hCY hFY hdvd).symm

theorem exists_inCStar_of_inC [Finite G] {X : Subgroup G} (hC : InC X) :
    ∃ Y : Subgroup G, WalterChain X Y ∧ InCStar Y := by
  classical
  have hfin : ({Y : Subgroup G | WalterChain X Y} : Set (Subgroup G)).Finite :=
    Set.toFinite _
  obtain ⟨Y, hY, hmax⟩ := Set.exists_max_image {Y : Subgroup G | WalterChain X Y} ctrQ hfin
    ⟨X, Relation.ReflTransGen.refl⟩
  refine ⟨Y, hY, ?_⟩
  refine ⟨inC_of_walterChain hY hC, fun Y' hYY' => ?_⟩
  have hXY' : WalterChain X Y' := WalterChain.trans hY hYY'
  have hle : ctrQ Y' ≤ ctrQ Y := hmax Y' hXY'
  have hdvd : ctrQ Y ∣ ctrQ Y' := ctrQ_dvd_of_walterChain hYY'
  have hpos : 0 < ctrQ Y' := Nat.card_pos
  have heq : ctrQ Y' = ctrQ Y := le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  exact nonempty_equiv_of_walterChain hYY' heq.symm

end CFSG.OddStandard.SmallF3.Omega
