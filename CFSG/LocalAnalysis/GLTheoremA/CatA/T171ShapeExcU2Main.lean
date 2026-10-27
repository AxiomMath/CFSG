module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172InnerConj
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk centerQuotientHom_injective)


theorem exit_of_indAut {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (hH : ExcSmallExit) (hS : Setup p L J A d b)
    (hcatE : catalogIs (PSimple p L) (onLie fun i : TauCeti.LieTypeIndex =>
      KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2))
    (hshape : ¬ I171.I171LieShapeAt p L) (hin : InducesInnerMod p L b)
    (hMI : MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) ∨
      Nat.card (PSimple p J) = 360) :
    InnDiagOn p (Subgroup.zpowers b) J := by
  have hqJ : CFSG.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open
      (isQuasisimple_pQuot_of_glaPComponent hS.prime hS.pcomp)
  rcases hMI with hMI | h360
  · rcases hS.chevJ with hon | hamb
    · obtain ⟨i, hi, ⟨e⟩⟩ := hon
      cases i with
      | cyclic _ _ => exact absurd hi (by simp [onLie])
      | alternating _ _ => exact absurd hi (by simp [onLie])
      | sporadic _ => exact absurd hi (by simp [onLie])
      | lie dd =>
        obtain ⟨idx, hv⟩ := dd
        have hval := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        cases idx with
        | A n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_A n q]; exact hi
          exact innAutDerivedInnDiag_linear p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.A n q, hv⟩, ⟨n, q, rfl, hq2⟩, ⟨e⟩⟩ hMI
        | twistedA n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedA n q]; exact hi
          exact innAutDerivedInnDiag_unitary p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.twistedA n q, hv⟩, ⟨n, q, rfl, hq2⟩, ⟨e⟩⟩ hMI
        | D n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_D n q]; exact hi
          by_cases hn4 : n = 4
          · subst hn4
            exact innDiagOn_of_inducesInnerMod_setup hS
              (hH p L J A d b hS hcatE hshape hin
                (Or.inr (Or.inl ⟨.lie ⟨.D 4 q, hv⟩, Or.inl ⟨q, rfl, hq2⟩, ⟨e⟩⟩)) (Or.inl hMI))
          · have hr : 4 ≤ n := by
              have h := hval.1
              simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
              omega
            exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
              ⟨.lie ⟨.D n q, hv⟩, ⟨by omega, hq2⟩, ⟨e⟩⟩ hMI
        | tits =>
          exact innDiagOn_of_inducesInnerMod_setup hS
            (hH p L J A d b hS hcatE hshape hin
              (Or.inr (Or.inl ⟨.lie ⟨.tits, hv⟩, Or.inr rfl, ⟨e⟩⟩)) (Or.inl hMI))
        | reeG2 m =>
          exact absurd (hi.symm.trans (TauCeti.LieTypeIndex.characteristic_reeG2 m)) (by norm_num)
        | B n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_B n q]; exact hi
          have hr : 2 ≤ n := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.B n q, hv⟩, ⟨hr, hq2⟩, ⟨e⟩⟩ hMI
        | C n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_C n q]; exact hi
          have hr : 3 ≤ n := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.C n q, hv⟩, ⟨by omega, hq2⟩, ⟨e⟩⟩ hMI
        | twistedD n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedD n q]; exact hi
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.twistedD n q, hv⟩,
              ⟨TauCeti.LieTypeIndex.four_le_of_twistedD_inStandardRange hval.1, hq2⟩,
              ⟨e⟩⟩ hMI
        | G2 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_G2]; exact hi
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.G2 q, hv⟩, hq2, ⟨e⟩⟩ hMI
        | F4 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_F4]; exact hi
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.F4 q, hv⟩, hq2, ⟨e⟩⟩ hMI
        | E6 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E6]; exact hi
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.E6 q, hv⟩, hq2, ⟨e⟩⟩ hMI
        | E7 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E7]; exact hi
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.E7 q, hv⟩, hq2, ⟨e⟩⟩ hMI
        | E8 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E8]; exact hi
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.E8 q, hv⟩, hq2, ⟨e⟩⟩ hMI
        | twistedE6 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedE6]; exact hi
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.twistedE6 q, hv⟩, hq2, ⟨e⟩⟩ hMI
        | trialityD4 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_trialityD4]; exact hi
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.trialityD4 q, hv⟩, hq2, ⟨e⟩⟩ hMI
        | suzuki m =>
          have hr : 1 ≤ m := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.suzuki m, hv⟩, hr, ⟨e⟩⟩ hMI
        | reeF4 m =>
          have hr : 1 ≤ m := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact innAutDerivedInnDiag_rest p J b hS.b_norm hS.prime hqJ
            ⟨.lie ⟨.reeF4 m, hv⟩, hr, ⟨e⟩⟩ hMI
    · exact innDiagOn_of_inducesInnerMod_setup hS
        (hH p L J A d b hS hcatE hshape hin (Or.inl hamb) (Or.inl hMI))
  · exact innDiagOn_of_inducesInnerMod_setup hS
      (hH p L J A d b hS hcatE hshape hin (Or.inr (Or.inr h360)) (Or.inr h360))



end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
