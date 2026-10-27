module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015Four
public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM5Lemmas
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4

theorem isA6_group_simple (i : TauCeti.CFSGIndex) (hi : S8.isA6 i) : IsSimpleGroup i.Group := by
  cases i with
  | cyclic p hp => rcases hi with h | h <;> exact (show False from h).elim
  | alternating n hn =>
    rcases hi with h | h
    · have h6 : n = 6 := h
      subst h6
      show IsSimpleGroup (alternatingGroup (Fin 6))
      exact alternatingGroup.isSimpleGroup (by norm_num [Nat.card_eq_fintype_card])
    · exact h.elim
  | sporadic s => rcases hi with h | h <;> exact h.elim
  | lie j =>
    rcases hi with h | h
    · exact h.elim
    · rcases j with ⟨d, hv⟩
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact h.elim
        · have h9 : q.card = 9 := h
          haveI : Fact q.p.Prime := ⟨q.prime_p⟩
          have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
            rw [TauCeti.PrimePower.card_def]
            exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
          let ePSL := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
          haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
              (GaloisField q.p q.exponent)) :=
            Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK, h9]; norm_num)
          exact ePSL.isSimpleGroup
        · exact h.elim
      | _ => exact h.elim

theorem isA6_isSimpleGroup {S : Type} [Group S] (hS : catalogIs S S8.isA6) :
    IsSimpleGroup S ∧ Nat.card S = 360 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  haveI := isA6_group_simple i hi
  exact ⟨e.isSimpleGroup, by rw [Nat.card_congr e.toEquiv, SFM5.card_of_isA6 i hi]⟩

theorem u5_equiv_statedSU {G : Type} [Group G] (hG : catalogIs G S8.L89.isU5of2) :
    Nonempty (G ≃* StatedSU 5 2 K4) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.I1015.equiv_projSU_five (M := G) hG
  obtain ⟨e2⟩ : Nonempty (CFSG.Assembly.RankThreeEven.projSU 5 2 1 ≃*
      StatedProj (StatedSU 5 2 K4)) := ⟨CFSG.PGLModel.projSUEquivStatedProj 5 2 1⟩
  exact ⟨e1.trans (e2.trans (statedProjSUEquiv (by norm_num) (by norm_num)))⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

end
