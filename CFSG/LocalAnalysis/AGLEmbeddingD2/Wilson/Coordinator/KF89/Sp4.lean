module

public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89
public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89G2
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
public import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec4 (InducesOuterTheta)
open CFSG.Assembly.RankThreeEven (projSp)


theorem projSp_and_barCentralizer {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hout : InducesOuterTheta a X)
    (hJ : Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
      alternatingGroup (Fin 6))) :
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) ∧
      Nonempty (barCentralizer (Subgroup.zpowers a) X ≃* projSp 2 (GaloisField 2 1)) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hSp8 : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) := by
    obtain ⟨d, m, -, -, hm, hcases⟩ := h.mem_pairOmega.2.2.2.2.2
    rcases hcases with ⟨k, hk, -, he, -⟩ | ⟨hX, -⟩
    · exact absurd hJ (kF89ReeF4 G X a k hk he ha3 hout)
    rcases hX with ⟨q, hq, hq2, hqe, he⟩ | ⟨q, hq2, -, hG⟩ | hU | hSU | hSp
    · exact absurd hJ
        (KFacts.not_nonempty_perfectResidual_mulEquiv_alternatingGroup_six_of_isoGTwoEven
          (h.gTwoPartner m (Or.inl ⟨q, hq, hq2, hqe, he⟩)))
    · exact absurd hJ (kF89GTwo G X a q hq2 hG ha3 hout)
    · exact absurd (Or.inl hU) (h.not_unitary (3 * m))
    · exact absurd (Or.inr hSU) (h.not_unitary (3 * m))
    · obtain ⟨-, hC⟩ := KFacts.barCentralizer_mulEquiv_projSp (by omega) ha3 hout hSp
      have hm1 : m = 1 :=
        KFacts.eq_one_of_perfectResidual_mulEquiv_alternatingGroup_six_of_projSp hm hC hJ
      subst hm1
      simpa using hSp
  refine ⟨hSp8, ?_⟩
  obtain ⟨-, hC⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := 1) (by norm_num) ha3 hout
    (by simpa using hSp8)
  exact hC

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89
