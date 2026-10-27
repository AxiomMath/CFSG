module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporFix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M23
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HSThree

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.RankThree.LocalRank CFSG.Blueprint

@[expose] def ThetaCentOf (s : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier s) →
    ∀ b : X, b ^ 3 = 1 → b ≠ 1 →
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) = ⊥

theorem k423SporThetaCent_of
    (hHe : ThetaCentOf .He) (hRu : ThetaCentOf .Ru) :
    CFSG.RankThree.PartTwo.Sec4.K423SporThetaCent := by
  intro X _ _ ⟨s, hs, ⟨e⟩⟩ b hb3 hb1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact ThreeCore.M23.thetaCent_of_m23 e b hb3 hb1
  · exact ThreeCore.M24.thetaCent_of_m24 e b hb3 hb1
  · exact ThetaSpor.thetaCent_of_hs e b hb3 hb1
  · exact hHe X ⟨e⟩ b hb3 hb1
  · exact hRu X ⟨e⟩ b hb3 hb1

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
