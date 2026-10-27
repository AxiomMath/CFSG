module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts
public import CFSG.Literature.GL52
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL52
public import CFSG.Quasithin.H13.A7Nat1233ModAbs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.RankThree.LocalRank Subgroup
open CFSG.Assembly.RankThreeEven (projSL)

theorem thetaCent_gl52
    (τ : CFSG.Literature.GL52.G)
    (hτ : orderOf τ = 3) :
    aschbacherSolvableCore 3 (centralizer ({τ} : Set CFSG.Literature.GL52.G)) = ⊥ := by
  have h3 : τ ^ 3 = 1 := hτ ▸ pow_orderOf_eq_one τ
  rcases CFSG.Literature.GL52.order_three_centralizer hτ with
    ⟨-, K, hK, -, hsup, ⟨e⟩⟩ | ⟨-, K, hK, -, hsup, -, ⟨e⟩⟩
  · have : IsSimpleGroup K := e.isSimpleGroup
    refine aschbacherSolvableCore_eq_bot_of_simple_complement h3 hK hsup ?_
    obtain ⟨a, b, hab⟩ : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by decide
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  · have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := CFSG.Quasithin.H13.A7.isSimpleGroup_GL_three_two_four
    have : IsSimpleGroup K := e.isSimpleGroup
    refine aschbacherSolvableCore_eq_bot_of_simple_complement h3 hK hsup ?_
    have hcard : Nat.card K = 168 := by
      rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]
      simp [Fin.prod_univ_three]
    exact exists_mul_ne_of_isSimpleGroup hcard (by norm_num) (by norm_num)

theorem thetaCent_of_l52
    {X : Type} [Group X] [Finite X]
    (e : X ≃* projSL 5 (GaloisField 2 1)) (b : X) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    aschbacherSolvableCore 3 (centralizer ({b} : Set X)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e' : X ≃* CFSG.Literature.GL52.G :=
    e.trans CFSG.RankThree.PartTwo.Sec4.Res417Four.gl5EquivProjSL.symm
  rw [ThreeCore.aschbacherSolvableCore_three_centralizer_eq_bot_iff e' b]
  refine thetaCent_gl52 (e' b) ?_
  rw [MulEquiv.orderOf_eq]
  exact orderOf_eq_prime hb3 hb1

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
