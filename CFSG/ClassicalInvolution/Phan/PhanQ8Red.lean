module

public import CFSG.ClassicalInvolution.Phan.PhanQ7Dict
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

section PairFacts

variable {F : Type} [Field F]

@[expose] def PairPent (ε : F) : Prop :=
  ∀ a c d : NPair ε, ColP ε c d → ∃ f : NPair ε, ColP ε f c ∧ ColP ε f d ∧ ColP ε a f

end PairFacts

section Red

variable {p e : ℕ} [Fact p.Prime]

theorem apexPentagon_of_pairPent (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (H : PairPent M.ε) : ApexPentagon (G := ptGraph M.S) := by
  have h2 := two_ne_zero_gf hp2 e
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  intro a c d hcd
  obtain ⟨ga, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨gc, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨gd, rfl⟩ := QuotientGroup.mk_surjective d
  obtain ⟨z, hzc, hzd, hza⟩ := H (ga • z0 M.ε) (gc • z0 M.ε) (gd • z0 M.ε)
    ((adj_iff M hp2 hq gc gd).1 hcd)
  obtain ⟨gf, rfl⟩ := exists_smul_z0 h2 hodd M.hε M.h4 z
  exact ⟨(gf : _ ⧸ parab M.S {1, 2, 3}), (adj_iff M hp2 hq gf gc).2 hzc,
    (adj_iff M hp2 hq gf gd).2 hzd, (adj_iff M hp2 hq ga gf).2 hza⟩

end Red

section Assembly

@[expose] def ConeFact {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    {G : Type} [Group G] (S : PhanFamilyD4 K p f G) (h0 : PtStep0 S) : Prop :=
  ∀ (a b c : G ⧸ parab S {1, 2, 3}) (hab : (ptGraph S).Adj a b) (hbc : (ptGraph S).Adj b c)
    (hca : (ptGraph S).Adj c a),
    ∃ (e : G ⧸ parab S {1, 2, 3}) (hae : (ptGraph S).Adj a e) (hbe : (ptGraph S).Adj b e)
      (hce : (ptGraph S).Adj c e),
      SolidNull S h0 (.cons hab (.cons hbe (.cons hae.symm .nil)) : (ptGraph S).Walk a a) ∧
      SolidNull S h0 (.cons hbc (.cons hce (.cons hbe.symm .nil)) : (ptGraph S).Walk b b) ∧
      SolidNull S h0 (.cons hca (.cons hae (.cons hce.symm .nil)) : (ptGraph S).Walk c c)

end Assembly

end CFSG.ClassicalInvolution.PhanQ
