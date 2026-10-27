module

public import CFSG.LieType.ChevTwo.OppCl.G2Core
public import CFSG.LieType.ChevTwo.OppCl.G2NormalForm

public section

namespace CFSG.LieType.ChevTwo.OppCl

section G2

open CFSG.Blueprint

theorem oppositeFixed_G2
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    OppositeFixed (AdjointQuotient Chevalley.Tag.G2 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra h
    have h1 : (n : ℕ) ≤ 1 := by omega
    have : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hΓ, -, -, -, ⟨Ψ, -, -, -⟩, -⟩ :=
    CFSG.RankThree.PartTwo.KFacts.even_D4_pure_graph_fixed_group_exact_G2 (K := K) hchar
  have e : AdjointQuotient Chevalley.Tag.G2 K ≃*
      ↥(Chevalley.graphFixedRootGroup Chevalley.TwistTag.D4 K (RingHom.id K)) :=
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Chevalley.Tag.G2) (K := K))).trans
      QuotientGroup.quotientBot).trans (Ψ.symm.trans (MulEquiv.subgroupCongr hΓ))
  refine oppositeFixed_of_mulEquiv e ?_
  have h1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
  have := CFSG.LieType.ChevTwo.Semi.oppositeFixed_graphFixedRootGroup_D4_of_nf (K := K) 1
    (one_pow 3) (by rw [h1]; exact CFSG.LieType.ChevTwo.Semi.uniqueNormalFormOn_G2 hn2 hKn)
  rwa [h1] at this

end G2

end CFSG.LieType.ChevTwo.OppCl
