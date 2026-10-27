module

public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
import CFSG.LieType.SeitzGeneration.OmegaF2.BridgeCore
import CFSG.ClassicalGroups.SpecialLinear.InvolutionInverts
import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix QuadraticMap CFSG.LieType.SeitzGeneration.RootPairOrth CFSG.RankThree.PartOne.CTP

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem quadHom_injective_of_orth {P P' : HypPair Q} (h : P.Orth P') :
    Function.Injective (quadHom h) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 := CFSG.LieType.SeitzGeneration.OmegaF2.quadHom_apply_quadEmb h A 1
  rw [hA, mul_one] at h1
  have h2 : quadEmb P P' (A : Matrix (Fin 2) (Fin 2) K) = quadEmb P P' 1 := h1.symm
  have h3 := congrArg (quadProj P P') h2
  rw [quadProj_emb h, quadProj_emb h] at h3
  exact Subtype.ext h3

theorem quadHom_mem_elementaryGroup {P P' : HypPair Q} (h : P.Orth P')
    (A : SpecialLinearGroup (Fin 2) K) : quadHom h A ∈ elementaryGroup Q := by
  have htop : (elementaryGroup Q).comap (quadHom h) = ⊤ := by
    refine CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem _ ?_
    intro i j hij c
    rw [Subgroup.mem_comap]
    have key : SpecialLinearGroup.transvection hij c = u2 c ∨
        SpecialLinearGroup.transvection hij c = l2 c := by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hij
    rcases key with hk | hk <;> rw [hk]
    · rw [quadHom_u2]
      exact eichler_mem_elementaryGroup Q _ _
    · rw [quadHom_l2]
      exact eichler_mem_elementaryGroup Q _ _
  have hA : A ∈ (elementaryGroup Q).comap (quadHom h) := by
    rw [htop]
    exact Subgroup.mem_top A
  exact hA

theorem exists_orderOf_eq_card_add_one_conj_eichler [Finite K] [CharP K 2] {P R : HypPair Q}
    (h : P.Orth R) :
    ∃ g ∈ elementaryGroup Q, orderOf g = Nat.card K + 1 ∧
      eichler Q P.e R.e * g * (eichler Q P.e R.e)⁻¹ = g⁻¹ := by
  let P' : HypPair Q := ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩
  let R' : HypPair Q := ⟨R.f, R.e, R.Q_f, R.Q_e, R.polar_fe⟩
  have h' : P'.Orth R' := ⟨h.ff, h.fe, h.ef, h.ee⟩
  obtain ⟨S, hSo, hS⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_orderOf_eq_card_add_one_conj_eq_inv (K := K)
  have hl : quadHom h' (l2 1) = eichler Q P.e R.e := by
    rw [quadHom_l2, one_smul]
  have hSinv : l2 (1 : K) * S * l2 1 = S⁻¹ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hS
  refine ⟨quadHom h' S, quadHom_mem_elementaryGroup h' S, ?_, ?_⟩
  · rw [orderOf_injective (quadHom h') (quadHom_injective_of_orth h') S, hSo]
  · rw [← hl, ← map_inv, ← map_mul, ← map_mul,
      inv_eq_of_mul_eq_one_right (l2_mul_self (1 : K)), hSinv, map_inv]

end CFSG.ClassicalGroups.Orthogonal
