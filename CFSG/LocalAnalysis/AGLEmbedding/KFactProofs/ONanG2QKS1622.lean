module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QHeis
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QUnip
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QSU33
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail22

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding.KFactProofs.G2Q

theorem exists_threePair_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ x y : Y, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set Y))) :
    ∃ x y : X, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set X)) := by
  obtain ⟨x, y, hx, hy, hxy, hP⟩ := h
  refine ⟨e.symm x, e.symm y, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hx, map_one]
  · rw [← map_pow, hy, map_one]
  · intro h
    apply hxy
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h
  · have hcl : Subgroup.closure ({e.symm x, e.symm y} : Set X) =
        (Subgroup.closure ({x, y} : Set Y)).map e.symm.toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [hcl]
    exact hP.map _

theorem ks1622GTwo :
    KS1622GTwo := by
  intro X _ _ hX
  rcases hX with ⟨p, f, ⟨hp, -⟩, K, _, _, hK, ⟨e₀⟩⟩ | ⟨⟨e⟩⟩
  · have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
    let e : X ≃* adjointGroup .G2 K :=
      e₀.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)
    refine exists_threePair_of_mulEquiv e ?_
    by_cases hp3 : p = 3
    · subst hp3
      have : Fact (Nat.Prime 3) := ⟨hp⟩
      have : Fintype K := Fintype.ofFinite K
      have : CharP K 3 := charP_of_card_eq_prime_pow (f := f)
        (by rw [← Nat.card_eq_fintype_card]; exact hK)
      exact exists_pair_char_three
    · refine exists_pair_not_dvd_three ?_
      rw [hK]
      intro hd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow hd)).symm
  · exact exists_pair_projSU33 e

end CFSG.RankThree.PartTwo.Sec16
