module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.G2Side

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


theorem g2ThreeClass_holds : G2ThreeClass := by
  intro K _ _ h5 t htγ ht3 ht1
  classical
  have hK3 : ringChar K ≠ 3 := by omega
  have hK2 : ringChar K ≠ 2 := by omega
  have hK4 : 4 ≤ Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hn]
    calc 4 ≤ ringChar K := by omega
      _ = ringChar K ^ 1 := (pow_one _).symm
      _ ≤ ringChar K ^ (n : ℕ) := Nat.pow_le_pow_right hpr.pos n.pos
  have hK3' : 3 ≤ Nat.card K := by omega
  set Φ := fixSubgroupEquivG2 K hK3'
  set y : ↥(fixSubgroup (d4Graph K 1)) := ⟨t, mem_fixSubgroup.2 htγ⟩
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simp [y, ht3])
  have hy1 : y ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hz3 : Φ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hz1 : Φ y ≠ 1 := fun h => hy1 (Φ.injective (h.trans (map_one Φ).symm))
  obtain ⟨g, j, A, hj⟩ := g2_exists_conj_simpleRootSL2 hK3 hK4 hz3 hz1
  have hinj := simpleRootSL2_injective (τ := Tag.G2) (K := K) hK2 j
  have hA3 : A ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one, ← hj, ← Subgroup.coe_pow, conj_pow, hz3]
    simp
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [map_one] at hj
    have h1 : g * Φ y * g⁻¹ = 1 := Subtype.ext hj
    exact hz1 (by
      calc Φ y = g⁻¹ * (g * Φ y * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
  set h := Φ.symm g
  have hΦ : Φ (h * y * h⁻¹) = g * Φ y * g⁻¹ := by simp [h]
  have hhγ : d4Graph K 1 (h : ↥(adjointGroup Tag.D4 K)) = h := mem_fixSubgroup.1 h.2
  refine ⟨h, A, hhγ, hA3, hA1, ?_⟩
  fin_cases j
  · left
    have e : h * y * h⁻¹ = sl2TwoFix A :=
      Φ.injective (Subtype.ext (by rw [hΦ, hj, fixSubgroupEquivG2_sl2Two]))
    exact congrArg Subtype.val e
  · right
    have e : h * y * h⁻¹ = sl2ShortFix A :=
      Φ.injective (Subtype.ext (by rw [hΦ, hj, fixSubgroupEquivG2_sl2Short]))
    exact congrArg Subtype.val e

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd
