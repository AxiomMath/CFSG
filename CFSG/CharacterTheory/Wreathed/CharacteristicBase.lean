module

public import CFSG.CharacterTheory.Wreathed.BaseAndDerived
public import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem abelian_subgroup_outside_card_le (m : ℕ) (hm : 0 < m)
    (H : Subgroup (Wreath m)) (hH : IsMulCommutative H)
    (hout : ¬H ≤ baseSubgroup m) : Nat.card H ≤ 2 * m := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨w, hwH, hwU⟩ : ∃ w ∈ H, w ∉ baseSubgroup m := by
    by_contra h
    apply hout
    intro w hw
    by_contra hu
    exact h ⟨w, hw, hu⟩
  obtain ⟨⟨c, d, f⟩, hw⟩ := (coordinateEquiv m).symm.surjective w
  change element m c d f = w at hw
  have hf : f = 1 := by
    rcases swap_exponent_cases f with h | h
    · apply False.elim
      apply hwU
      rw [← hw, element_mem_base, h]
    · exact h
  rw [hf] at hw
  have hcomm (p : H) : Commute p.val (element m c d 1) := by
    have hpw := (isMulCommutative_iff.mp hH) p ⟨w, hwH⟩
    have heq := congrArg Subtype.val hpw
    change p.val * w = w * p.val at heq
    rw [← hw] at heq
    exact heq
  let encode : H → ZMod m × ZMod 2 := fun p =>
    ((coordinateEquiv m p.val).1, (coordinateEquiv m p.val).2.2)
  have hinj : Function.Injective encode := by
    intro x y hxy
    have hcx := hcomm x
    have hcy := hcomm y
    apply Subtype.ext
    obtain ⟨⟨a, b, e⟩, hx⟩ := (coordinateEquiv m).symm.surjective x.val
    obtain ⟨⟨u, v, t⟩, hy⟩ := (coordinateEquiv m).symm.surjective y.val
    change element m a b e = x.val at hx
    change element m u v t = y.val at hy
    have hencode : (a, e) = (u, t) := by
      change ((coordinateEquiv m x.val).1, (coordinateEquiv m x.val).2.2) =
        ((coordinateEquiv m y.val).1, (coordinateEquiv m y.val).2.2) at hxy
      rw [← hx, ← hy] at hxy
      exact hxy
    have ha := congrArg Prod.fst hencode
    have he := congrArg Prod.snd hencode
    change a = u at ha
    change e = t at he
    subst u
    subst t
    rw [← hx] at hcx
    rw [← hy] at hcy
    rw [← hx, ← hy]
    rcases swap_exponent_cases e with rfl | rfl
    · have hb := (base_commutes_swap_iff m a b c d).mp hcx
      have hv := (base_commutes_swap_iff m a v c d).mp hcy
      rw [← hb, ← hv]
    · have hb := (swap_commutes_swap_iff m a b c d).mp hcx
      have hv := (swap_commutes_swap_iff m a v c d).mp hcy
      have h : b = v := by linear_combination -hb + hv
      rw [h]
  have hcard := Nat.card_le_card_of_injective encode hinj
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at hcard
  omega

theorem abelian_subgroup_eq_base_of_card (m : ℕ) (hm : 2 < m)
    (H : Subgroup (Wreath m)) (hH : IsMulCommutative H) (hcard : Nat.card H = m ^ 2) :
    H = baseSubgroup m := by
  let : NeZero m := ⟨by omega⟩
  have hle : H ≤ baseSubgroup m := by
    by_contra hout
    have hb := abelian_subgroup_outside_card_le m (by omega) H hH hout
    rw [hcard] at hb
    nlinarith
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_base, hcard])

theorem unique_abelian_index_two (m : ℕ) (hm : 2 < m)
    (H : Subgroup (Wreath m)) (hH : IsMulCommutative H) (hindex : H.index = 2) :
    H = baseSubgroup m := by
  have hmul := H.card_mul_index
  rw [hindex, card_wreath] at hmul
  apply abelian_subgroup_eq_base_of_card m hm H hH
  omega

theorem base_characteristic (m : ℕ) (hm : 2 < m) : (baseSubgroup m).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  apply abelian_subgroup_eq_base_of_card m hm
  · let : IsMulCommutative (baseSubgroup m) := base_is_abelian m
    exact Subgroup.map_isMulCommutative (baseSubgroup m) φ.toMonoidHom
  · rw [Subgroup.card_map_of_injective φ.injective, card_base]

end CFSG.Wreathed
