module

public import CFSG.GF2Type.Smith1980Orth.Order
public import CFSG.LargeExtraspecial.S14C12SmQ
public import CFSG.LargeExtraspecial.FS77PSU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.factorization_card_cases (O : OrthData S) :
    (Nat.card G).factorization 2 = (S.width / 2 + 1) * (S.width / 2 + 2) ∨
      (Nat.card G).factorization 2 = (S.width / 2 + 1) * (S.width / 2 + 2) + 1 := by
  rcases O.iso with h | h
  · exact Or.inl (O.factorization_card.1 h)
  · exact Or.inr (O.factorization_card.2 h)

theorem OrthData.factorization_ne_of_wide (O : OrthData S) (hw : 5 ≤ S.width) {N : ℕ}
    (hN : N = (S.width + 2) * (S.width + 2 - 1) / 2) :
    (Nat.card G).factorization 2 ≠ N := by
  obtain ⟨m, hm⟩ : ∃ m, S.width = 2 * m := ⟨S.width / 2, O.width_eq_two_mul⟩
  have hm2 : S.width / 2 = m := by omega
  have hm3 : 3 ≤ m := by omega
  have hN' : N = (m + 1) * (2 * m + 1) := by
    rw [hN, hm, show 2 * m + 2 - 1 = 2 * m + 1 by omega,
      show (2 * m + 2) * (2 * m + 1) = 2 * ((m + 1) * (2 * m + 1)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  intro h
  rcases O.factorization_card_cases with h' | h' <;> rw [h', hm2, hN'] at h <;> nlinarith

theorem exists_isConj_orderOf_mul_eq_four [IsSimpleGroup G] (hAS : S14.AschbacherSmithWideInput)
    (hDW : DW.DW37Statement) (O : OrthData S) (hw : 5 ≤ S.width) :
    ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4 := by
  by_cases hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  · exfalso
    obtain ⟨e⟩ := hAS G S hw hW
    have h := FS77.factorization_card_timmesfeldPSU (m := S.width + 2) (by omega)
    rw [← Nat.card_congr e.toEquiv] at h
    exact O.factorization_ne_of_wide hw rfl h
  · push Not at hW
    obtain ⟨g, hgQ, hne⟩ := hW
    by_contra hno
    have hcomm : ∀ x y : G, IsConj S.z x → x ∈ S.QG → IsConj S.z y → y ∈ S.QG →
        x * y = y * x := by
      intro x y hx hxQ hy hyQ
      by_contra hxy
      exact hno ⟨x, y, hx, hy, S14.SmithQ.orderOf_mul_eq_four S hxQ hyQ
        (S14.SmithQ.mul_self_eq_one_of_isConj S hx) (S14.SmithQ.mul_self_eq_one_of_isConj S hy) hxy⟩
    obtain ⟨e⟩ := hDW G S g hw hgQ hne
      (S14.SmithQ.isReducible_of_commute S (by omega) (isConj_iff.mpr ⟨g, rfl⟩) hgQ hne hcomm)
    have h := S14.SmithQ.factorization_card_psl (S.width + 2)
    rw [← Nat.card_congr e.toEquiv] at h
    exact O.factorization_ne_of_wide hw rfl h

end CFSG.GF2Type.Smith1980Orth
