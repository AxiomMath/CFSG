module

public import CFSG.CharacterTheory.PSL2Table.Classes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.GroupLemmas

public section

namespace CFSG.QuasithinUnique.I43Dihedral

open scoped MatrixGroups

theorem psl2_involution_centralizer {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (hq : 5 ≤ Nat.card F) {g : PSL(2, F)} (hg : orderOf g = 2) :
    ∃ A : Subgroup PSL(2, F), A ≤ Subgroup.centralizer {g} ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      Nat.card (Subgroup.centralizer {g} : Subgroup PSL(2, F)) = 2 * Nat.card A ∧
      ((Nat.card F % 4 = 1 ∧ 2 * Nat.card A + 1 = Nat.card F) ∨
        (Nat.card F % 4 = 3 ∧ 2 * Nat.card A = Nat.card F + 1)) := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  have hq' : 5 ≤ Fintype.card F := by rw [hcard]; exact hq
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    omega
  have hg2 : g ^ 2 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg] at this
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have hsq : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := FiniteField.isSquare_neg_one_iff
  have hmod : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by
    omega
  have transport : ∀ (c x : PSL(2, F)) (T : Subgroup PSL(2, F)), c * g * c⁻¹ = x →
      (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → x ∈ T → x ≠ 1 → x ^ 2 = 1 →
      Nat.card (Subgroup.centralizer {x} : Subgroup PSL(2, F)) = 2 * Nat.card T →
      ∃ A : Subgroup PSL(2, F), A ≤ Subgroup.centralizer {g} ∧
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ Nat.card A = Nat.card T ∧
        Nat.card (Subgroup.centralizer {g} : Subgroup PSL(2, F)) = 2 * Nat.card A := by
    intro c x T hc hcomm hxT _ _ hcent
    have hxg : (MulAut.conj c) g = x := by rw [MulAut.conj_apply]; exact hc
    refine exists_comm_subgroup_of_mulEquiv (MulAut.conj c) g (T := T) ?_ hcomm ?_
    · rw [hxg]
      exact fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm t ht x hxT)
    · rw [hxg]
      exact hcent
  have hconj : ∀ (c x : PSL(2, F)), c * g * c⁻¹ = x → x ≠ 1 ∧ x ^ 2 = 1 := by
    intro c x hc
    have hxg : (MulAut.conj c) g = x := by rw [MulAut.conj_apply]; exact hc
    refine ⟨fun h => hg1 ((MulAut.conj c).injective ?_), ?_⟩
    · rw [hxg, h, map_one]
    · rw [← hxg, ← map_pow, hg2, map_one]
  rcases hmod with h4 | h4
  ·
    obtain ⟨x, hx, hgx⟩ :=
      (CFSG.PSL2Table.involution_conj_torus hF hq' hν hg).1 (hsq.mpr (by omega))
    obtain ⟨c, hc⟩ := isConj_iff.mp hgx
    obtain ⟨hx1, hx2⟩ := hconj c x hc
    have hcent := CFSG.PSL2Table.card_centralizer_splitTorus hF hq' hx hx1
    simp only [hx2, ↓reduceIte] at hcent
    obtain ⟨A, hAC, hAcomm, hAcard, hAcent⟩ := transport c x (CFSG.PSL2Table.splitTorus F) hc
      (fun a ha b hb => CFSG.PSL2Table.splitTorus_mul_comm ha hb) hx hx1 hx2 hcent
    have hT := CFSG.PSL2Table.card_splitTorus (F := F) h2
    refine ⟨A, hAC, hAcomm, hAcent, Or.inl ⟨by rw [← hcard]; exact h4, ?_⟩⟩
    omega
  ·
    obtain ⟨x, hx, hgx⟩ := (CFSG.PSL2Table.involution_conj_torus hF hq' hν hg).2
      (fun hs => by have := hsq.mp hs; omega)
    obtain ⟨c, hc⟩ := isConj_iff.mp hgx
    obtain ⟨hx1, hx2⟩ := hconj c x hc
    have hcent := CFSG.PSL2Table.card_centralizer_nonsplitTorus hF hq' hν hx hx1
    simp only [hx2, ↓reduceIte] at hcent
    obtain ⟨A, hAC, hAcomm, hAcard, hAcent⟩ := transport c x (CFSG.PSL2Table.nonsplitTorus ν) hc
      (fun a ha b hb => CFSG.PSL2Table.nonsplitTorus_mul_comm ha hb) hx hx1 hx2 hcent
    have hT := CFSG.PSL2Table.card_nonsplitTorus (F := F) hF hν
    refine ⟨A, hAC, hAcomm, hAcent, Or.inr ⟨by rw [← hcard]; exact h4, ?_⟩⟩
    omega

end CFSG.QuasithinUnique.I43Dihedral
