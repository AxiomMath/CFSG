module

public import CFSG.GH74.OrderForm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.Statement
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.CaseA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.CaseB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.Survivors

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

private theorem isElemAbelian_of_sq {X : Type} [Group X] {E : Subgroup X}
    (hE : ∀ x ∈ E, x ^ 2 = 1) : CFSG.Open.IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE x hx⟩
  apply Subtype.ext
  have ha : (a : X) * a = 1 := by rw [← pow_two]; exact hE a a.2
  have hb : (b : X) * b = 1 := by rw [← pow_two]; exact hE b b.2
  have hab : ((a : X) * b) * (a * b) = 1 := by
    rw [← pow_two]; exact hE (a * b) (mul_mem a.2 b.2)
  have h1 : ((a : X) * b)⁻¹ = (a : X) * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at h1
  exact h1.symm

theorem three_le_twoRank_of_e16 {X : Type} [Group X] [Finite X]
    (h : ∃ E : Subgroup X, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    3 ≤ CFSG.Open.twoRank X := by
  obtain ⟨E, hEcard, hEsq⟩ := h
  have h4 : 4 ≤ CFSG.Open.twoRank X := by
    unfold CFSG.Open.twoRank CFSG.Open.pRank
    refine le_csSup ⟨Nat.card X, ?_⟩ ⟨E, le_top, isElemAbelian_of_sq hEsq, ?_⟩
    · rintro k ⟨F, -, -, hF⟩
      have h1 : 2 ^ k ≤ Nat.card X := by
        rw [← hF]
        exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card F)
      exact (Nat.lt_two_pow_self (n := k)).le.trans h1
    · rw [hEcard]; norm_num
  exact le_trans (by norm_num) h4

theorem gh73TheoremA64K_of_models
    (hM : CFSG.GH74.ModelsFormStatement)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog) :
    GH73TheoremA64K := by
  intro X _ _ hK hperf hO hZ hA8
  obtain ⟨S, hS8⟩ := hA8
  let D : A8SylowData X := A8SylowData.of_sylow S hS8
  haveI : Group.IsPerfect X := ⟨hperf⟩
  by_cases hE : CFSG.layer X = ⊥
  · rcases caseA hO hE D with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · haveI : IsSimpleGroup X := caseB hK hS hZ D hE
    have hnonab : ∃ a b : X, a * b ≠ b * a :=
      let ⟨a, _, b, _, _, _, hab⟩ := D.exists_noncomm S
      ⟨a, b, hab⟩
    have h3 : 3 ≤ CFSG.Open.twoRank X := three_le_twoRank_of_e16 D.exists_e16
    have hX' : CFSG.GH74.GH74Conclusion X := hM X hnonab h3 D.gen_four
    rcases survivors D hX' with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSG.EvenSporadicStandard.HNRecog.GH73
