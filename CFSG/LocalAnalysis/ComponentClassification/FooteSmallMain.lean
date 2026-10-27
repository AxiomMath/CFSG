module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA7
public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallL27
public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA6
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Inputs

public section

namespace CFSG.ComponentClassification.FooteSmall

open CFSG.GH74.KGroups

theorem prime_pow_eq {p f r j : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hr : r.Prime)
    (h : p ^ f = r ^ j) : p = r ∧ f = j := by
  have hpr : p = r := by
    have hdvd : p ∣ r ^ j := h ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow hdvd)
  subst hpr
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

theorem sylow_comm_of_five {S : Type} [Group S] [Finite S]
    (h : Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 5 1) (P : Sylow 2 S) :
    ∀ x ∈ (P : Subgroup S), ∀ y ∈ (P : Subgroup S), x * y = y * x := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr (by simpa using hK))
  have hS : Nat.card S = 60 := by
    rw [Nat.card_congr (e.trans e').toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  have hP : Nat.card P = 2 ^ 2 := by
    rw [P.card_eq_multiplicity, hS,
      factorization_two_of_eq (k := 2) (r := 15) (by norm_num) (by norm_num)]
  intro x hx y hy
  have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hP).is_comm.comm
    (⟨x, hx⟩ : (P : Subgroup S)) ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem footeSmallCentralizers : FooteLit.FooteSmallCentralizers := by
  intro S _ _ hS hnonab T hT hTP
  rcases hS with he | ⟨p, f, hq, hmodel⟩
  · obtain ⟨e⟩ := he
    obtain ⟨e'⟩ := A7.equiv_of_alt e
    exact A7.iSup_fix_eq_top e' T hT hTP
  · have hp : p.Prime := hmodel.1.1
    have hf : 1 ≤ f := hmodel.1.2.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with h5 | h7 | h9
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq (j := 1) hp hf Nat.prime_five (by rw [h5, pow_one])
      exfalso
      obtain ⟨P, -⟩ := hTP
      obtain ⟨x, hx, y, hy, hxy⟩ := hnonab P
      exact hxy (sylow_comm_of_five hmodel P x hx y hy)
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq (j := 1) hp hf (by norm_num : Nat.Prime 7)
        (by rw [h7, pow_one])
      obtain ⟨e'⟩ := L27.equiv_of_stated hmodel
      exact L27.iSup_fix_eq_top e' T hT hTP
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq (j := 2) hp hf Nat.prime_three (by rw [h9]; norm_num)
      obtain ⟨e'⟩ := A6.equiv_of_stated hmodel
      exact A6.iSup_fix_eq_top e' T hT hTP

end CFSG.ComponentClassification.FooteSmall
