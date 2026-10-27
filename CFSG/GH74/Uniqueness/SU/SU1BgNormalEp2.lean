module

public import CFSG.GH74.Uniqueness.SU.SU1BgTwoMaxClass
public import CFSG.GH74.Uniqueness.SU.SU1NormalFour
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

theorem dihedral_or_semidihedral_of_no_normal_four {P : Type} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {Q : Subgroup P} [hQ : Q.Normal]
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False)
    (hrank : ∃ E : Subgroup P, E ≤ Q ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 2) :
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥Q ≃* DihedralGroup (2 ^ m))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥Q ≃* CFSG.Open.SemidihedralGroup n) := by
  obtain ⟨E₀, hE₀Q, hE₀, hE₀c⟩ := hrank
  obtain ⟨k, a, hk, hord, haQ, y, hyQ, hyA, hy2, hcos, hconj⟩ :=
    two_shape_of_rank hP hstar ⟨E₀, hE₀Q, hE₀, hE₀c⟩
  obtain ⟨a', ha'⟩ : ∃ a' : Q, (a' : P) = a := ⟨⟨a, haQ⟩, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Q, (y' : P) = y := ⟨⟨y, hyQ⟩, rfl⟩
  have hcosQ : ∀ g : Q, g ∈ zpowers a' ∨ y'⁻¹ * g ∈ zpowers a' := by
    intro g
    rcases hcos g g.2 with h | h
    · exact Or.inl (mem_zpowers_subtype.mpr (by rw [ha']; exact h))
    · refine Or.inr (mem_zpowers_subtype.mpr ?_)
      rw [ha']
      simpa [hy'] using h
  have hy2Q : y' * y' ∈ zpowers a' :=
    mem_zpowers_subtype.mpr (by rw [ha']; simpa [hy'] using hy2)
  have hyQ' : y' ∉ zpowers a' := by
    intro h
    apply hyA
    have h1 := mem_zpowers_subtype.mp h
    rw [ha', hy'] at h1
    exact h1
  have hordQ : orderOf a' = 2 ^ k := by
    rw [← Subgroup.orderOf_coe, ha']
    exact hord
  have hconjQ : y' * a' * y'⁻¹ = a'⁻¹ ∨
      (3 ≤ k ∧ y' * a' * y'⁻¹ = a' ^ (2 ^ (k - 1) - 1)) := by
    rcases hconj with h | ⟨hk3, h⟩
    · left
      apply Subtype.ext
      simpa [ha', hy'] using h
    · right
      refine ⟨hk3, ?_⟩
      apply Subtype.ext
      simpa [ha', hy'] using h
  have hidx : (zpowers a').index = 2 := index_eq_two_of_cosets hy2Q hyQ' hcosQ
  have hcardQ : Nat.card Q = 2 ^ (k + 1) := by
    have h1 := Subgroup.card_mul_index (zpowers a')
    rw [hidx, Nat.card_zpowers, hordQ] at h1
    rw [← h1, pow_succ]
  have hE₀2 : ∀ x ∈ E₀.subgroupOf Q, x * x = 1 := by
    intro x hx
    apply Subtype.ext
    have := (isElemAbelian_iff.mp hE₀).2 x.1 (Subgroup.mem_subgroupOf.mp hx)
    simpa [pow_two] using this
  have hE₀card : Nat.card (E₀.subgroupOf Q) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀Q).toEquiv, hE₀c]
    norm_num
  rcases shape_of_index_two hk hordQ hy2Q hyQ' hcosQ hconjQ hE₀2 hE₀card with
    ⟨a₁, y₁, ha₁, hy₁, hgen, hy₁2, hconj₁⟩ | ⟨hk3, a₁, y₁, ha₁, hy₁, hgen, hy₁2, hconj₁⟩
  · left
    refine ⟨k, by omega, ?_⟩
    have hgen' : ⊤ = zpowers a₁ ⊔ zpowers y₁ := by
      rw [← hgen, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        ← Subgroup.closure_union]
      rfl
    have := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem a₁ y₁ hgen'
      (by rw [pow_two]; exact hy₁2) hconj₁ hy₁
    rwa [ha₁] at this
  · right
    refine ⟨k + 1, by omega, ?_⟩
    exact nonempty_mulEquiv_semidihedral (n := k + 1) (by omega) hcardQ
      (by rw [show k + 1 - 1 = k by omega, ← ha₁]; exact pow_orderOf_eq_one a₁) hy₁2
      (by rw [show k + 1 - 2 = k - 1 by omega]; exact hconj₁) hgen

theorem b_normal_Ep2 : CFSG.GH74.GLS.Bg.B_normal_Ep2 := by
  intro p hp P _ _ hP Q hQ h2
  have : Q.Normal := hQ
  by_cases hex : ∃ E : Subgroup P, E.Normal ∧ E ≤ Q ∧ CFSG.IsElementaryAbelian p E ∧
      Nat.card E = p ^ 2
  · exact Or.inl hex
  · right
    have hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian p E →
        Nat.card E = p ^ 2 → False := fun E hE hEQ hel hc =>
      hex ⟨E, hE, hEQ, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mpr hel, hc⟩
    have hrank : ∃ E : Subgroup P, E ≤ Q ∧ Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp] at h2
      exact exists_isElemAbelian_of_le_pRank hp h2
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact ⟨rfl, dihedral_or_semidihedral_of_no_normal_four hP hstar hrank⟩
    · exfalso
      obtain ⟨a, k, hset, hord, hk1, hne⟩ := exists_setting hp hP hstar hrank
      exact false_of_odd hp hodd hP hset hord hk1 hne hstar

end CFSG.GH74.Uniqueness.SU.SU1
