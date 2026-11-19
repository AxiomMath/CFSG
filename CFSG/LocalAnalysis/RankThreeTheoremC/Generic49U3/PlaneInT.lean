module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open

theorem exists_isElemAbelian_card_sq_of_nonabelian {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {T : Subgroup G} (hcard : Nat.card T = p ^ 3) (hexp : ∀ t ∈ T, t ^ p = 1)
    (hnc : ¬ IsMulCommutative T) :
    ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      T ⊓ Subgroup.centralizer (T : Set G) ≤ E := by
  have hp : p.Prime := Fact.out
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup G, Z = T ⊓ Subgroup.centralizer (T : Set G) := ⟨_, rfl⟩
  have hZcard : Nat.card Z = p := by
    rw [hZdef]
    exact card_inf_centralizer_of_nonabelian_card_p_cube hcard hnc
  have hZT : Z ≤ T := by
    rw [hZdef]
    exact inf_le_left
  have hZc : ∀ z ∈ Z, ∀ g ∈ T, g * z = z * g := by
    intro z hz g hg
    rw [hZdef] at hz
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 g hg
  obtain ⟨t, htT, htZ⟩ : ∃ t ∈ T, t ∉ Z := by
    by_contra hcon
    push Not at hcon
    apply hnc
    refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_
    exact (hZc a (hcon a ha) b hb).symm
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = Subgroup.closure (insert t (Z : Set G)) := ⟨_, rfl⟩
  have hZE : Z ≤ E := by
    rw [hEdef]
    intro z hz
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hz)
  have htE : t ∈ E := by
    rw [hEdef]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hET : E ≤ T := by
    rw [hEdef, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact htT
    · exact hZT hx
  have hEcomm : IsMulCommutative E := by
    rw [hEdef]
    apply Subgroup.isMulCommutative_closure
    intro x hx y hy _
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact Commute.refl _
    · exact hZc y hy _ htT
    · exact (hZc x hx _ htT).symm
    · exact hZc y hy x (hZT hx)
  have hexpE : ∀ x ∈ E, x ^ p = 1 := fun x hx => hexp x (hET hx)
  have hdvdT : Nat.card E ∣ p ^ 3 := by
    have h := Subgroup.card_dvd_of_le hET
    rwa [hcard] at h
  have hZdvd : p ∣ Nat.card E := by
    have h := Subgroup.card_dvd_of_le hZE
    rwa [hZcard] at h
  have hEfin : Finite E := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    rw [h0, zero_dvd_iff] at hdvdT
    exact pow_ne_zero 3 hp.ne_zero hdvdT
  have hTfin : Finite T :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨i, hi, hEi⟩ := (Nat.dvd_prime_pow hp).mp hdvdT
  have hcardE : Nat.card E = p ^ 2 := by
    interval_cases i
    · exfalso
      rw [pow_zero] at hEi
      rw [hEi] at hZdvd
      have h1 : p = 1 := Nat.dvd_one.mp hZdvd
      have h2 := hp.one_lt
      omega
    · exfalso
      rw [pow_one] at hEi
      have hZE' : Z = E := Subgroup.eq_of_le_of_card_ge hZE (le_of_eq (by rw [hEi, hZcard]))
      apply htZ
      rw [hZE']
      exact htE
    · exact hEi
    · exfalso
      have hET' : E = T := Subgroup.eq_of_le_of_card_ge hET (le_of_eq (by rw [hEi, hcard]))
      rw [hET'] at hEcomm
      exact hnc hEcomm
  refine ⟨E, hET, ⟨hEcomm, hexpE⟩, hcardE, ?_⟩
  rw [← hZdef]
  exact hZE

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
