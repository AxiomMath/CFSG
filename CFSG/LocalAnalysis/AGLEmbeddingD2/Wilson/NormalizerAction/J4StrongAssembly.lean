module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4StrongOrbit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4NoPrimeCommute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.SylowUniqConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.SylowCountOne

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open scoped commutatorElement Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

theorem card_centralizer_conj_le {G : Type*} [Group G] [Finite G] (n g : G) :
    Nat.card (Subgroup.centralizer ({n * g * n⁻¹} : Set G)) ≤
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  refine Nat.card_le_card_of_injective
    (fun c => (⟨n⁻¹ * c * n, ?_⟩ : Subgroup.centralizer ({g} : Set G))) ?_
  · have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc n⁻¹ * c * n * g = n⁻¹ * (c * (n * g * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * g * n⁻¹) * c) * n := by rw [h]
      _ = g * (n⁻¹ * c * n) := by group
  · intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this

theorem comm_of_mem_centralizer_singleton {G : Type*} [Group G] (g : G)
    (x : Subgroup.centralizer ({g} : Set G)) : (x : G) * g = g * x :=
  Subgroup.mem_centralizer_singleton_iff.1 x.2

theorem prime_dvd_card_J_cases {r : ℕ} (hr : r.Prime)
    (h : r ∣ 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 23 ∨ r = 29 ∨ r = 31 ∨ r = 37 ∨ r = 43 := by
  have key : ∀ q : ℕ, q.Prime → r ∣ q → r = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hr hq).1 h
  simp only [hr.dvd_mul] at h
  rcases h with ((((((((h2 | h3) | h5) | h7) | h11) | h23) | h29) | h31) | h37) | h43
  · exact Or.inl (key 2 (by norm_num) (hr.dvd_of_dvd_pow h2))
  · exact Or.inr (Or.inl (key 3 (by norm_num) (hr.dvd_of_dvd_pow h3)))
  · exact Or.inr (Or.inr (Or.inl (key 5 (by norm_num) h5)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key 7 (by norm_num) h7))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 11 (by norm_num) (hr.dvd_of_dvd_pow h11))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 23 (by norm_num) h23))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 29 (by norm_num) h29)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key 31 (by norm_num) h31))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key 37 (by norm_num) h37)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (key 43 (by norm_num) h43)))))))))


theorem fixDim_of_mem_zpowers_qz {x : J} (hx : x ∈ Subgroup.zpowers qz) (hx1 : x ≠ 1) :
    fixDim x = 2 := by
  have hz := @zpowers_eq_of_mem_of_ne_one J (Subgroup.toGroup J) _ _ _ orderOf_qz hx hx1
  have hq : qz ∈ Subgroup.zpowers x := by rw [hz]; exact Subgroup.mem_zpowers qz
  rw [fixDim_eq_of_mem_zpowers hx hq]
  exact finrank_rowFix_qz

theorem Q11_commutator_mem_zpowers : ∀ a ∈ Q11, ∀ b ∈ Q11, ⁅a, b⁆ ∈ Subgroup.zpowers qz := by
  intro a ha b hb
  rw [← inf_centralizer_Q11, ← commutator_Q11_eq]
  exact Subgroup.commutator_mem_commutator ha hb

theorem Q11_mem_zpowers_of_central :
    ∀ q ∈ Q11, (∀ a ∈ Q11, q * a = a * q) → q ∈ Subgroup.zpowers qz := by
  intro q hq h
  rw [← inf_centralizer_Q11]
  refine ⟨hq, ?_⟩
  change q ∈ Subgroup.centralizer (Q11 : Set J)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (h a ha).symm


theorem fixDim_of_mem_Q11 (hC : Nat.card (Subgroup.centralizer ({qx} : Set J)) ≤ 242) {u : J}
    (hu : u ∈ Q11) (hnu : u ∉ Subgroup.zpowers qz) : fixDim u = 12 := by
  obtain ⟨n, hn, rfl⟩ := exists_conj_of_mem_Q11 hC u hu hnu
  rw [fixDim_conj]
  exact finrank_rowFix_qx

theorem not_dvd_card_J : ¬ 11 ^ 4 ∣ Nat.card J := by
  rw [card_J_eq]; norm_num

theorem eq_Q11_of_mem (hC : Nat.card (Subgroup.centralizer ({qx} : Set J)) ≤ 242)
    (Q' : Subgroup J) (hQ' : Nat.card Q' = 11 ^ 3) {u : J} (huQ : u ∈ Q11)
    (hnu : u ∉ Subgroup.zpowers qz) (huQ' : u ∈ Q') : Q' = Q11 := by
  obtain ⟨g, hg⟩ := exists_conj_of_card_pow Q11 Q' card_Q11 hQ' not_dvd_card_J
  have hcQ := Q11_commutator_mem_zpowers
  have hZQ := Q11_mem_zpowers_of_central
  obtain ⟨n, hn, hun⟩ := exists_conj_of_mem_Q11 hC u huQ hnu
  refine @eq_of_conj_mem_of_class_data J (Subgroup.toGroup J) _ fixDim fixDim_conj Q11 Q' g qz u card_Q11 hQ' orderOf_qz
    qz_mem hcQ hZQ (fun q hq => qz_commute_of_mem hq) hg
    (fun x hx hx1 => fixDim_of_mem_zpowers_qz hx hx1)
    (fun x hx hnx => fixDim_of_mem_Q11 hC hx hnx) huQ hnu huQ' ?_
  rw [hun]
  exact (card_centralizer_conj_le n qx).trans hC


theorem prime_dvd_card_centralizer_qz {r : ℕ} (hr : r.Prime)
    (h : r ∣ Nat.card (Subgroup.centralizer ({qz} : Set J))) : r = 2 ∨ r = 3 ∨ r = 11 := by
  have h1 : r ∣ 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 := by
    rw [← card_J_eq]
    exact h.trans (Subgroup.card_subgroup_dvd_card _)
  have hcases := prime_dvd_card_J_cases hr h1
  by_contra hne
  have hmem : r ∈ ({5, 7, 23, 29, 31, 37, 43} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have := Fact.mk hr
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({qz} : Set J)) r h
  have hxJ : orderOf (x : J) = r := by rw [Subgroup.orderOf_coe]; exact hx
  have hc : (x : J) * qz = qz * (x : J) := @comm_of_mem_centralizer_singleton J (Subgroup.toGroup J) qz x
  have h2 := not_commute_qz_of_prime hmem hxJ
  exact h2 hc

theorem centralizer_qz_le_normalizer (hC : Nat.card (Subgroup.centralizer ({qx} : Set J)) ≤ 242) :
    Subgroup.centralizer ({qz} : Set J) ≤ Subgroup.normalizer (Q11 : Set J) := by
  refine centralizer_le_normalizer_of_count Q11 qz orderOf_qz card_Q11 qz_mem
    (fun q hq => qz_commute_of_mem hq) ?_ card_normalizer_inf_centralizer_qz
    (fun r hr h => prime_dvd_card_centralizer_qz hr h) card_J_eq
  intro Q' hQ' _ hne g hg hgQ'
  by_contra hgz
  exact hne (eq_Q11_of_mem hC Q' hQ' hg hgz hgQ')

theorem normalizer_zpowers_qz_eq (hC : Nat.card (Subgroup.centralizer ({qx} : Set J)) ≤ 242) :
    Subgroup.normalizer ((Subgroup.zpowers qz : Subgroup J) : Set J) =
      Subgroup.normalizer (Q11 : Set J) := by
  refine le_antisymm (@normalizer_zpowers_le_normalizer J (Subgroup.toGroup J) _ Q11 qz card_Q11
    (fun q hq => qz_commute_of_mem hq) (centralizer_qz_le_normalizer hC) not_dvd_card_J) ?_
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact (conj_mem_zpowers_iff hn).symm

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
