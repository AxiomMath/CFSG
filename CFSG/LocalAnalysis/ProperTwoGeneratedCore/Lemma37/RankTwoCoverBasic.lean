module

public import CFSG.Quasithin.Background.A1cTransferVariants

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open scoped commutatorElement

variable {J : Type*} [Group J]

theorem commutatorElement_mem_of_sq_mem {N : Subgroup J} (h : ∀ x : J, x ^ 2 ∈ N) (a b : J) :
    ⁅a, b⁆ ∈ N := by
  have hab : ⁅a, b⁆ = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]; group
  rw [hab, ← pow_two, ← pow_two, ← pow_two]
  exact N.mul_mem (N.mul_mem (h _) (h _)) (h _)

theorem exists_conj_mem_of_relIndex_eq_two [Finite J] (hperf : commutator J = ⊤) (Q : Sylow 2 J)
    {H : Subgroup J} (hHQ : H ≤ Q) (hH : H.relIndex (Q : Subgroup J) = 2) {y : J}
    (hy : orderOf y = 2) : ∃ g : J, g⁻¹ * y * g ∈ H := by
  by_contra hne
  push Not at hne
  obtain ⟨N, -, hsq, hyN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal Q hHQ hH hy hne
  apply hyN
  have hle : commutator J ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact commutatorElement_mem_of_sq_mem hsq a b
  rw [hperf] at hle
  exact hle (Subgroup.mem_top y)

theorem eq_of_orderOf_eq_two_of_isCyclic [Finite J] {C : Subgroup J} (hC : IsCyclic C) {a b : J}
    (ha : a ∈ C) (hb : b ∈ C) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  classical
  have := Fintype.ofFinite C
  by_contra hab
  have hsq : ∀ c : J, orderOf c = 2 → c ^ 2 = 1 := fun c hc => hc ▸ pow_orderOf_eq_one c
  have hne : ∀ c : J, orderOf c = 2 → c ≠ 1 := fun c hc h => by
    rw [h, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have hsub : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (hsq a ha2)
    · exact Subtype.ext (hsq b hb2)
  have hcard := (Finset.card_le_card hsub).trans (IsCyclic.card_pow_eq_one_le (α := C) two_pos)
  have h1a : (1 : C) ≠ ⟨a, ha⟩ := fun h => hne a ha2 (congrArg Subtype.val h).symm
  have h1b : (1 : C) ≠ ⟨b, hb⟩ := fun h => hne b hb2 (congrArg Subtype.val h).symm
  have hab' : (⟨a, ha⟩ : C) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  rw [Finset.card_insert_of_notMem (by simp [h1a, h1b]),
    Finset.card_insert_of_notMem (by simp [hab']), Finset.card_singleton] at hcard
  omega

theorem exists_orderOf_eq_two_of_isPGroup [Finite J] {Z : Subgroup J} (hZ : IsPGroup 2 Z)
    (hZne : Z ≠ ⊥) : ∃ u ∈ Z, orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZne
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hk
    exact not_subsingleton Z hk.1
  have hdvd : 2 ∣ Nat.card Z := hk ▸ dvd_pow_self 2 hk0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 hdvd
  exact ⟨u, u.2, by rw [← Subgroup.orderOf_coe] at hu; exact hu⟩

theorem mem_center_of_cyclic_index_two [Finite J] (hperf : commutator J = ⊤)
    (hZ : IsPGroup 2 (Subgroup.center J)) (hZne : Subgroup.center J ≠ ⊥) (Q : Sylow 2 J) {x : J}
    (hxQ : x ∈ (Q : Subgroup J)) (hx : (Subgroup.zpowers x).relIndex (Q : Subgroup J) = 2)
    (hZx : Subgroup.center J ≤ Subgroup.zpowers x) {y : J} (hy : orderOf y = 2) :
    y ∈ Subgroup.center J := by
  obtain ⟨u, huZ, hu⟩ := exists_orderOf_eq_two_of_isPGroup hZ hZne
  have hle : Subgroup.zpowers x ≤ Q := (Subgroup.zpowers_le).mpr hxQ
  obtain ⟨g, hg⟩ := exists_conj_mem_of_relIndex_eq_two hperf Q hle hx hy
  have hord : orderOf (g⁻¹ * y * g) = 2 := by
    rw [SemiconjBy.orderOf_eq g (x := g⁻¹ * y * g) (y := y) (by
      simp only [SemiconjBy]; group)]
    exact hy
  have heq := eq_of_orderOf_eq_two_of_isCyclic (Subgroup.isCyclic_zpowers x) hg (hZx huZ) hord hu
  have hy' : y = g * u * g⁻¹ := by rw [← heq]; group
  rw [hy', Subgroup.mem_center_iff.mp huZ g, mul_inv_cancel_right]
  exact huZ

end CFSG.ProperTwoGeneratedCore.Lemma37
