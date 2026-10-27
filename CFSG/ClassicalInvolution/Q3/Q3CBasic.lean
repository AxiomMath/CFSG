module

public import CFSG.ClassicalInvolution.Q3.Q3TAxis

public section

namespace CFSG.ClassicalInvolution.Q3.Q3C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance

section Elementary

variable {G : Type} [Group G]

theorem mem_closure_pair_commuting {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have h_aab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h_bab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have h_aba : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have h_abb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have h_abab : a * b * (a * b) = 1 := by rw [← mul_assoc, h_aba, hb]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hy
      exact Or.inr (Or.inr (Or.inl hy))
  | one => exact Or.inl rfl
  | mul y z _ _ hy hz =>
    rcases hy with h1 | h1 | h1 | h1 <;> rcases hz with h2 | h2 | h2 | h2 <;> rw [h1, h2]
    · simp
    · simp
    · simp
    · simp
    · simp
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl h_aab))
    · simp
    · exact Or.inr (Or.inr (Or.inr hba))
    · exact Or.inl hb
    · exact Or.inr (Or.inl h_bab)
    · simp
    · exact Or.inr (Or.inr (Or.inl h_aba))
    · exact Or.inr (Or.inl h_abb)
    · exact Or.inl h_abab
  | inv y _ hy =>
    rcases hy with h1 | h1 | h1 | h1 <;> rw [h1]
    · simp
    · exact Or.inr (Or.inl hai)
    · exact Or.inr (Or.inr (Or.inl hbi))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, hai, hbi, hba]

end Elementary

section BootData

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_of_le_centralizer_isElemAbelian (hB : ¬ BootData3 Ω) {L : Subgroup G} {z : G}
    (hLΩ : L ∈ Ω) (hz : IsClassicalMember3 L z) {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (h4 : 4 ≤ Nat.card E) (hLE : L ≤ Subgroup.centralizer (E : Set G)) : z ∈ E := by
  by_contra hzE
  obtain ⟨E₀, hE₀E, hE₀c⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two E hE (by simpa using h4)
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have hzC : ∀ e ∈ E, e * z = z * e := fun e he =>
    Subgroup.mem_centralizer_iff.mp (hLE hz.mem) e he
  have hzE₀ : z ∉ E₀ := fun h => hzE (hE₀E h)
  have hE₀2 : ∀ e ∈ E₀, e * e = 1 := fun e he => by
    rw [← pow_two]
    exact hE.2 e (hE₀E he)
  have hE₀c' : ∀ e ∈ E₀, ∀ e' ∈ E₀, e * e' = e' * e := fun e he e' he' =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨e, hE₀E he⟩ : E) ⟨e', hE₀E he'⟩)
  set A : Subgroup G := Subgroup.closure (insert z (E₀ : Set G)) with hA
  have hAel : IsElemAbelian 2 A := by
    refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
    · intro s hs
      rcases hs with rfl | hs
      · exact hz2
      · exact hE₀2 s hs
    · intro s hs t ht
      rcases hs with rfl | hs <;> rcases ht with rfl | ht
      · rfl
      · exact (hzC t (hE₀E ht)).symm
      · exact hzC s (hE₀E hs)
      · exact hE₀c' s hs t ht
  have hzA : z ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have hE₀A : E₀ ≤ A := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have hcardle : Nat.card A ≤ 8 := by
    have h := Theorem5.card_closure_insert_le (S := (E₀ : Set G)) (c := z) hz2
      (fun s hs => (hzC s (hE₀E hs)).symm)
    rw [Subgroup.closure_eq, hE₀c] at h
    simpa using h
  have hcard : Nat.card A = 8 := by
    have hdvd : 4 ∣ Nat.card A := by
      have := Subgroup.card_dvd_of_le hE₀A
      rw [hE₀c] at this
      simpa using this
    have hpos : 0 < Nat.card A := Nat.card_pos
    by_contra h8
    have h4' : Nat.card A = 4 := by omega
    have hEq := Subgroup.eq_of_le_of_card_ge hE₀A (by omega)
    exact hzE₀ (hEq ▸ hzA)
  have hLz : L ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hz.subnormal
  have hLA : L ≤ Subgroup.centralizer (A : Set G) := by
    rw [hA, Subgroup.centralizer_closure]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | hy
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLz hk)).symm
    · exact Subgroup.mem_centralizer_iff.mp (hLE hk) y (hE₀E hy)
  exact hB ⟨L, z, A, hLΩ, hz, hAel, hcard, hzA, hLA⟩

theorem mem_pair_of_le_centralizer (hB : ¬ BootData3 Ω) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (he : IsEdge3 Ω K₁ K₂ z₁ z₂) {L : Subgroup G} {z : G} (hLΩ : L ∈ Ω)
    (hz : IsClassicalMember3 L z)
    (hL : L ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G)) :
    z ∈ Subgroup.closure ({z₁, z₂} : Set G) :=
  mem_of_le_centralizer_isElemAbelian hB hLΩ hz he.isElemAbelian_pair (he.card_pair.ge.trans' (by
    norm_num)) hL

theorem eq_mul_of_third (hB : ¬ BootData3 Ω) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (he : IsEdge3 Ω K₁ K₂ z₁ z₂) {K₃ : Subgroup G} {z₃ : G} (hK₃ : K₃ ∈ Ω)
    (hz₃ : IsClassicalMember3 K₃ z₃) (h13 : Commutes K₁ K₃) (h23 : Commutes K₂ K₃)
    (h1 : z₃ ≠ z₁) (h2 : z₃ ≠ z₂) : z₃ = z₁ * z₂ := by
  have hL : K₃ ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
    rw [Subgroup.centralizer_closure]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | hy
    · exact h13 _ he.cls₁.mem k hk
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h23 _ he.cls₂.mem k hk
  have hmem := mem_pair_of_le_centralizer hB he hK₃ hz₃ hL
  rcases mem_closure_pair_commuting he.cls₁.isCentralInvolution.sq
      he.cls₂.isCentralInvolution.sq he.comm_involutions hmem with h | h | h | h
  · exact absurd h hz₃.ne_one
  · exact absurd h h1
  · exact absurd h h2
  · exact h

theorem isTriangle3_of_third (hB : ¬ BootData3 Ω) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (he : IsEdge3 Ω K₁ K₂ z₁ z₂) {K₃ : Subgroup G} {z₃ : G} (hK₃ : K₃ ∈ Ω)
    (hz₃ : IsClassicalMember3 K₃ z₃) (h13 : Commutes K₁ K₃) (h23 : Commutes K₂ K₃)
    (h1 : z₃ ≠ z₁) (h2 : z₃ ≠ z₂) : IsTriangle3 Ω K₁ K₂ K₃ z₁ z₂ := by
  have h := eq_mul_of_third hB he hK₃ hz₃ h13 h23 h1 h2
  subst h
  exact ⟨he, hK₃, hz₃, h13, h23⟩

end BootData

end CFSG.ClassicalInvolution.Q3.Q3C
