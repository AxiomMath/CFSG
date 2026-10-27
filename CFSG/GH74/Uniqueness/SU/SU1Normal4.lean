module

public import CFSG.GH74.Uniqueness.SU.SU1MaxClassShape

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_le_two_of_le_zpowers {a : G} {S : Subgroup G} (hS : S ≤ zpowers a)
    (h2 : ∀ x ∈ S, x * x = 1) : Nat.card S ≤ 2 := by
  set S' : Subgroup (zpowers a) := S.subgroupOf (zpowers a) with hS'
  have hcard : Nat.card S = Nat.card S' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv).symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S')
  have hog : orderOf g = Nat.card S' := orderOf_eq_card_of_forall_mem_zpowers hg
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact h2 _ (Subgroup.mem_subgroupOf.mp g.2)
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  rw [hcard, ← hog]
  exact Nat.le_of_dvd two_pos hdvd

omit [Finite G] in
theorem pow_eq_one_or_of_dvd' {k : ℕ} (hk : 1 ≤ k) {a : G} (ha : orderOf a = 2 ^ k) {j : ℕ}
    (hj : 2 ^ (k - 1) ∣ j) : a ^ j = 1 ∨ a ^ j = a ^ (2 ^ (k - 1)) := by
  obtain ⟨s, rfl⟩ := hj
  have ha1 : a ^ (2 ^ k) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb : (a ^ (2 ^ (k - 1))) ^ 2 = 1 := by
    rw [← pow_mul]
    have : 2 ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [this, ha1]
  rcases Nat.even_or_odd' s with ⟨t, rfl | rfl⟩
  · left
    rw [pow_mul, pow_mul, hb, one_pow]
  · right
    rw [pow_mul, pow_succ, pow_mul, hb, one_pow, one_mul]

theorem sq_cases_inv' {k : ℕ} (hk : 2 ≤ k) {a y : G} (ha : orderOf a = 2 ^ k)
    (hM : (zpowers a).index = 2) (hy : y * a * y⁻¹ = a⁻¹) :
    y * y = 1 ∨ y * y = a ^ (2 ^ (k - 1)) := by
  obtain ⟨j, hj⟩ := exists_sq_pow y hM
  have h1 : y * a ^ j * y⁻¹ = a ^ j := by
    rw [← hj]
    group
  rw [← conj_pow, hy, inv_pow] at h1
  have h2 : a ^ (j + j) = 1 := by
    rw [pow_add]
    calc a ^ j * a ^ j = (a ^ j)⁻¹ * a ^ j := by rw [h1]
      _ = 1 := inv_mul_cancel _
  have h3 : 2 ^ k ∣ j + j := by
    rw [← ha]
    exact orderOf_dvd_of_pow_eq_one h2
  have h4 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h5 : 2 ^ (k - 1) ∣ j := by
    rw [h4, show j + j = 2 * j by ring] at h3
    exact Nat.dvd_of_mul_dvd_mul_left two_pos h3
  rw [hj]
  exact pow_eq_one_or_of_dvd' (by omega) ha h5

omit [Finite G] in
theorem index_eq_two_of_cosets {a y : G} (hy2 : y * y ∈ zpowers a) (hy : y ∉ zpowers a)
    (hcos : ∀ g : G, g ∈ zpowers a ∨ y⁻¹ * g ∈ zpowers a) : (zpowers a).index = 2 := by
  rw [Subgroup.index_eq_two_iff']
  refine ⟨y, fun c => ?_⟩
  by_cases hc : c ∈ zpowers a
  · have h1 : ¬ y * c ∈ zpowers a := by
      intro hmem
      apply hy
      have := (zpowers a).mul_mem hmem ((zpowers a).inv_mem hc)
      simpa using this
    exact Or.inr ⟨hc, h1⟩
  · have h2 : y * c ∈ zpowers a := by
      have := (zpowers a).mul_mem hy2 (hcos c |>.resolve_left hc)
      simpa [mul_assoc] using this
    exact Or.inl ⟨h2, hc⟩

theorem shape_of_index_two {k : ℕ} (hk : 2 ≤ k) {a y : G} (ha : orderOf a = 2 ^ k)
    (hy2 : y * y ∈ zpowers a) (hy : y ∉ zpowers a)
    (hcos : ∀ g : G, g ∈ zpowers a ∨ y⁻¹ * g ∈ zpowers a)
    (hconj : y * a * y⁻¹ = a⁻¹ ∨ (3 ≤ k ∧ y * a * y⁻¹ = a ^ (2 ^ (k - 1) - 1)))
    {E₀ : Subgroup G} (hE₀ : ∀ x ∈ E₀, x * x = 1) (hE₀c : Nat.card E₀ = 4) :
    (∃ a₁ y₁ : G, orderOf a₁ = 2 ^ k ∧ y₁ ∉ zpowers a₁ ∧
        Subgroup.closure ({a₁, y₁} : Set G) = ⊤ ∧ y₁ * y₁ = 1 ∧ y₁ * a₁ * y₁⁻¹ = a₁⁻¹) ∨
    (3 ≤ k ∧ ∃ a₁ y₁ : G, orderOf a₁ = 2 ^ k ∧ y₁ ∉ zpowers a₁ ∧
        Subgroup.closure ({a₁, y₁} : Set G) = ⊤ ∧ y₁ * y₁ = 1 ∧
        y₁ * a₁ * y₁⁻¹ = a₁ ^ (2 ^ (k - 1) - 1)) := by
  have hidx : (zpowers a).index = 2 := index_eq_two_of_cosets hy2 hy hcos
  have hcl : Subgroup.closure ({a, y} : Set G) = ⊤ := closure_pair_eq_top hidx hy
  have hz1 : a ^ (2 ^ (k - 1)) ≠ 1 := by
    intro h1
    have : orderOf a ∣ 2 ^ (k - 1) := orderOf_dvd_of_pow_eq_one h1
    rw [ha] at this
    have h2 := Nat.le_of_dvd (pow_pos two_pos _) this
    have h3 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  rcases hconj with hinv | ⟨hk3, hsd⟩
  · rcases sq_cases_inv' hk ha hidx hinv with h1 | h1
    · exact Or.inl ⟨a, y, ha, hy, hcl, h1, hinv⟩
    · exfalso
      have hnle : ¬ E₀ ≤ zpowers a := by
        intro hle
        have := card_le_two_of_le_zpowers hle hE₀
        omega
      obtain ⟨x, hxE, hxA⟩ : ∃ x ∈ E₀, x ∉ zpowers a := by
        by_contra hcon
        exact hnle (fun x hx => by_contra (fun hx' => hcon ⟨x, hx, hx'⟩))
      obtain ⟨c, hc, hxc⟩ : ∃ c ∈ zpowers a, x = y * c :=
        ⟨y⁻¹ * x, (hcos x).resolve_left hxA, by group⟩
      have hcinv : y * c * y⁻¹ = c⁻¹ := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
        rw [← conj_zpow, hinv, inv_zpow]
      have hxx : x * x = a ^ (2 ^ (k - 1)) := by
        calc x * x = (y * c * y⁻¹) * (y * y) * c := by rw [hxc]; group
          _ = c⁻¹ * a ^ (2 ^ (k - 1)) * c := by rw [hcinv, h1]
          _ = a ^ (2 ^ (k - 1)) := by
              obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
              have : Commute (a ^ m) (a ^ (2 ^ (k - 1))) := (Commute.refl a).zpow_left m |>.pow_right _
              rw [mul_assoc, ← this.eq]
              group
      exact hz1 (hxx ▸ hE₀ x hxE)
  · have hn4 : 4 ≤ k + 1 := by omega
    have ha' : orderOf a = 2 ^ (k + 1 - 1) := by simpa using ha
    have hsd' : y * a * y⁻¹ = a ^ (2 ^ (k + 1 - 2) - 1) := by
      have : k + 1 - 2 = k - 1 := by omega
      rw [this]
      exact hsd
    rcases sq_cases_sd hn4 ha' hidx hsd' with h1 | h1
    · exact Or.inr ⟨hk3, a, y, ha, hy, hcl, h1, hsd⟩
    · have hy' : y * a ∉ zpowers a := by
        intro h
        apply hy
        have := (zpowers a).mul_mem h ((zpowers a).inv_mem (Subgroup.mem_zpowers a))
        simpa using this
      have ha1 : a ^ (2 ^ k) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
      have hq : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
      have h2n : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hsq : y * a * (y * a) = 1 := by
        have e : y * a * (y * a) = (y * a * y⁻¹) * (y * y) * a := by group
        have h1' : y * y = a ^ (2 ^ (k - 1)) := by rw [← show k + 1 - 2 = k - 1 by omega]; exact h1
        rw [e, hsd, h1', ← pow_add, ← pow_succ]
        have : 2 ^ (k - 1) - 1 + 2 ^ (k - 1) + 1 = 2 ^ k := by omega
        rw [this, ha1]
      have hconj' : y * a * a * (y * a)⁻¹ = a ^ (2 ^ (k - 1) - 1) := by
        rw [← hsd]
        group
      exact Or.inr ⟨hk3, a, y * a, ha, hy', closure_pair_eq_top hidx hy', hsq, hconj'⟩

end CFSG.GH74.Uniqueness.SU.SU1
