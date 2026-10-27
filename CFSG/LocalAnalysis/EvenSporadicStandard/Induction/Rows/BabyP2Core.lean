module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP2Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowComponent

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup

structure IsSuborbit {G : Type} [Group G] (H : Subgroup G) (V S : Set G) (n : ℕ) : Prop where
  subset : S ⊆ V
  inv : ∀ h ∈ H, ∀ s ∈ S, h * s * h⁻¹ ∈ S
  trans : ∀ s ∈ S, ∀ s' ∈ S, ∃ h ∈ H, h * s * h⁻¹ = s'
  ncard : S.ncard = n

theorem overgroups_arith (a₀ a₁ a₂ a₃ : ℕ)
    (h₀ : 2 * a₀ = 0 ∨ 2 * a₀ = 3968055 ∨ 2 * a₀ = 2 * 3968055)
    (h₁ : 2 * a₁ = 0 ∨ 2 * a₁ = 23113728 ∨ 2 * a₁ = 2 * 23113728)
    (h₂ : 2 * a₂ = 0 ∨ 2 * a₂ = 2370830336 ∨ 2 * a₂ = 2 * 2370830336)
    (h₃ : 2 * a₃ = 0 ∨ 2 * a₃ = 11174042880 ∨ 2 * a₃ = 2 * 11174042880)
    (hd : 1 + a₀ + a₁ + a₂ + a₃ ∣ 2 * 13571955000) :
    1 + a₀ + a₁ + a₂ + a₃ = 1 ∨ 1 + a₀ + a₁ + a₂ + a₃ = 13571955000 := by
  have e0 : a₀ = 0 ∨ a₀ = 3968055 := by omega
  have e1 : a₁ = 0 ∨ a₁ = 11556864 ∨ a₁ = 23113728 := by omega
  have e2 : a₂ = 0 ∨ a₂ = 1185415168 ∨ a₂ = 2370830336 := by omega
  have e3 : a₃ = 0 ∨ a₃ = 5587021440 ∨ a₃ = 11174042880 := by omega
  rcases e0 with rfl | rfl <;> rcases e1 with rfl | rfl | rfl <;> rcases e2 with rfl | rfl | rfl <;>
    rcases e3 with rfl | rfl | rfl <;> omega

section Decomp

variable {G : Type*} [Finite G]

theorem ovg_ncard_decomp {r : G} {S₀ S₁ S₂ S₃ Y : Set G} (hrY : r ∈ Y)
    (hcover : ∀ s ∈ Y, s ≠ r → s ∈ S₀ ∨ s ∈ S₁ ∨ s ∈ S₂ ∨ s ∈ S₃)
    (hr₀ : r ∉ S₀) (hr₁ : r ∉ S₁) (hr₂ : r ∉ S₂) (hr₃ : r ∉ S₃)
    (d₀₁ : Disjoint S₀ S₁) (d₀₂ : Disjoint S₀ S₂) (d₀₃ : Disjoint S₀ S₃)
    (d₁₂ : Disjoint S₁ S₂) (d₁₃ : Disjoint S₁ S₃) (d₂₃ : Disjoint S₂ S₃) :
    Y.ncard = 1 + (Y ∩ S₀).ncard + (Y ∩ S₁).ncard + (Y ∩ S₂).ncard + (Y ∩ S₃).ncard := by
  have hY : Y = ((({r} ∪ Y ∩ S₀) ∪ Y ∩ S₁) ∪ Y ∩ S₂) ∪ Y ∩ S₃ := by
    ext s
    constructor
    · intro hs
      by_cases hsr : s = r
      · exact Or.inl (Or.inl (Or.inl (Or.inl hsr)))
      · rcases hcover s hs hsr with h | h | h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hs, h⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨hs, h⟩))
        · exact Or.inl (Or.inr ⟨hs, h⟩)
        · exact Or.inr ⟨hs, h⟩
    · rintro ((((h | ⟨h, -⟩) | ⟨h, -⟩) | ⟨h, -⟩) | ⟨h, -⟩)
      · rw [Set.mem_singleton_iff.1 h]
        exact hrY
      · exact h
      · exact h
      · exact h
      · exact h
  have e1 : (({r} : Set G) ∪ Y ∩ S₀).ncard = 1 + (Y ∩ S₀).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_singleton_left.2 fun h => hr₀ h.2) (Set.toFinite _)
      (Set.toFinite _), Set.ncard_singleton]
  have e2 : ((({r} : Set G) ∪ Y ∩ S₀) ∪ Y ∩ S₁).ncard =
      1 + (Y ∩ S₀).ncard + (Y ∩ S₁).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2
      ⟨Set.disjoint_singleton_left.2 fun h => hr₁ h.2,
        d₀₁.mono Set.inter_subset_right Set.inter_subset_right⟩) (Set.toFinite _)
      (Set.toFinite _), e1]
  have e3 : (((({r} : Set G) ∪ Y ∩ S₀) ∪ Y ∩ S₁) ∪ Y ∩ S₂).ncard =
      1 + (Y ∩ S₀).ncard + (Y ∩ S₁).ncard + (Y ∩ S₂).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2
      ⟨Set.disjoint_union_left.2 ⟨Set.disjoint_singleton_left.2 fun h => hr₂ h.2,
        d₀₂.mono Set.inter_subset_right Set.inter_subset_right⟩,
        d₁₂.mono Set.inter_subset_right Set.inter_subset_right⟩) (Set.toFinite _)
      (Set.toFinite _), e2]
  have e4 : ((((({r} : Set G) ∪ Y ∩ S₀) ∪ Y ∩ S₁) ∪ Y ∩ S₂) ∪ Y ∩ S₃).ncard =
      1 + (Y ∩ S₀).ncard + (Y ∩ S₁).ncard + (Y ∩ S₂).ncard + (Y ∩ S₃).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2
      ⟨Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
        ⟨Set.disjoint_singleton_left.2 fun h => hr₃ h.2,
          d₀₃.mono Set.inter_subset_right Set.inter_subset_right⟩,
        d₁₃.mono Set.inter_subset_right Set.inter_subset_right⟩,
        d₂₃.mono Set.inter_subset_right Set.inter_subset_right⟩) (Set.toFinite _)
      (Set.toFinite _), e3]
  exact (congrArg Set.ncard hY).trans e4

end Decomp

section Core

variable {G : Type} [Group G] [Finite G]

theorem ovg_dvd_of_mul_mul_dvd {k j o N : ℕ} (hk : 0 < k) (h : k * j * o ∣ 2 * k * N) :
    o ∣ 2 * N := by
  have h2 : k * (j * o) ∣ k * (2 * N) := by
    have e1 : k * (j * o) = k * j * o := (mul_assoc _ _ _).symm
    have e2 : k * (2 * N) = 2 * k * N := by ring
    rw [e1, e2]
    exact h
  exact (Dvd.intro_left j rfl).trans (Nat.dvd_of_mul_dvd_mul_left hk h2)

theorem overgroups_core {r : G} {K X : Subgroup G} (hKX : K ≤ X)
    (hKr : K ≤ centralizer ({r} : Set G))
    (hidx : Nat.card (centralizer ({r} : Set G)) = 2 * Nat.card K) {V S₀ S₁ S₂ S₃ : Set G}
    (hrV : r ∈ V) (hVconj : ∀ g s, s ∈ V → g * s * g⁻¹ ∈ V)
    (hVcl : ∀ s ∈ V, ∃ g : G, g * r * g⁻¹ = s)
    (h₀ : IsSuborbit (centralizer ({r} : Set G)) V S₀ 3968055)
    (h₁ : IsSuborbit (centralizer ({r} : Set G)) V S₁ 23113728)
    (h₂ : IsSuborbit (centralizer ({r} : Set G)) V S₂ 2370830336)
    (h₃ : IsSuborbit (centralizer ({r} : Set G)) V S₃ 11174042880)
    (hcover : ∀ s ∈ V, s ≠ r → s ∈ S₀ ∨ s ∈ S₁ ∨ s ∈ S₂ ∨ s ∈ S₃)
    (hr₀ : r ∉ S₀) (hr₁ : r ∉ S₁) (hr₂ : r ∉ S₂) (hr₃ : r ∉ S₃)
    (d₀₁ : Disjoint S₀ S₁) (d₀₂ : Disjoint S₀ S₂) (d₀₃ : Disjoint S₀ S₃)
    (d₁₂ : Disjoint S₁ S₂) (d₁₃ : Disjoint S₁ S₃) (d₂₃ : Disjoint S₂ S₃)
    (hsimple : IsSimpleGroup G) :
    X ≤ centralizer ({r} : Set G) ∨ X = ⊤ := by
  set H : Subgroup G := centralizer ({r} : Set G) with hH
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hK2 : (K.subgroupOf H).index = 2 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf H)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKr).toEquiv, hidx] at h1
    exact Nat.eq_of_mul_eq_mul_left hKpos (by rw [h1]; exact mul_comm _ _)
  set O : Set G := {y | ∃ h ∈ X, h * r * h⁻¹ = y} with hO
  have hrO : r ∈ O := ⟨1, X.one_mem, by simp⟩
  have hOV : O ⊆ V := by
    rintro _ ⟨h, -, rfl⟩
    exact hVconj h r hrV
  have hOX : ∀ x ∈ X, ∀ s ∈ O, x * s * x⁻¹ ∈ O := by
    rintro x hx _ ⟨y, hy, rfl⟩
    exact ⟨x * y, X.mul_mem hx hy, by group⟩
  have hOS : Nat.card ↥(X ⊓ H) * O.ncard = Nat.card X :=
    CFSG.EvenSporadicStandard.Solomon78.card_inf_centralizer_mul_ncard_conj X r
  have hVeq : ({y | ∃ h ∈ (⊤ : Subgroup G), h * r * h⁻¹ = y} : Set G) = V := by
    ext y
    constructor
    · rintro ⟨h, -, rfl⟩
      exact hVconj h r hrV
    · intro hy
      obtain ⟨g, hg⟩ := hVcl y hy
      exact ⟨g, mem_top g, hg⟩
  have hGV : Nat.card H * V.ncard = Nat.card G := by
    have h := CFSG.EvenSporadicStandard.Solomon78.card_inf_centralizer_mul_ncard_conj
      (⊤ : Subgroup G) r
    rw [hVeq, top_inf_eq, Subgroup.card_top] at h
    exact h
  have hVcard : V.ncard = 13571955000 := by
    have h := ovg_ncard_decomp (Y := V) hrV hcover hr₀ hr₁ hr₂ hr₃ d₀₁ d₀₂ d₀₃ d₁₂ d₁₃ d₂₃
    rw [Set.inter_eq_right.2 h₀.subset, Set.inter_eq_right.2 h₁.subset,
      Set.inter_eq_right.2 h₂.subset, Set.inter_eq_right.2 h₃.subset, h₀.ncard, h₁.ncard,
      h₂.ncard, h₃.ncard] at h
    omega
  have hpiece : ∀ (S : Set G) (n : ℕ), IsSuborbit H V S n →
      2 * (O ∩ S).ncard = 0 ∨ 2 * (O ∩ S).ncard = n ∨ 2 * (O ∩ S).ncard = 2 * n := by
    intro S n hS
    by_cases hne : (O ∩ S).Nonempty
    · rcases card_invariant_subset_of_index_two hKr hK2 hS.inv hS.trans Set.inter_subset_right
        (fun k hk t ht => ⟨hOX k (hKX hk) t ht.1, hS.inv k (hKr hk) t ht.2⟩) hne with h | h
      · right
        right
        rw [h, hS.ncard]
      · right
        left
        rw [h, hS.ncard]
    · left
      rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.ncard_empty]
  have hOcard : O.ncard =
      1 + (O ∩ S₀).ncard + (O ∩ S₁).ncard + (O ∩ S₂).ncard + (O ∩ S₃).ncard :=
    ovg_ncard_decomp hrO (fun s hs hsr => hcover s (hOV hs) hsr) hr₀ hr₁ hr₂ hr₃ d₀₁ d₀₂ d₀₃ d₁₂
      d₁₃ d₂₃
  have hKm : Nat.card K ∣ Nat.card ↥(X ⊓ H) := Subgroup.card_dvd_of_le (le_inf hKX hKr)
  have hmH : Nat.card ↥(X ⊓ H) ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨j, hj⟩ := hKm
  have hj2 : j = 1 ∨ j = 2 := by
    have h1 : Nat.card K * j ∣ Nat.card K * 2 := by
      have h := hmH
      rw [hj, hidx, mul_comm 2] at h
      exact h
    exact (Nat.dvd_prime Nat.prime_two).1 (Nat.dvd_of_mul_dvd_mul_left hKpos h1)
  have hOdvd : O.ncard ∣ 2 * 13571955000 := by
    have h1 : Nat.card ↥(X ⊓ H) * O.ncard ∣ Nat.card H * V.ncard := by
      rw [hOS, hGV]
      exact Subgroup.card_subgroup_dvd_card X
    rw [hj, hidx, hVcard] at h1
    exact ovg_dvd_of_mul_mul_dvd hKpos h1
  have harith := overgroups_arith _ _ _ _ (hpiece S₀ _ h₀) (hpiece S₁ _ h₁) (hpiece S₂ _ h₂)
    (hpiece S₃ _ h₃) (by rw [← hOcard]; exact hOdvd)
  rw [← hOcard] at harith
  rcases harith with h1 | h1
  · left
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have hra : r = a := by
      have h := hrO
      rw [ha] at h
      exact h
    intro x hx
    have hxO : x * r * x⁻¹ ∈ O := ⟨x, hx, rfl⟩
    rw [ha, Set.mem_singleton_iff, ← hra] at hxO
    rw [hH, mem_centralizer_singleton_iff]
    calc x * r = x * r * x⁻¹ * x := by group
      _ = r * x := by rw [hxO]
  · right
    have hOV' : O = V := Set.eq_of_subset_of_ncard_le hOV (by rw [h1, hVcard]) (Set.toFinite _)
    have hXcard : Nat.card ↥(X ⊓ H) * V.ncard = Nat.card X := by
      rw [← hOV']
      exact hOS
    have hVpos : 0 < V.ncard := by
      rw [hVcard]
      norm_num
    have h2 : X.index * Nat.card ↥(X ⊓ H) = Nat.card H := by
      apply Nat.eq_of_mul_eq_mul_right hVpos
      calc X.index * Nat.card ↥(X ⊓ H) * V.ncard
          = X.index * (Nat.card ↥(X ⊓ H) * V.ncard) := by ring
        _ = X.index * Nat.card X := by rw [hXcard]
        _ = Nat.card G := Subgroup.index_mul_card X
        _ = Nat.card H * V.ncard := hGV.symm
    rw [hj, hidx] at h2
    have h3 : X.index * j = 2 := by
      apply Nat.eq_of_mul_eq_mul_left hKpos
      calc Nat.card K * (X.index * j) = X.index * (Nat.card K * j) := by ring
        _ = 2 * Nat.card K := h2
        _ = Nat.card K * 2 := mul_comm _ _
    rcases hj2 with rfl | rfl
    · exfalso
      have hi2 : X.index = 2 := by simpa using h3
      have hn := normal_of_index_eq_two hi2
      rcases hsimple.eq_bot_or_eq_top_of_normal X with hb | ht
      · rw [hb, index_bot] at hi2
        have h4 : Nat.card H * V.ncard = 2 := by rw [hGV]; exact hi2
        rw [hVcard] at h4
        have h5 : 0 < Nat.card H := Nat.card_pos
        omega
      · rw [ht, index_top] at hi2
        exact absurd hi2 (by norm_num)
    · exact index_eq_one.1 (by omega)

end Core

end CFSG.EvenSporadicStandard.Induction.Hyp
