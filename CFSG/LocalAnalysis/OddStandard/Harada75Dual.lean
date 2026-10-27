module

public import CFSG.LocalAnalysis.OddStandard.Harada75Iota
public import CFSG.LocalAnalysis.OddStandard.Harada75Count
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.OddStandard.Harada75

variable {S : Type} [Group S]

private theorem dual_pw_inj {z : S} (hz1 : z ≠ 1) {c c' : ZMod 2} (h : pw z c = pw z c') :
    c = c' := by
  rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases c' with rfl | rfl
  · rfl
  · exfalso
    rw [pw_zero, pw_one] at h
    exact hz1 h.symm
  · exfalso
    rw [pw_one, pw_zero] at h
    exact hz1 h
  · rfl

private theorem dual_pw_comm {z : S} (hzc : ∀ s : S, s * z = z * s) (c : ZMod 2) (s : S) :
    s * pw z c = pw z c * s := by
  rcases zmod2_cases c with rfl | rfl
  · rw [pw_zero, mul_one, one_mul]
  · rw [pw_one]
    exact hzc s

private theorem dual_swap {z x y : S} (hz2 : z * z = 1) (h : x * y = y * x * z) :
    y * x = x * y * z :=
  calc y * x = y * x * (z * z) := by rw [hz2, mul_one]
    _ = y * x * z * z := (mul_assoc _ _ _).symm
    _ = x * y * z := by rw [← h]

private theorem dual_card_le_finset {G : Type} [Group G] [Finite G] (U : Subgroup G)
    (F : Finset G) (h : ∀ x ∈ U, x ∈ F) : Nat.card U ≤ F.card := by
  have h1 : (U : Set G) ⊆ (F : Set G) := fun x hx => h x hx
  have h2 := Set.ncard_le_ncard h1 (Finset.finite_toSet F)
  rw [Set.ncard_coe_finset] at h2
  rwa [← Nat.card_coe_set_eq] at h2

private theorem dual_A_le_closure [Finite S] {A : Subgroup S} {z f₁ f₂ : S}
    (hA8 : Nat.card A = 8) (hzA : z ∈ A) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hf₁ : f₁ ∈ A) (hf₂ : f₂ ∈ A) (h1 : f₁ ≠ 1 ∧ f₁ ≠ z)
    (h2 : f₂ ≠ 1 ∧ f₂ ≠ z ∧ f₂ ≠ f₁ ∧ f₂ ≠ f₁ * z) :
    ∀ a ∈ A, a ∈ Subgroup.closure ({f₁, f₂, z} : Set S) := by
  classical
  have hCA : Subgroup.closure ({f₁, f₂, z} : Set S) ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h <;> rw [h] <;> assumption
  have hf₁C : f₁ ∈ Subgroup.closure ({f₁, f₂, z} : Set S) := Subgroup.subset_closure (by simp)
  have hf₂C : f₂ ∈ Subgroup.closure ({f₁, f₂, z} : Set S) := Subgroup.subset_closure (by simp)
  have hzC : z ∈ Subgroup.closure ({f₁, f₂, z} : Set S) := Subgroup.subset_closure (by simp)
  have hf₁zC : f₁ * z ∈ Subgroup.closure ({f₁, f₂, z} : Set S) :=
    Subgroup.mul_mem _ hf₁C hzC
  have hfive : ({1, f₁, z, f₁ * z, f₂} : Finset S).card ≤
      Nat.card (Subgroup.closure ({f₁, f₂, z} : Set S)) :=
    finset_card_le_subgroup _ _ (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h | h | h <;> rw [h]
      exacts [Subgroup.one_mem _, hf₁C, hzC, hf₁zC, hf₂C])
  have n1 : (1 : S) ≠ f₁ := h1.1.symm
  have n2 : (1 : S) ≠ z := hz1.symm
  have n3 : (1 : S) ≠ f₁ * z := by
    intro h
    apply h1.2
    calc f₁ = f₁ * (z * z) := by rw [hz2, mul_one]
      _ = f₁ * z * z := (mul_assoc _ _ _).symm
      _ = z := by rw [← h, one_mul]
  have n4 : (1 : S) ≠ f₂ := h2.1.symm
  have n5 : f₁ ≠ z := h1.2
  have n6 : f₁ ≠ f₁ * z := by
    intro h
    apply hz1
    exact mul_left_cancel (a := f₁) (by rw [← h, mul_one])
  have n7 : f₁ ≠ f₂ := h2.2.2.1.symm
  have n8 : z ≠ f₁ * z := by
    intro h
    apply h1.1
    exact mul_right_cancel (b := z) (by rw [← h, one_mul])
  have n9 : z ≠ f₂ := h2.2.1.symm
  have n10 : f₁ * z ≠ f₂ := h2.2.2.2.symm
  have hcard : ({1, f₁, z, f₁ * z, f₂} : Finset S).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10]
  have hdvd : Nat.card (Subgroup.closure ({f₁, f₂, z} : Set S)) ∣ Nat.card A :=
    Subgroup.card_dvd_of_le hCA
  rw [hA8] at hdvd
  have hC8 : Nat.card (Subgroup.closure ({f₁, f₂, z} : Set S)) = 8 := by
    have hle : Nat.card (Subgroup.closure ({f₁, f₂, z} : Set S)) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hdvd
    have h5 : 5 ≤ Nat.card (Subgroup.closure ({f₁, f₂, z} : Set S)) := hcard ▸ hfive
    generalize Nat.card (Subgroup.closure ({f₁, f₂, z} : Set S)) = n at hdvd hle h5
    interval_cases n <;> first | rfl | exact absurd hdvd (by decide)
  have hEq : Subgroup.closure ({f₁, f₂, z} : Set S) = A :=
    Subgroup.eq_of_le_of_card_ge hCA (by rw [hC8, hA8])
  intro a ha
  rw [hEq]
  exact ha

private theorem dual_exists_sign {A B : Subgroup S} {z : S}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a ∨ a * b = b * a * z) :
    ∃ ζ : S → S → ZMod 2, ∀ a ∈ A, ∀ b ∈ B, a * b = b * a * pw z (ζ a b) := by
  classical
  refine ⟨fun a b => if a * b = b * a then 0 else 1, fun a ha b hb => ?_⟩
  by_cases h : a * b = b * a
  · simp only [h, ite_true, pw_zero, mul_one]
  · simp only [h, ite_false, pw_one]
    exact (hcomm a ha b hb).resolve_left h

private theorem dual_sign_zero_iff {A B : Subgroup S} {z : S} (hz1 : z ≠ 1)
    {ζ : S → S → ZMod 2} (hζ : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a * pw z (ζ a b))
    {a b : S} (ha : a ∈ A) (hb : b ∈ B) : ζ a b = 0 ↔ a * b = b * a := by
  have h := hζ a ha b hb
  constructor
  · intro h0
    rw [h0, pw_zero, mul_one] at h
    exact h
  · intro hab
    rw [hab] at h
    have h' : b * a * pw z (ζ a b) = b * a * pw z 0 := by rw [pw_zero, mul_one]; exact h.symm
    exact dual_pw_inj hz1 (mul_left_cancel h')

private theorem dual_sign_mul {A B : Subgroup S} {z : S} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzc : ∀ s : S, s * z = z * s) {ζ : S → S → ZMod 2}
    (hζ : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a * pw z (ζ a b))
    {f : S} (hf : f ∈ A) {b b' : S} (hb : b ∈ B) (hb' : b' ∈ B) :
    ζ f (b * b') = ζ f b + ζ f b' := by
  have h1 := hζ f hf b hb
  have h2 := hζ f hf b' hb'
  have h3 := hζ f hf (b * b') (B.mul_mem hb hb')
  have h4 : f * (b * b') = b * b' * f * pw z (ζ f b' + ζ f b) := by
    calc f * (b * b') = (f * b) * b' := (mul_assoc _ _ _).symm
      _ = (b * f * pw z (ζ f b)) * b' := by rw [h1]
      _ = b * f * (pw z (ζ f b) * b') := mul_assoc _ _ _
      _ = b * f * (b' * pw z (ζ f b)) := by rw [← dual_pw_comm hzc (ζ f b) b']
      _ = b * (f * b') * pw z (ζ f b) := by simp only [mul_assoc]
      _ = b * (b' * f * pw z (ζ f b')) * pw z (ζ f b) := by rw [h2]
      _ = b * b' * f * (pw z (ζ f b') * pw z (ζ f b)) := by simp only [mul_assoc]
      _ = b * b' * f * pw z (ζ f b' + ζ f b) := by rw [pw_add hz2]
  have h5 : pw z (ζ f (b * b')) = pw z (ζ f b' + ζ f b) := mul_left_cancel (h3.symm.trans h4)
  rw [dual_pw_inj hz1 h5, add_comm]

private theorem dual_commutes {A : Subgroup S} {z f₁ f₂ b : S}
    (hcl : ∀ a ∈ A, a ∈ Subgroup.closure ({f₁, f₂, z} : Set S))
    (hzc : ∀ s : S, s * z = z * s) (h₁ : f₁ * b = b * f₁) (h₂ : f₂ * b = b * f₂) :
    ∀ a ∈ A, a * b = b * a := by
  intro a ha
  have hle : Subgroup.closure ({f₁, f₂, z} : Set S) ≤ Subgroup.centralizer {b} := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    rcases hx with h | h | h
    · rw [h]
      exact h₁.symm
    · rw [h]
      exact h₂.symm
    · rw [h]
      exact hzc b
  exact (Subgroup.mem_centralizer_iff.mp (hle (hcl a ha)) b rfl).symm

private theorem dual_zmod2_aux : ∀ x₁ y₁ x₂ y₂ : ZMod 2, ¬ (x₁ = 0 ∧ y₁ = 0) →
    ¬ (x₂ = 0 ∧ y₂ = 0) → ¬ (x₁ = x₂ ∧ y₁ = y₂) →
    ((x₁ = 1 ∧ y₁ = 0) ∨ (x₂ = 1 ∧ y₂ = 0) ∨ (x₁ + x₂ = 1 ∧ y₁ + y₂ = 0)) ∧
    ((x₁ = 0 ∧ y₁ = 1) ∨ (x₂ = 0 ∧ y₂ = 1) ∨ (x₁ + x₂ = 0 ∧ y₁ + y₂ = 1)) := by
  decide

theorem exists_hyperbolic_dual {S : Type} [Group S] [Finite S] {A B : Subgroup S} {z f₁ f₂ : S}
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA8 : Nat.card A = 8)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hB2 : ∀ b ∈ B, b * b = 1)
    (hB8 : Nat.card B = 8)
    (hzc : ∀ s : S, s * z = z * s) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hAB : ∀ x : S, (x ∈ A ∧ x ∈ B) ↔ (x = 1 ∨ x = z))
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a ∨ a * b = b * a * z)
    (hCA : ∀ a ∈ A, (∀ b ∈ B, a * b = b * a) → a = 1 ∨ a = z)
    (hCB : ∀ b ∈ B, (∀ a ∈ A, a * b = b * a) → b = 1 ∨ b = z)
    (hf₁ : f₁ ∈ A) (hf₂ : f₂ ∈ A) (h1 : f₁ ≠ 1 ∧ f₁ ≠ z)
    (h2 : f₂ ≠ 1 ∧ f₂ ≠ z ∧ f₂ ≠ f₁ ∧ f₂ ≠ f₁ * z) :
    ∃ e₁ e₂ : S, e₁ ∈ B ∧ e₂ ∈ B ∧ Pres e₁ e₂ f₁ f₂ z ∧
      (∀ a ∈ A, a ∈ Subgroup.closure ({f₁, f₂, z} : Set S)) := by
  classical
  have hzA : z ∈ A := ((hAB z).2 (Or.inr rfl)).1
  have hcl := dual_A_le_closure hA8 hzA hz1 hz2 hf₁ hf₂ h1 h2
  obtain ⟨ζ, hζ⟩ := dual_exists_sign (A := A) (B := B) (z := z) hcomm
  have hK : ∀ b ∈ B, ζ f₁ b = 0 → ζ f₂ b = 0 → b = 1 ∨ b = z := by
    intro b hb h₁ h₂
    have c₁ := (dual_sign_zero_iff hz1 hζ hf₁ hb).mp h₁
    have c₂ := (dual_sign_zero_iff hz1 hζ hf₂ hb).mp h₂
    exact hCB b hb (dual_commutes hcl hzc c₁ c₂)
  have hb₁ : ∃ b₁ ∈ B, b₁ ≠ 1 ∧ b₁ ≠ z := by
    by_contra hne
    push Not at hne
    rcases hCA f₁ hf₁ (fun b hb => by
      by_cases hb1 : b = 1
      · rw [hb1, mul_one, one_mul]
      · rw [hne b hb hb1]
        exact hzc f₁) with h | h
    exacts [h1.1 h, h1.2 h]
  obtain ⟨b₁, hb₁B, hb₁1, hb₁z⟩ := hb₁
  have hb₂ : ∃ b₂ ∈ B, b₂ ≠ 1 ∧ b₂ ≠ z ∧ b₂ ≠ b₁ ∧ b₂ ≠ b₁ * z := by
    by_contra hne
    push Not at hne
    have hle := dual_card_le_finset B ({1, z, b₁, b₁ * z} : Finset S) (by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      by_cases hx2 : x = z
      · simp [hx2]
      by_cases hx3 : x = b₁
      · simp [hx3]
      · simp [hne x hx hx1 hx2 hx3])
    have h4 : ({1, z, b₁, b₁ * z} : Finset S).card ≤ 4 := Finset.card_le_four
    omega
  obtain ⟨b₂, hb₂B, hb₂1, hb₂z, hb₂b₁, hb₂b₁z⟩ := hb₂
  have hn₁ : ¬ (ζ f₁ b₁ = 0 ∧ ζ f₂ b₁ = 0) := by
    rintro ⟨h₁, h₂⟩
    rcases hK b₁ hb₁B h₁ h₂ with h | h
    exacts [hb₁1 h, hb₁z h]
  have hn₂ : ¬ (ζ f₁ b₂ = 0 ∧ ζ f₂ b₂ = 0) := by
    rintro ⟨h₁, h₂⟩
    rcases hK b₂ hb₂B h₁ h₂ with h | h
    exacts [hb₂1 h, hb₂z h]
  have hn₃ : ¬ (ζ f₁ b₁ = ζ f₁ b₂ ∧ ζ f₂ b₁ = ζ f₂ b₂) := by
    rintro ⟨h₁, h₂⟩
    have z₁ : ζ f₁ (b₁ * b₂) = 0 := by
      rw [dual_sign_mul hz1 hz2 hzc hζ hf₁ hb₁B hb₂B, ← h₁]
      exact CharTwo.add_self_eq_zero _
    have z₂ : ζ f₂ (b₁ * b₂) = 0 := by
      rw [dual_sign_mul hz1 hz2 hzc hζ hf₂ hb₁B hb₂B, ← h₂]
      exact CharTwo.add_self_eq_zero _
    have hb₁sq := hB2 b₁ hb₁B
    have hrec : b₂ = b₁ * (b₁ * b₂) := by rw [← mul_assoc, hb₁sq, one_mul]
    rcases hK _ (B.mul_mem hb₁B hb₂B) z₁ z₂ with h | h
    · apply hb₂b₁
      rw [hrec, h, mul_one]
    · apply hb₂b₁z
      rw [hrec, h]
  obtain ⟨hex₁, hex₂⟩ := dual_zmod2_aux _ _ _ _ hn₁ hn₂ hn₃
  have he₁ : ∃ e ∈ B, ζ f₁ e = 1 ∧ ζ f₂ e = 0 := by
    rcases hex₁ with h | h | h
    · exact ⟨b₁, hb₁B, h.1, h.2⟩
    · exact ⟨b₂, hb₂B, h.1, h.2⟩
    · refine ⟨b₁ * b₂, B.mul_mem hb₁B hb₂B, ?_, ?_⟩
      · rw [dual_sign_mul hz1 hz2 hzc hζ hf₁ hb₁B hb₂B]
        exact h.1
      · rw [dual_sign_mul hz1 hz2 hzc hζ hf₂ hb₁B hb₂B]
        exact h.2
  have he₂ : ∃ e ∈ B, ζ f₁ e = 0 ∧ ζ f₂ e = 1 := by
    rcases hex₂ with h | h | h
    · exact ⟨b₁, hb₁B, h.1, h.2⟩
    · exact ⟨b₂, hb₂B, h.1, h.2⟩
    · refine ⟨b₁ * b₂, B.mul_mem hb₁B hb₂B, ?_, ?_⟩
      · rw [dual_sign_mul hz1 hz2 hzc hζ hf₁ hb₁B hb₂B]
        exact h.1
      · rw [dual_sign_mul hz1 hz2 hzc hζ hf₂ hb₁B hb₂B]
        exact h.2
  obtain ⟨e₁, he₁B, he₁₁, he₁₂⟩ := he₁
  obtain ⟨e₂, he₂B, he₂₁, he₂₂⟩ := he₂
  refine ⟨e₁, e₂, he₁B, he₂B, ?_, hcl⟩
  have c₁₁ := hζ f₁ hf₁ e₁ he₁B
  have c₁₂ := hζ f₂ hf₂ e₁ he₁B
  have c₂₁ := hζ f₁ hf₁ e₂ he₂B
  have c₂₂ := hζ f₂ hf₂ e₂ he₂B
  rw [he₁₁, pw_one] at c₁₁
  rw [he₁₂, pw_zero, mul_one] at c₁₂
  rw [he₂₁, pw_zero, mul_one] at c₂₁
  rw [he₂₂, pw_one] at c₂₂
  exact
    { z_sq := hz2
      z_ne := hz1
      z_cent := hzc
      e₁_sq := hB2 e₁ he₁B
      e₂_sq := hB2 e₂ he₂B
      f₁_sq := hA2 f₁ hf₁
      f₂_sq := hA2 f₂ hf₂
      e₁e₂ := hBc e₁ he₁B e₂ he₂B
      f₁f₂ := hAc f₁ hf₁ f₂ hf₂
      e₁f₁ := dual_swap hz2 c₁₁
      e₂f₂ := dual_swap hz2 c₂₂
      e₁f₂ := c₁₂.symm
      e₂f₁ := c₂₁.symm }

end CFSG.OddStandard.Harada75
