module

public import CFSG.LieType.Seitz.Defs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.LieType.Seitz CFSG.Open

section Counting

variable {Γ : Type*} [Group Γ]

theorem card_closure_pair_le {a b : Γ} (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    Nat.card (Subgroup.closure ({a, b} : Set Γ)) ≤ 9 := by
  classical
  have hmul : ∀ x y : Γ, (∃ i j : ℕ, x = a ^ i * b ^ j) → (∃ i j : ℕ, y = a ^ i * b ^ j) →
      ∃ i j : ℕ, x * y = a ^ i * b ^ j := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    refine ⟨i + k, j + l, ?_⟩
    have h : b ^ j * a ^ k = a ^ k * b ^ j := (hab.symm.pow_pow j k).eq
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [h]
      _ = a ^ (i + k) * b ^ (j + l) := by rw [pow_add, pow_add]; group
  let T : Subgroup Γ :=
    { carrier := {x | ∃ i j : ℕ, x = a ^ i * b ^ j}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := fun {x y} hx hy => hmul x y hx hy
      inv_mem' := fun {x} hx => by
        obtain ⟨i, j, rfl⟩ := hx
        have h3 : (a ^ i * b ^ j) * ((a ^ i * b ^ j) * (a ^ i * b ^ j)) = 1 := by
          have e : (a ^ i * b ^ j) * ((a ^ i * b ^ j) * (a ^ i * b ^ j)) = (a ^ i * b ^ j) ^ 3 :=
            (pow_three _).symm
          rw [e, ((hab.pow_pow i j).mul_pow 3), ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3,
            pow_mul, pow_mul, ha, hb]
          simp
        have hinv : (a ^ i * b ^ j)⁻¹ = (a ^ i * b ^ j) * (a ^ i * b ^ j) :=
          inv_eq_of_mul_eq_one_right h3
        rw [hinv]
        exact hmul _ _ ⟨i, j, rfl⟩ ⟨i, j, rfl⟩ }
  have hle : Subgroup.closure ({a, b} : Set Γ) ≤ T := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rcases hx with rfl
      exact ⟨0, 1, by simp⟩
  let f : Fin 3 × Fin 3 → Γ := fun p => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)
  have hsub : (Subgroup.closure ({a, b} : Set Γ) : Set Γ) ⊆ ↑(Finset.univ.image f) := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := hle hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [f]
    have e1 : a ^ i = a ^ (i % 3) := by
      conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, ha, one_pow, one_mul]
    have e2 : b ^ j = b ^ (j % 3) := by
      conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hb, one_pow, one_mul]
    rw [e1, e2]
  calc Nat.card (Subgroup.closure ({a, b} : Set Γ))
      = Set.ncard (Subgroup.closure ({a, b} : Set Γ) : Set Γ) := (Nat.card_coe_set_eq _)
    _ ≤ Set.ncard (↑(Finset.univ.image f) : Set Γ) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.univ.image f).card := Set.ncard_coe_finset _
    _ ≤ (Finset.univ : Finset (Fin 3 × Fin 3)).card := Finset.card_image_le
    _ = 9 := by simp

theorem closure_pair_relIndex {E : Subgroup Γ} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    {a b : Γ} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb' : b ∉ Subgroup.zpowers a) :
    Subgroup.closure ({a, b} : Set Γ) ≤ E ∧
      (Subgroup.closure ({a, b} : Set Γ)).relIndex E = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hFE : Subgroup.closure ({a, b} : Set Γ) ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · rcases hx with rfl
      exact hb
  have ha3 : a ^ 3 = 1 := hE.2 a ha
  have hb3 : b ^ 3 = 1 := hE.2 b hb
  have hab : Commute a b := by
    have := hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hle := card_closure_pair_le hab ha3 hb3
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hz : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hza : Subgroup.zpowers a ≤ Subgroup.closure ({a, b} : Set Γ) :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have hdvd : 3 ∣ Nat.card (Subgroup.closure ({a, b} : Set Γ)) := by
    have := Subgroup.card_dvd_of_le hza
    rwa [hz] at this
  have hdvd27 : Nat.card (Subgroup.closure ({a, b} : Set Γ)) ∣ 27 := by
    have := Subgroup.card_dvd_of_le hFE
    rwa [hcard] at this
  have hne : Nat.card (Subgroup.closure ({a, b} : Set Γ)) ≠ 3 := by
    intro h3
    have hfin : Finite (Subgroup.closure ({a, b} : Set Γ)) :=
      Finite.of_injective (Subgroup.inclusion hFE) (Subgroup.inclusion_injective hFE)
    have : Subgroup.zpowers a = Subgroup.closure ({a, b} : Set Γ) :=
      Subgroup.eq_of_le_of_card_ge hza (by rw [hz, h3])
    exact hb' (this ▸ Subgroup.subset_closure (by simp))
  have h9 : Nat.card (Subgroup.closure ({a, b} : Set Γ)) = 9 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at hle hne hdvd27
    have hc3 : c ≤ 3 := by omega
    interval_cases c <;> simp_all
  refine ⟨hFE, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := Subgroup.closure ({a, b} : Set Γ)) (K := E)
  rw [inf_of_le_left hFE, h9, hcard] at h
  omega

theorem exists_notMem_zpowers {E : Subgroup Γ} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) {a : Γ} (ha : a ∈ E) : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
  by_contra hcon
  push Not at hcon
  have hle : E ≤ Subgroup.zpowers a := fun x hx => hcon x hx
  have ha3 : a ^ 3 = 1 := hE.2 a ha
  have hord : orderOf a ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ha3)
  have hpos : 0 < orderOf a :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, ha3⟩)
  have hfin : Finite (Subgroup.zpowers a) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact hpos.ne')
  have := Subgroup.card_le_of_le hle
  rw [hcard, Nat.card_zpowers] at this
  omega

theorem exists_notMem_closure_pair {E : Subgroup Γ} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) {a b : Γ} (ha : a ∈ E) (hb : b ∈ E) :
    ∃ c ∈ E, c ∉ Subgroup.closure ({a, b} : Set Γ) := by
  by_contra hcon
  push Not at hcon
  have hle : E ≤ Subgroup.closure ({a, b} : Set Γ) := fun x hx => hcon x hx
  have hab : Commute a b := by
    have := hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have h9 := card_closure_pair_le hab (hE.2 a ha) (hE.2 b hb)
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hFE : Subgroup.closure ({a, b} : Set Γ) ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · rcases hx with rfl
      exact hb
  have hfin : Finite (Subgroup.closure ({a, b} : Set Γ)) :=
    Finite.of_injective (Subgroup.inclusion hFE) (Subgroup.inclusion_injective hFE)
  have := Subgroup.card_le_of_le hle
  omega

theorem pow_mul_pow_mem_zpowers {σ ε₁ ε₂ : Γ} (h1 : ε₁ ∉ Subgroup.zpowers σ)
    (h2 : ε₂ ∉ Subgroup.closure ({σ, ε₁} : Set Γ)) (hσ3 : σ ^ 3 = 1)
    (hε₁3 : ε₁ ^ 3 = 1) (hε₂3 : ε₂ ^ 3 = 1) {a b : ℕ}
    (h : ε₁ ^ a * ε₂ ^ b ∈ Subgroup.zpowers σ) : 3 ∣ a ∧ 3 ∣ b := by
  have hcube : ∀ (x : Γ) (n : ℕ), x ^ 3 = 1 → ¬ 3 ∣ n → ∃ m : ℕ, (x ^ n) ^ m = x := by
    intro x n hx hn
    have hn' : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hn' with h' | h'
    · refine ⟨1, ?_⟩
      rw [pow_one]
      conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul, h', pow_one]
    · refine ⟨2, ?_⟩
      rw [← pow_mul]
      have : n * 2 = 3 * (n * 2 / 3) + 1 := by omega
      rw [this, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]
  by_cases hb : 3 ∣ b
  · have hb0 : ε₂ ^ b = 1 := by
      obtain ⟨c, rfl⟩ := hb
      rw [pow_mul, hε₂3, one_pow]
    rw [hb0, mul_one] at h
    refine ⟨?_, hb⟩
    by_contra ha
    obtain ⟨m, hm⟩ := hcube ε₁ a hε₁3 ha
    exact h1 (hm ▸ Subgroup.pow_mem _ h m)
  · exfalso
    have hcl : ε₁ ^ a ∈ Subgroup.closure ({σ, ε₁} : Set Γ) :=
      Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) a
    have hs : σ ∈ Subgroup.closure ({σ, ε₁} : Set Γ) := Subgroup.subset_closure (by simp)
    have hzp : Subgroup.zpowers σ ≤ Subgroup.closure ({σ, ε₁} : Set Γ) :=
      (Subgroup.zpowers_le).2 hs
    have hb2 : ε₂ ^ b ∈ Subgroup.closure ({σ, ε₁} : Set Γ) := by
      have : ε₂ ^ b = (ε₁ ^ a)⁻¹ * (ε₁ ^ a * ε₂ ^ b) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcl) (hzp h)
    obtain ⟨m, hm⟩ := hcube ε₂ b hε₂3 hb
    exact h2 (hm ▸ Subgroup.pow_mem _ hb2 m)

end Counting

section Fixed

variable {G : Type*} [Group G]

theorem mem_seitzHyperGamma_of_fixed {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) {σ ε : MulAut G} (hσ : σ ∈ E) (hε : ε ∈ E) (hσ1 : σ ≠ 1)
    (hεσ : ε ∉ Subgroup.zpowers σ) {k : G} (hkσ : σ k = k) (hkε : ε k = k) :
    k ∈ seitzHyperGamma 3 E := by
  obtain ⟨hFE, hrel⟩ := closure_pair_relIndex hE hcard hσ hε hσ1 hεσ
  have hk : k ∈ fixedPoints (Subgroup.closure ({σ, ε} : Set (MulAut G))) := by
    intro φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hkσ
      · rcases hx with rfl
        exact hkε
    | one => simp
    | mul x y _ _ hx hy => rw [MulAut.mul_apply, hy, hx]
    | inv x _ hx =>
      have : x k = k := hx
      rw [MulAut.inv_apply]
      exact (MulEquiv.symm_apply_eq x).2 this.symm
  exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem ⟨hFE, hrel⟩ hk)

end Fixed

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
