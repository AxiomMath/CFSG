module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup

variable {G : Type*} [Group G]

theorem mul_comm_of_mul_self_eq_one {A : Subgroup G} (hA2 : ∀ x ∈ A, x * x = 1) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have h1 := hA2 _ (mul_mem ha hb)
  calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
    _ = (a * a) * b * a * (b * b) := by group
    _ = b * a := by rw [hA2 a ha, hA2 b hb, one_mul, mul_one]

theorem pow_apply_of_apply_eq {σ : MulAut G} {x : G} (h : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem pow_apply_mem {A : Subgroup G} {σ : MulAut G} (hσA : ∀ x ∈ A, σ x ∈ A) (n : ℕ) {x : G}
    (hx : x ∈ A) : (σ ^ n) x ∈ A := by
  induction n with
  | zero => exact hx
  | succ n ih => rw [pow_succ', MulAut.mul_apply]; exact hσA _ ih

variable [Finite G] {A : Subgroup G}

theorem card_eq_of_fixed_eq_one (hAc : Nat.card A = 2 ^ 11) (σ : MulAut G)
    (hσ11 : ∀ x ∈ A, (σ ^ 11) x = x) {V : Subgroup G} (hVA : V ≤ A) (hV : ∀ x ∈ V, σ x ∈ V)
    (hfix : ∀ x ∈ V, σ x = x → x = 1) : Nat.card V = 1 ∨ Nat.card V = 2 ^ 10 := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have := Fintype.ofFinite V
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm V, ∀ x : V, ((π x : V) : G) = σ x := by
    have hinj : Function.Injective fun x : V => (⟨σ x, hV x x.2⟩ : V) := fun x y h =>
      Subtype.ext (σ.injective (congrArg Subtype.val h))
    exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), fun _ => rfl⟩
  have hiter : ∀ (n : ℕ) (x : V), (((π ^ n) x : V) : G) = (σ ^ n) x := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, MulAut.mul_apply, hπ, ih]
  have hπ11 : π ^ 11 ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [hiter, Equiv.Perm.one_apply]
    exact hσ11 x (hVA x.2)
  have hmod := Equiv.Perm.card_compl_support_modEq hπ11
  have hsupp : (Equiv.Perm.support π)ᶜ = {1} := by
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro h
      exact Subtype.ext (hfix x x.2 ((hπ x).symm.trans (congrArg Subtype.val h)))
    · rintro rfl
      exact Subtype.ext ((hπ 1).trans (map_one σ))
  rw [hsupp, Finset.card_singleton] at hmod
  have hmod' : Nat.card V % 11 = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact hmod.symm
  obtain ⟨k, hk, hkV⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (hAc ▸ Subgroup.card_dvd_of_le hVA)
  rw [hkV] at hmod' ⊢
  interval_cases k <;> revert hmod' <;> decide

theorem exists_commutatorSubgroup (hA2 : ∀ x ∈ A, x * x = 1) (hAc : Nat.card A = 2 ^ 11)
    (σ : MulAut G) (hσA : ∀ x ∈ A, σ x ∈ A) (hσ11 : ∀ x ∈ A, (σ ^ 11) x = x) {u : G}
    (hu : ∀ x ∈ A, σ x = x ↔ x = 1 ∨ x = u) :
    ∃ W : Subgroup G, (∀ x, x ∈ W ↔ ∃ e ∈ A, x = e * σ e) ∧ W ≤ A ∧ (∀ x ∈ W, σ x ∈ W) ∧
      (∀ x ∈ W, σ x = x → x = 1) ∧ Nat.card W = 2 ^ 10 ∧ u ∈ A ∧ u ≠ 1 ∧ u ∉ W ∧
      zpowers u ⊔ W = A := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    mul_comm_of_mul_self_eq_one hA2 ha hb
  obtain ⟨δ, hδ⟩ : ∃ δ : A →* A, ∀ e : A, ((δ e : A) : G) = e * σ e := by
    refine ⟨MonoidHom.mk' (fun e => ⟨e * σ e, A.mul_mem e.2 (hσA e e.2)⟩) fun a b => ?_,
      fun _ => rfl⟩
    apply Subtype.ext
    change ((a : G) * b) * σ ((a : G) * b) = ((a : G) * σ a) * ((b : G) * σ b)
    rw [map_mul]
    calc (a : G) * b * (σ a * σ b) = a * (b * σ a) * σ b := by group
      _ = a * (σ a * b) * σ b := by rw [hcomm _ b.2 _ (hσA _ a.2)]
      _ = a * σ a * (b * σ b) := by group
  set W := δ.range.map A.subtype with hWdef
  have hWmem : ∀ x, x ∈ W ↔ ∃ e ∈ A, x = e * σ e := by
    intro x
    constructor
    · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
      exact ⟨e, e.2, hδ e⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨δ ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, hδ _⟩
  have hWA : W ≤ A := map_subtype_le _
  have hWσ : ∀ x ∈ W, σ x ∈ W := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := (hWmem x).mp hx
    exact (hWmem _).mpr ⟨σ e, hσA e he, map_mul σ _ _⟩
  have hWfix : ∀ x ∈ W, σ x = x → x = 1 := by
    intro x hx hσx
    obtain ⟨e, he, rfl⟩ := (hWmem x).mp hx
    have hσe := hσA e he
    have h2 : (σ ^ 2) e = e := by
      rw [sq, MulAut.mul_apply]
      rw [map_mul, hcomm e he _ hσe] at hσx
      exact mul_left_cancel hσx
    have h11 : (σ ^ 11) e = σ e := by
      rw [show 11 = 1 + 2 * 5 from rfl, pow_add, pow_one, pow_mul, MulAut.mul_apply,
        pow_apply_of_apply_eq h2]
    rw [← h11, hσ11 e he, hA2 e he]
  have hcardA : Nat.card A = Nat.card W * Nat.card δ.ker := by
    rw [hWdef, card_map_of_injective A.subtype_injective,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hkerval : ∀ k : δ.ker, ((k : A) : G) = 1 ∨ ((k : A) : G) = u := by
    intro k
    have hk : ((k : A) : G) * σ (k : A) = 1 := by
      rw [← hδ]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
    have hkσ : σ (k : A) = (k : A) := by
      rw [eq_inv_of_mul_eq_one_right hk, inv_eq_of_mul_eq_one_right (hA2 _ (k : A).2)]
    exact (hu _ (k : A).2).mp hkσ
  have hker2 : Nat.card δ.ker ≤ 2 := by
    classical
    have hinj : Function.Injective fun k : δ.ker => decide (((k : A) : G) = 1) := by
      intro k₁ k₂ h
      apply Subtype.ext
      apply Subtype.ext
      rcases hkerval k₁ with h₁ | h₁ <;> rcases hkerval k₂ with h₂ | h₂
      · rw [h₁, h₂]
      · by_cases hu1 : u = 1
        · rw [h₁, h₂, hu1]
        · simp only [h₁, h₂, hu1, decide_true, decide_false] at h
          exact absurd h Bool.noConfusion
      · by_cases hu1 : u = 1
        · rw [h₁, h₂, hu1]
        · simp only [h₁, h₂, hu1, decide_true, decide_false] at h
          exact absurd h Bool.noConfusion
      · rw [h₁, h₂]
    calc Nat.card δ.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  have hWcard : Nat.card W = 2 ^ 10 := by
    rcases card_eq_of_fixed_eq_one hAc σ hσ11 hWA hWσ hWfix with h | h
    · rw [hAc, h, one_mul] at hcardA
      omega
    · exact h
  have hker2' : Nat.card δ.ker = 2 := by
    rw [hAc, hWcard] at hcardA
    omega
  have : Nontrivial δ.ker := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨k, hk⟩ := exists_ne (1 : δ.ker)
  have hk1 : ((k : A) : G) ≠ 1 := fun h => hk (Subtype.ext (Subtype.ext h))
  have hku : ((k : A) : G) = u := (hkerval k).resolve_left hk1
  have huA : u ∈ A := hku ▸ (k : A).2
  have hu1 : u ≠ 1 := hku ▸ hk1
  have huW : u ∉ W := fun h => hu1 (hWfix u h ((hu u huA).mpr (Or.inr rfl)))
  have hsup : zpowers u ⊔ W = A := by
    set S := zpowers u ⊔ W with hS
    have hSA : S ≤ A := sup_le (zpowers_le.mpr huA) hWA
    obtain ⟨j, hj, hjS⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (hAc ▸ Subgroup.card_dvd_of_le hSA)
    have hWS := Subgroup.card_dvd_of_le (le_sup_right : W ≤ S)
    rw [hWcard, hjS] at hWS
    have hj10 : 10 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hWS
    have hj11 : j = 11 := by
      by_contra hne
      have hSW : W = S :=
        eq_of_le_of_card_ge (le_sup_right : W ≤ S) (by rw [hjS, hWcard, show j = 10 by omega])
      apply huW
      rw [hSW]
      exact (le_sup_left : zpowers u ≤ S) (mem_zpowers u)
    exact eq_of_le_of_card_ge hSA (by rw [hAc, hjS, hj11])
  exact ⟨W, hWmem, hWA, hWσ, hWfix, hWcard, huA, hu1, huW, hsup⟩

theorem eleven_invariant (hA2 : ∀ x ∈ A, x * x = 1) (hAc : Nat.card A = 2 ^ 11) (σ : MulAut G)
    (hσA : ∀ x ∈ A, σ x ∈ A) (hσ11 : ∀ x ∈ A, (σ ^ 11) x = x) {u : G}
    (hu : ∀ x ∈ A, σ x = x ↔ x = 1 ∨ x = u) {U : Subgroup G} (hUA : U ≤ A)
    (hU : ∀ x ∈ U, σ x ∈ U) : U ≤ zpowers u ∨ ∀ e ∈ A, e * σ e ∈ U := by
  obtain ⟨W, hWmem, hWA, hWσ, hWfix, hWcard, -, -, -, -⟩ :=
    exists_commutatorSubgroup hA2 hAc σ hσA hσ11 hu
  by_cases hUu : U ≤ zpowers u
  · exact Or.inl hUu
  right
  obtain ⟨x, hxU, hxu⟩ := IsConcreteLE.not_le_iff_exists.mp hUu
  have hxA := hUA hxU
  have hV := card_eq_of_fixed_eq_one hAc σ hσ11 (V := U ⊓ W) (inf_le_right.trans hWA)
    (fun y hy => ⟨hU y hy.1, hWσ y hy.2⟩) (fun y hy => hWfix y hy.2)
  have hxσ : x * σ x ∈ U ⊓ W := ⟨U.mul_mem hxU (hU x hxU), (hWmem _).mpr ⟨x, hxA, rfl⟩⟩
  have hxσ1 : x * σ x ≠ 1 := by
    intro h1
    apply hxu
    have h2 : σ x = x := by
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right (hA2 x hxA)]
    rcases (hu x hxA).mp h2 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers u
  have hV1 : Nat.card ↥(U ⊓ W) ≠ 1 := by
    intro h1
    rw [Subgroup.eq_bot_of_card_eq _ h1] at hxσ
    exact hxσ1 ((mem_bot).mp hxσ)
  have hVW : U ⊓ W = W :=
    eq_of_le_of_card_ge inf_le_right (by rw [hWcard, hV.resolve_left hV1])
  intro e he
  have h1 : e * σ e ∈ U ⊓ W := by
    rw [hVW]
    exact (hWmem _).mpr ⟨e, he, rfl⟩
  exact h1.1

omit [Finite G] in
theorem exists_pow_pow_apply {σ : MulAut G} (hσ11 : ∀ x ∈ A, (σ ^ 11) x = x) {m : ℕ}
    (hm : ¬ 11 ∣ m) : ∃ k : ℕ, ∀ x ∈ A, ((σ ^ m) ^ k) x = σ x := by
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm).symm (by norm_num : 1 < 11)
  refine ⟨k, fun x hx => ?_⟩
  rw [← pow_mul, ← Nat.mod_add_div (m * k) 11, hk, pow_add, pow_one, pow_mul, MulAut.mul_apply,
    pow_apply_of_apply_eq (hσ11 x hx)]

theorem eleven_invariant_of_pow (hA2 : ∀ x ∈ A, x * x = 1) (hAc : Nat.card A = 2 ^ 11)
    (σ : MulAut G) (hσA : ∀ x ∈ A, σ x ∈ A) (hσ11 : ∀ x ∈ A, (σ ^ 11) x = x) {u : G}
    (hu : ∀ x ∈ A, σ x = x ↔ x = 1 ∨ x = u) {m : ℕ} (hm : ¬ 11 ∣ m) {U : Subgroup G}
    (hUA : U ≤ A) (hU : ∀ x ∈ U, (σ ^ m) x ∈ U) : U ≤ zpowers u ∨ ∀ e ∈ A, e * σ e ∈ U := by
  obtain ⟨k, hk⟩ := exists_pow_pow_apply hσ11 hm
  have hUk : ∀ (j : ℕ) {x : G}, x ∈ U → ((σ ^ m) ^ j) x ∈ U := by
    intro j x hx
    induction j with
    | zero => exact hx
    | succ j ih => rw [pow_succ', MulAut.mul_apply]; exact hU _ ih
  refine eleven_invariant hA2 hAc σ hσA hσ11 hu hUA fun x hx => ?_
  rw [← hk x (hUA hx)]
  exact hUk k hx

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
