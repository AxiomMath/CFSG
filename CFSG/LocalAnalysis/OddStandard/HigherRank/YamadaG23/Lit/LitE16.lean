module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem lit_card_modEq_fix {α : Type*} [Finite α] (σ : Equiv.Perm α) (h : σ ^ 5 = 1) :
    Nat.card α ≡ Nat.card {a // σ a = a} [MOD 5] := by
  classical
  haveI := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h1 := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := σ) (by simpa using h)
  have h2 : Nat.card {a // σ a = a} = σ.supportᶜ.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext a
    simp [Equiv.Perm.mem_support]
  rw [h2, Nat.card_eq_fintype_card]
  exact h1.symm

theorem lit_one_or_sixteen {c : ℕ} (hd : c ∣ 16) (hm : c ≡ 1 [MOD 5]) : c = 1 ∨ c = 16 := by
  have hle : c ≤ 16 := Nat.le_of_dvd (by norm_num) hd
  unfold Nat.ModEq at hm
  interval_cases c <;> omega

variable {X : Type*} [Group X]

@[expose] def litConjOn (W : Subgroup X) {n : X} (hn : ∀ x, x ∈ W ↔ n * x * n⁻¹ ∈ W) :
    Equiv.Perm {x // x ∈ W} where
  toFun w := ⟨n * w * n⁻¹, (hn w).mp w.2⟩
  invFun w := ⟨n⁻¹ * w * n, (hn _).mpr (by simpa [mul_assoc] using w.2)⟩
  left_inv w := by
    apply Subtype.ext
    group
  right_inv w := by
    apply Subtype.ext
    group

theorem litConjOn_apply (W : Subgroup X) {n : X} (hn : ∀ x, x ∈ W ↔ n * x * n⁻¹ ∈ W)
    (w : {x // x ∈ W}) : (litConjOn W hn w : X) = n * w * n⁻¹ := rfl

theorem litConjOn_pow (W : Subgroup X) {n : X} (hn : ∀ x, x ∈ W ↔ n * x * n⁻¹ ∈ W) (k : ℕ)
    (w : {x // x ∈ W}) : (((litConjOn W hn) ^ k) w : X) = n ^ k * w * (n ^ k)⁻¹ := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, litConjOn_apply, pow_succ]
    group

theorem litConjOn_pow_five (W : Subgroup X) {n : X} (hn : ∀ x, x ∈ W ↔ n * x * n⁻¹ ∈ W)
    (h5 : ∀ w ∈ W, n ^ 5 * w * (n ^ 5)⁻¹ = w) : litConjOn W hn ^ 5 = 1 := by
  ext ⟨w, hw⟩
  rw [litConjOn_pow, Equiv.Perm.coe_one, id_eq]
  exact h5 w hw

theorem litConjOn_fixed (W : Subgroup X) {n : X} (hn : ∀ x, x ∈ W ↔ n * x * n⁻¹ ∈ W)
    (w : {x // x ∈ W}) : litConjOn W hn w = w ↔ n * w * n⁻¹ = w := by
  rw [Subtype.ext_iff, litConjOn_apply]

theorem lit_card_modEq_one [Finite X] {W : Subgroup X} {n : X}
    (hn : ∀ x, x ∈ W ↔ n * x * n⁻¹ ∈ W) (h5 : ∀ w ∈ W, n ^ 5 * w * (n ^ 5)⁻¹ = w)
    (hfree : ∀ w ∈ W, n * w * n⁻¹ = w → w = 1) : Nat.card W ≡ 1 [MOD 5] := by
  have h := lit_card_modEq_fix (litConjOn W hn) (litConjOn_pow_five W hn h5)
  have h1 : Nat.card {a // litConjOn W hn a = a} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, (litConjOn_fixed W hn 1).mpr (by simp)⟩, fun y => ?_⟩
    obtain ⟨⟨y, hy⟩, hy'⟩ := y
    have := hfree y hy ((litConjOn_fixed W hn ⟨y, hy⟩).mp hy')
    subst this
    rfl
  rw [h1] at h
  exact h

theorem lit_free_of_five [Finite X] {A : Subgroup X} (hA : Nat.card A = 16) {n : X}
    (hn : ∀ x, x ∈ A ↔ n * x * n⁻¹ ∈ A) (h5 : ∀ a ∈ A, n ^ 5 * a * (n ^ 5)⁻¹ = a)
    (hnt : ¬ ∀ a ∈ A, n * a * n⁻¹ = a) : ∀ a ∈ A, n * a * n⁻¹ = a → a = 1 := by
  set F : Subgroup A := (centralizer ({n} : Set X)).subgroupOf A with hF
  have hmem : ∀ a : A, a ∈ F ↔ litConjOn A hn a = a := fun a => by
    rw [litConjOn_fixed, hF, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc n * (a : X) * n⁻¹ = (n * a) * n⁻¹ := rfl
        _ = (a * n) * n⁻¹ := by rw [h]
        _ = a := by group
    · intro h
      calc (a : X) * n = (n * a * n⁻¹) * n := by rw [h]
        _ = n * a := by group
  have hcard : Nat.card F ≡ 16 [MOD 5] := by
    have h := lit_card_modEq_fix (litConjOn A hn) (litConjOn_pow_five A hn h5)
    rw [hA] at h
    have e : Nat.card F = Nat.card {a // litConjOn A hn a = a} :=
      Nat.card_congr (Equiv.subtypeEquivRight hmem)
    rw [e]
    exact h.symm
  have hdvd : Nat.card F ∣ 16 := hA ▸ Subgroup.card_subgroup_dvd_card F
  have hF1 : Nat.card F = 1 := by
    rcases lit_one_or_sixteen hdvd (hcard.trans (by decide)) with h | h
    · exact h
    · exfalso
      apply hnt
      have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [h, hA])
      intro a ha
      have : (⟨a, ha⟩ : A) ∈ F := htop ▸ Subgroup.mem_top _
      exact (litConjOn_fixed A hn ⟨a, ha⟩).mp ((hmem _).mp this)
  have hbot : F = ⊥ := Subgroup.card_eq_one.mp hF1
  intro a ha han
  have : (⟨a, ha⟩ : A) ∈ F := (hmem _).mpr ((litConjOn_fixed A hn ⟨a, ha⟩).mpr han)
  rw [hbot, Subgroup.mem_bot] at this
  simpa using congrArg Subtype.val this

theorem lit_irreducible_of_five [Finite X] {A : Subgroup X} (hA : Nat.card A = 16) {n : X}
    (hn : ∀ x, x ∈ A ↔ n * x * n⁻¹ ∈ A) (h5 : ∀ a ∈ A, n ^ 5 * a * (n ^ 5)⁻¹ = a)
    (hnt : ¬ ∀ a ∈ A, n * a * n⁻¹ = a) {W : Subgroup X} (hWA : W ≤ A)
    (hW : ∀ x, x ∈ W ↔ n * x * n⁻¹ ∈ W) : W = ⊥ ∨ W = A := by
  have hfree := lit_free_of_five hA hn h5 hnt
  have hcard : Nat.card W ≡ 1 [MOD 5] :=
    lit_card_modEq_one hW (fun w hw => h5 w (hWA hw)) (fun w hw => hfree w (hWA hw))
  have hdvd : Nat.card W ∣ 16 := hA ▸ Subgroup.card_dvd_of_le hWA
  rcases lit_one_or_sixteen hdvd hcard with hc | hc
  · exact Or.inl (Subgroup.card_eq_one.mp hc)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hWA (by rw [hc, hA]))

theorem lit_exists_five {N : Type*} [Group N] (φ : N →* Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) : ∃ g : N, φ g ^ 5 = 1 ∧ φ g ≠ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := Equiv.Perm (Fin 6)) 5
    (by rw [Nat.card_perm, Nat.card_fin]; decide)
  obtain ⟨g, rfl⟩ := hφ σ
  refine ⟨g, by rw [← hσ]; exact pow_orderOf_eq_one _, ?_⟩
  intro h
  rw [h, orderOf_one] at hσ
  omega

theorem lit_irreducible [Finite X] {A N : Subgroup X} (hAN : N ≤ normalizer (A : Set X))
    (hA : Nat.card A = 16) (φ : N →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hker : ∀ g : N, φ g = 1 ↔ ∀ a ∈ A, (g : X) * a = a * g) {W : Subgroup X} (hWA : W ≤ A)
    (hW : N ≤ normalizer (W : Set X)) : W = ⊥ ∨ W = A := by
  obtain ⟨g, hg5, hg1⟩ := lit_exists_five φ hφ
  have hgA := Subgroup.mem_normalizer_iff.mp (hAN g.2)
  have hgW := Subgroup.mem_normalizer_iff.mp (hW g.2)
  refine lit_irreducible_of_five hA (n := (g : X)) hgA ?_ ?_ hWA hgW
  · intro a ha
    have h : φ (g ^ 5) = 1 := by rw [map_pow, hg5]
    have h2 := (hker (g ^ 5)).mp h a ha
    have : ((g : X)) ^ 5 * a = a * ((g : X)) ^ 5 := by simpa using h2
    rw [this]
    group
  · intro hcon
    refine hg1 ((hker g).mpr fun a ha => ?_)
    have := hcon a ha
    calc (g : X) * a = (g : X) * a * (g : X)⁻¹ * g := by group
      _ = a * g := by rw [this]

end CFSG.OddStandard.HigherRank.YamadaG23
