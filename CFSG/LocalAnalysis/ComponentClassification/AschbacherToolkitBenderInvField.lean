module

public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitaryCoord

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace InvField

variable {K : Type*} [Field K]

theorem exists_add_apply_eq_one [CharP K 2] (θ : K →+* K) (hθ : ∀ x, θ (θ x) = x) {e : K}
    (he : θ e ≠ e) : ∃ w : K, w + θ w = 1 := by
  have hd0 : e + θ e ≠ 0 := fun h => he (CharTwo.add_eq_zero.mp h).symm
  have hθd : θ (e + θ e) = e + θ e := by rw [map_add, hθ, add_comm]
  refine ⟨e / (e + θ e), ?_⟩
  rw [map_div₀, hθd, ← add_div, div_self hd0]

variable [Finite K]

theorem card_fix_sq [CharP K 2] (θ : K →+* K) (hθ : ∀ x, θ (θ x) = x) {e : K} (he : θ e ≠ e) :
    Nat.card {x : K // θ x = x} ^ 2 = Nat.card K := by
  obtain ⟨w, hw⟩ := exists_add_apply_eq_one θ hθ he
  have hθw : θ w = w + 1 := by linear_combination hw - CharTwo.add_self_eq_zero w
  have htr : ∀ x : K, θ (x + θ x) = x + θ x := fun x => by rw [map_add, hθ, add_comm]
  have hdec : ∀ x : K, θ (x + (x + θ x) * w) = x + (x + θ x) * w := fun x => by
    rw [map_add, map_mul, htr, hθw]
    linear_combination CharTwo.add_self_eq_zero (θ x)
  let f : {x : K // θ x = x} × {x : K // θ x = x} → K := fun p => (p.1 : K) + (p.2 : K) * w
  let g : K → {x : K // θ x = x} × {x : K // θ x = x} := fun x =>
    (⟨x + (x + θ x) * w, hdec x⟩, ⟨x + θ x, htr x⟩)
  have hf : Function.Injective f := by
    rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ h
    change s + t * w = s' + t' * w at h
    have h2 := congrArg θ h
    rw [map_add, map_add, map_mul, map_mul, hs, ht, hs', ht', hθw] at h2
    have htt : t = t' := by linear_combination h2 - h
    have hss : s = s' := by linear_combination h - w * htt
    subst htt
    subst hss
    rfl
  have hg : Function.Injective g := by
    intro x y h
    have h1 := congrArg (fun p => (p.1 : K)) h
    have h2 := congrArg (fun p => (p.2 : K)) h
    change x + (x + θ x) * w = y + (y + θ y) * w at h1
    change x + θ x = y + θ y at h2
    linear_combination h1 - w * h2
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod] at h1 h2
  rw [sq]
  exact le_antisymm h1 h2

theorem pow_card_fix (θ : K →+* K) {x : K} (hx : θ x = x) :
    x ^ Nat.card {y : K // θ y = y} = x := by
  let F : Subfield K :=
    { carrier := {y | θ y = y}
      mul_mem' := fun {a b} ha hb => by
        change θ (a * b) = a * b
        rw [map_mul, show θ a = a from ha, show θ b = b from hb]
      one_mem' := map_one θ
      add_mem' := fun {a b} ha hb => by
        change θ (a + b) = a + b
        rw [map_add, show θ a = a from ha, show θ b = b from hb]
      zero_mem' := map_zero θ
      neg_mem' := fun {a} ha => by
        change θ (-a) = -a
        rw [map_neg, show θ a = a from ha]
      inv_mem' := fun a ha => by
        change θ a⁻¹ = a⁻¹
        rw [map_inv₀, show θ a = a from ha] }
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card (⟨x, hx⟩ : F)
  have hcard : Fintype.card F = Nat.card {y : K // θ y = y} := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard] at h
  have h2 := congrArg (fun y : F => (y : K)) h
  simpa only [SubmonoidClass.coe_pow] using h2

omit [Finite K] in
theorem card_pow_eq_self_le {n : ℕ} (hn : 2 ≤ n) : Nat.card {x : K // x ^ n = x} ≤ n := by
  classical
  set Z := insert (0 : K) (Polynomial.nthRootsFinset (n - 1) (1 : K)) with hZ
  have hsub : {x : K | x ^ n = x} ⊆ (Z : Set K) := by
    intro x hx
    change x ^ n = x at hx
    rw [hZ, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      rw [Polynomial.mem_nthRootsFinset (by omega)]
      have e : x ^ n = x ^ (n - 1) * x := by
        rw [← pow_succ]
        congr 1
        omega
      rw [e] at hx
      exact mul_right_cancel₀ hx0 (hx.trans (one_mul x).symm)
  have hZcard : Z.card ≤ n := by
    calc Z.card ≤ (Polynomial.nthRootsFinset (n - 1) (1 : K)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (n - 1) + 1 := by
          gcongr
          rw [Polynomial.nthRootsFinset_def]
          exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
      _ = n := by omega
  calc Nat.card {x : K // x ^ n = x} = ({x : K | x ^ n = x} : Set K).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ (Z : Set K).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = Z.card := Set.ncard_coe_finset _
    _ ≤ n := hZcard

theorem apply_eq_self_of_involutive [CharP K 2] (σ : K ≃+* K) (θ : K →+* K) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // σ x = x} = q)
    (hθ : ∀ x, θ (θ x) = x) {t : K} (ht : σ t = t) : θ t = t := by
  by_cases hid : ∀ x, θ x = x
  · exact hid t
  push Not at hid
  obtain ⟨e, he⟩ := hid
  have h1 := card_fix_sq θ hθ he
  rw [hcard] at h1
  have hθcard : Nat.card {x : K // θ x = x} = q := Nat.pow_left_injective two_ne_zero h1
  have hsubθ : {x : K | θ x = x} ⊆ {x : K | x ^ q = x} := fun x hx => by
    have h2 := pow_card_fix θ hx
    rwa [hθcard] at h2
  have hsubσ : {x : K | σ x = x} ⊆ {x : K | x ^ q = x} := fun x hx => by
    have h2 := pow_card_fix σ.toRingHom (x := x) hx
    have e2 : Nat.card {y : K // σ.toRingHom y = y} = q := hfixed
    rwa [e2] at h2
  have hle : ({x : K | x ^ q = x} : Set K).ncard ≤ ({x : K | θ x = x} : Set K).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (card_pow_eq_self_le hq).trans hθcard.ge
  have heq := Set.eq_of_subset_of_ncard_le hsubθ hle (Set.toFinite _)
  have hmem : t ∈ {x : K | θ x = x} := by
    rw [heq]
    exact hsubσ ht
  exact hmem

theorem apply_eq_self_of_odd [CharP K 2] {n : ℕ} (hcard : Nat.card K = 2 ^ (2 * n + 1))
    (θ : K →+* K) (hθ : ∀ x, θ (θ x) = x) (x : K) : θ x = x := by
  by_contra hx
  have h1 := card_fix_sq θ hθ hx
  rw [hcard] at h1
  have hd : Nat.card {y : K // θ y = y} ∣ 2 ^ (2 * n + 1) :=
    ⟨Nat.card {y : K // θ y = y}, by rw [← h1, sq]⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rw [hj, ← pow_mul] at h1
  have h2 := Nat.pow_right_injective (le_refl 2) h1
  omega

end InvField

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
