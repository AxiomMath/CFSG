module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G Q : Type*} [Group G] [Group Q] {P : Subgroup G}

theorem mul_mul_mul_mul_eq_one {M : Type*} [Group M] {a b : M} (ha : a * a = 1)
    (hb : b * b = 1) : a * b * a * b * (b * a * b * a) = 1 := by
  have ha' : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ x, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  simp only [mul_assoc, ha', hb', ha]

theorem commutatorSq_mul_self_eq_one {M : Type*} [Group M] {a b : M} (ha : a * a = 1)
    (hb : b * b = 1) (hz : a * b * a * b * b = b * (a * b * a * b)) :
    a * b * a * b * (a * b * a * b) = 1 := by
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have h1 : b * a * b * a = a * b * a * b := by
    calc b * a * b * a = b * (a * b * a * b) * b⁻¹ := by
          rw [hbi]
          simp only [mul_assoc]
          rw [hb, mul_one]
      _ = a * b * a * b := by rw [← hz, mul_assoc, mul_inv_cancel, mul_one]
  calc a * b * a * b * (a * b * a * b) = a * b * a * b * (b * a * b * a) := by rw [h1]
    _ = 1 := mul_mul_mul_mul_eq_one ha hb

@[expose] def involutionsOver (p : P →* Q) (U : Subgroup Q)
    (hc : ∀ y : P, p y = 1 → ∀ y' : P, y * y' = y' * y)
    (hodd : ∀ y : P, p y = 1 → y * y = 1 → y = 1) (hU2 : ∀ u ∈ U, u * u = 1) : Subgroup G where
  carrier := {y | ∃ hy : y ∈ P, p ⟨y, hy⟩ ∈ U ∧ y * y = 1}
  mul_mem' := by
    rintro a b ⟨ha, hpa, haa⟩ ⟨hb, hpb, hbb⟩
    refine ⟨mul_mem ha hb, ?_, ?_⟩
    · have h : (⟨a * b, mul_mem ha hb⟩ : P) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [h, map_mul]
      exact mul_mem hpa hpb
    · set A : P := ⟨a, ha⟩
      set B : P := ⟨b, hb⟩
      have hA : A * A = 1 := Subtype.ext haa
      have hB : B * B = 1 := Subtype.ext hbb
      have hpz : p (A * B * A * B) = 1 := by
        have h := hU2 _ (mul_mem hpa hpb)
        rw [map_mul, map_mul, map_mul]
        rw [← mul_assoc] at h
        exact h
      have hz := hc _ hpz B
      have hzz := commutatorSq_mul_self_eq_one hA hB hz
      have h1 : A * B * A * B = 1 := hodd _ hpz hzz
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_one] at h2
      calc a * b * (a * b) = a * b * a * b := by rw [← mul_assoc]
        _ = 1 := h2
  one_mem' := ⟨one_mem P, by
    have h : (⟨1, one_mem P⟩ : P) = 1 := rfl
    rw [h, map_one]
    exact one_mem U, mul_one 1⟩
  inv_mem' := by
    rintro y ⟨hy, hpy, hyy⟩
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left hyy
    rw [hyi]
    exact ⟨hy, hpy, hyy⟩

variable {p : P →* Q} {U : Subgroup Q} {hc : ∀ y : P, p y = 1 → ∀ y' : P, y * y' = y' * y}
  {hodd : ∀ y : P, p y = 1 → y * y = 1 → y = 1} {hU2 : ∀ u ∈ U, u * u = 1}

theorem isPGroup_involutionsOver : IsPGroup 2 (involutionsOver p U hc hodd hU2) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
  exact g.2.2.2

theorem exists_mem_involutionsOver_of_surjective [Finite P] (hp : Function.Surjective p)
    (hk : Odd (Nat.card p.ker)) {u : Q} (hu : u ∈ U) :
    ∃ y ∈ involutionsOver p U hc hodd hU2, ∃ hy : y ∈ P, p ⟨y, hy⟩ = u := by
  obtain ⟨y₀, rfl⟩ := hp u
  obtain ⟨m, hm⟩ := hk
  set y : P := y₀ ^ Nat.card p.ker with hydef
  have hpy : p y = p y₀ := by
    rw [hydef, map_pow, hm, pow_succ, pow_mul, sq, hU2 _ hu, one_pow, one_mul]
  have hker : y₀ * y₀ ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact hU2 _ hu
  have hyy : y * y = 1 := by
    have h := pow_card_eq_one' (x := (⟨y₀ * y₀, hker⟩ : p.ker))
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h'
    rw [hydef, ← pow_add, ← two_mul, pow_mul, sq]
    exact h'
  refine ⟨(y : G), ⟨y.2, ?_, congrArg Subtype.val hyy⟩, y.2, ?_⟩
  · rw [Subtype.coe_eta, hpy]
    exact hu
  · rw [Subtype.coe_eta, hpy]

theorem involutionsOver_le_normalizer {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1)
    (hpW : ∀ y ∈ involutionsOver p U hc hodd hU2, ∀ w ∈ W,
      ∃ w' ∈ W, ∃ (hw' : w' ∈ P) (hyw : y * w * y⁻¹ ∈ P), p ⟨y * w * y⁻¹, hyw⟩ = p ⟨w', hw'⟩) :
    involutionsOver p U hc hodd hU2 ≤ normalizer (W : Set G) := by
  have key : ∀ y ∈ involutionsOver p U hc hodd hU2, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro y hy w hw
    obtain ⟨w', hw'W, hw'P, hywP, hpeq⟩ := hpW y hy w hw
    obtain ⟨k, hkdef⟩ : ∃ k : P, k = (⟨w', hw'P⟩ : P)⁻¹ * ⟨y * w * y⁻¹, hywP⟩ := ⟨_, rfl⟩
    have hpk : p k = 1 := by rw [hkdef, map_mul, map_inv, hpeq, inv_mul_cancel]
    have hkc := hc k hpk
    have hyy : y * y = 1 := hy.2.2
    have hsq : (⟨y * w * y⁻¹, hywP⟩ : P) * ⟨y * w * y⁻¹, hywP⟩ = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_one]
      calc y * w * y⁻¹ * (y * w * y⁻¹) = y * (w * w) * y⁻¹ := by group
        _ = 1 := by rw [hW2 w hw, mul_one, mul_inv_cancel]
    have hw'w' : (⟨w', hw'P⟩ : P) * ⟨w', hw'P⟩ = 1 := Subtype.ext (hW2 w' hw'W)
    have e1 : (⟨y * w * y⁻¹, hywP⟩ : P) = ⟨w', hw'P⟩ * k := by rw [hkdef, mul_inv_cancel_left]
    have hkk : k * k = 1 := by
      calc k * k = (⟨w', hw'P⟩ * ⟨w', hw'P⟩) * (k * k) := by rw [hw'w', one_mul]
        _ = ⟨w', hw'P⟩ * ((⟨w', hw'P⟩ : P) * k) * k := by simp only [mul_assoc]
        _ = ⟨w', hw'P⟩ * (k * ⟨w', hw'P⟩) * k := by rw [hkc ⟨w', hw'P⟩]
        _ = ⟨w', hw'P⟩ * k * (⟨w', hw'P⟩ * k) := by simp only [mul_assoc]
        _ = (⟨y * w * y⁻¹, hywP⟩ : P) * ⟨y * w * y⁻¹, hywP⟩ := by rw [e1]
        _ = 1 := hsq
    have hk1 : k = 1 := hodd k hpk hkk
    have e2 : (⟨y * w * y⁻¹, hywP⟩ : P) = ⟨w', hw'P⟩ := by
      rw [e1, hk1, mul_one]
    have e3 := congrArg Subtype.val e2
    simp only at e3
    rw [e3]
    exact hw'W
  intro y hy
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key y hy w, fun hw => ?_⟩
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy.2.2
  have h := key y hy _ hw
  rwa [hyi, show y * (y * w * y) * y = (y * y) * w * (y * y) by group, hy.2.2, one_mul,
    mul_one] at h

theorem mem_normalizer_involutionsOver {t : G} (ht : t * t = 1)
    (htP : t ∈ normalizer (P : Set G)) {θ : Q →* Q} (hθU : ∀ u ∈ U, θ u ∈ U)
    (hpt : ∀ (y : G) (hy : y ∈ P), p ⟨t * y * t⁻¹, (mem_normalizer_iff.1 htP y).1 hy⟩ =
      θ (p ⟨y, hy⟩)) :
    t ∈ normalizer (involutionsOver p U hc hodd hU2 : Set G) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have key : ∀ y ∈ involutionsOver p U hc hodd hU2,
      t * y * t⁻¹ ∈ involutionsOver p U hc hodd hU2 := by
    rintro y ⟨hy, hpy, hyy⟩
    refine ⟨(mem_normalizer_iff.1 htP y).1 hy, ?_, ?_⟩
    · rw [hpt y hy]
      exact hθU _ hpy
    · calc t * y * t⁻¹ * (t * y * t⁻¹) = t * (y * y) * t⁻¹ := by group
        _ = 1 := by rw [hyy, mul_one, mul_inv_cancel]
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key y, fun hy => ?_⟩
  have h := key _ hy
  rwa [hti, show t * (t * y * t) * t = (t * t) * y * (t * t) by group, ht, one_mul,
    mul_one] at h

theorem eq_one_of_mem_involutionsOver_of_commute {v : G} (hv : v ∈ P)
    (hU : ∀ u ∈ U, u * p ⟨v, hv⟩ = p ⟨v, hv⟩ * u → u = 1) {y : G}
    (hy : y ∈ involutionsOver p U hc hodd hU2) (hyv : y * v = v * y) : y = 1 := by
  obtain ⟨hyP, hpy, hyy⟩ := hy
  have hcomm : (⟨y, hyP⟩ : P) * ⟨v, hv⟩ = ⟨v, hv⟩ * ⟨y, hyP⟩ := Subtype.ext hyv
  have hp1 : p ⟨y, hyP⟩ = 1 := hU _ hpy (by rw [← map_mul, ← map_mul, hcomm])
  have h1 := hodd ⟨y, hyP⟩ hp1 (Subtype.ext hyy)
  exact congrArg Subtype.val h1

end CFSG.SeitzReduction.LinearPilot
