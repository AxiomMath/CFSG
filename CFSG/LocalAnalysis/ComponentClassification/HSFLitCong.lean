module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.ComponentClassification.HSFLit

open Equiv

theorem four_dvd_card_sub_fixedPoints {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h2 : σ ^ 2 = 1) (hs : Equiv.Perm.sign σ = 1) :
    4 ∣ Fintype.card α - Fintype.card (Function.fixedPoints σ) := by
  rw [Equiv.Perm.card_fixedPoints, Nat.sub_sub_self σ.sum_cycleType_le]
  by_cases h1 : σ = 1
  · rw [h1, Equiv.Perm.cycleType_one, Multiset.sum_zero]
    exact dvd_zero 4
  have ho : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
    rw [hn, Multiset.card_replicate]
  have hsign := Equiv.Perm.sign_of_cycleType_eq_replicate (by norm_num : 0 < 2) hrep
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide)), hs, Equiv.Perm.card_fixedPoints,
    Nat.sub_sub_self σ.sum_cycleType_le, hn, Multiset.sum_replicate, smul_eq_mul,
    Nat.mul_div_cancel _ (by norm_num : 0 < 2)] at hsign
  have heven : Even (n + 1) := (neg_one_pow_eq_one_iff_even (by decide)).mp hsign.symm
  rw [hn, Multiset.sum_replicate, smul_eq_mul]
  obtain ⟨m, hm⟩ := heven
  exact ⟨m, by omega⟩

theorem eq_one_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (φ : X →* ℤˣ) : φ = 1 := by
  rcases (φ.normal_ker).eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
    apply hinj
    rw [map_mul, map_mul, mul_comm]
  · ext g
    have : g ∈ φ.ker := h ▸ Subgroup.mem_top g
    simpa using this

theorem card_conj_modEq_card_conj_centralizer {X : Type*} [Group X] [Finite X]
    (hsign : ∀ φ : X →* ℤˣ, φ = 1) {t : X} (ht2 : t ^ 2 = 1) (i : X) :
    {a | IsConj i a ∧ t * a = a * t}.ncard ≡ {a | IsConj i a}.ncard [MOD 4] := by
  classical
  have : Fintype X := Fintype.ofFinite X
  set Ω : Set X := {a | IsConj i a} with hΩ
  have hmem : ∀ (g : X) (a : Ω), g * (a : X) * g⁻¹ ∈ Ω := fun g a =>
    (show IsConj i (a : X) from a.2).trans (isConj_iff.mpr ⟨g, rfl⟩)
  let σ : X → Perm Ω := fun g =>
    { toFun := fun a => ⟨g * a * g⁻¹, hmem g a⟩
      invFun := fun a => ⟨g⁻¹ * a * g, by simpa using hmem g⁻¹ a⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }
  let ρ : X →* Perm Ω :=
    { toFun := σ
      map_one' := by ext a; simp [σ]
      map_mul' := fun g h => by ext a; simp [σ, Perm.mul_apply, mul_assoc] }
  have hs : Equiv.Perm.sign (ρ t) = 1 := by
    have := hsign (Equiv.Perm.sign.comp ρ)
    simpa using congrArg (fun φ : X →* ℤˣ => φ t) this
  have h2 : ρ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have h4 := four_dvd_card_sub_fixedPoints h2 hs
  have hfix : Fintype.card (Function.fixedPoints (ρ t)) =
      {a | IsConj i a ∧ t * a = a * t}.ncard := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    refine Nat.card_congr
      { toFun := fun a => ⟨(a : Ω), (a : Ω).2, ?_⟩
        invFun := fun a => ⟨⟨a, a.2.1⟩, ?_⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
    · have h := congrArg Subtype.val (show ρ t (a : Ω) = a from a.2)
      change t * (a : X) * t⁻¹ = a at h
      calc t * (a : X) = t * a * t⁻¹ * t := by group
        _ = a * t := by rw [h]
    · apply Subtype.ext
      change t * (a : X) * t⁻¹ = a
      rw [a.2.2]
      group
  have hΩc : Fintype.card Ω = Ω.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [← hfix, ← hΩc]
  have hle : Fintype.card (Function.fixedPoints (ρ t)) ≤ Fintype.card Ω :=
    Fintype.card_subtype_le _
  exact (Nat.modEq_iff_dvd' hle).mpr h4

theorem card_modEq_card_fixedPoints_sq {α : Type*} [Fintype α] [DecidableEq α] (π : Perm α)
    (h4 : π ^ 4 = 1) :
    Fintype.card (Function.fixedPoints ⇑(π ^ 2)) ≡ Fintype.card α [MOD 4] := by
  have hsq : ∀ a, (π ^ 2) a = π (π a) := fun a => by rw [pow_two, Perm.mul_apply]
  have h4' : ∀ a, π (π (π (π a))) = a := fun a => by
    have : (π ^ 4) a = a := by rw [h4]; rfl
    rwa [show (4 : ℕ) = 2 + 2 by rfl, pow_add, Perm.mul_apply, hsq, hsq] at this
  set M : Finset α := Finset.univ.filter fun a => (π ^ 2) a ≠ a with hM
  have hmemM : ∀ a, a ∈ M ↔ π (π a) ≠ a := fun a => by
    simp only [hM, Finset.mem_filter, Finset.mem_univ, true_and, hsq]
  have hMinv : ∀ a ∈ M, π a ∈ M := by
    intro a ha
    rw [hmemM] at ha ⊢
    exact fun h => ha (π.injective h)
  have key : ∀ s : Finset α, s ⊆ M → (∀ a ∈ s, π a ∈ s) → 4 ∣ s.card := by
    intro s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro hsM hsinv
      rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
      · simp
      have haM := (hmemM a).mp (hsM ha)
      have hs1 : π a ∈ s := hsinv a ha
      have hs2 : π (π a) ∈ s := hsinv _ hs1
      have hs3 : π (π (π a)) ∈ s := hsinv _ hs2
      have h01 : a ≠ π a := by
        intro h
        apply haM
        rw [← h, ← h]
      have h02 : a ≠ π (π a) := fun h => haM h.symm
      have h03 : a ≠ π (π (π a)) := by
        intro h
        apply h01
        calc a = π (π (π (π a))) := (h4' a).symm
          _ = π a := by rw [← h]
      have h12 : π a ≠ π (π a) := fun h => h01 (π.injective h)
      have h13 : π a ≠ π (π (π a)) := fun h => h02 (π.injective h)
      have h23 : π (π a) ≠ π (π (π a)) := fun h => h01 (π.injective (π.injective h))
      set o : Finset α := {a, π a, π (π a), π (π (π a))} with ho
      have hos : o ⊆ s := by
        intro b hb
        simp only [ho, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hocard : o.card = 4 := by
        rw [ho, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simpa using h23
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h12, h13⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h01, h02, h03⟩
      have hss : s \ o ⊂ s := Finset.sdiff_ssubset hos ⟨a, by simp [ho]⟩
      have hinv' : ∀ b ∈ s \ o, π b ∈ s \ o := by
        intro b hb
        rw [Finset.mem_sdiff] at hb ⊢
        refine ⟨hsinv b hb.1, fun hbo => hb.2 ?_⟩
        simp only [ho, Finset.mem_insert, Finset.mem_singleton] at hbo ⊢
        rcases hbo with h | h | h | h
        · right; right; right
          calc b = π (π (π (π b))) := (h4' b).symm
            _ = π (π (π a)) := by rw [h]
        · left
          exact π.injective h
        · right; left
          exact π.injective h
        · right; right; left
          exact π.injective h
      have h1 := ih (s \ o) hss ((Finset.sdiff_subset).trans hsM) hinv'
      have h2 : (s \ o).card + o.card = s.card := Finset.card_sdiff_add_card_eq_card hos
      rw [hocard] at h2
      omega
  have hMc := key M le_rfl hMinv
  have hsplit : Fintype.card (Function.fixedPoints ⇑(π ^ 2)) + M.card = Fintype.card α := by
    rw [hM, Fintype.card_subtype, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hle : Fintype.card (Function.fixedPoints ⇑(π ^ 2)) ≤ Fintype.card α := by omega
  refine (Nat.modEq_iff_dvd' hle).mpr ?_
  rw [← hsplit, Nat.add_sub_cancel_left]
  exact hMc

end CFSG.ComponentClassification.HSFLit
