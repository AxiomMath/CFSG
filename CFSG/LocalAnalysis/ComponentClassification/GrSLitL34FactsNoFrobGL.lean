module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open Subgroup

variable {X : Type*} [Group X]

theorem false_of_index_two {V W : Subgroup X} (hWV : W ≤ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1)
    (hV8 : Nat.card V = 8) (hW4 : Nat.card W = 4) {ρ : X}
    (hρV : ρ ∈ normalizer (V : Set X)) (hρW : ρ ∈ normalizer (W : Set X))
    (hfix : ∀ v ∈ V, ρ * v = v * ρ → v = 1) : False := by
  have hcV : ∀ v ∈ V, ρ * v * ρ⁻¹ ∈ V := fun v hv => (mem_normalizer_iff.mp hρV v).mp hv
  have hinj : ∀ a ∈ V, ∀ b ∈ V, a * (ρ * a * ρ⁻¹) = b * (ρ * b * ρ⁻¹) → a = b := by
    intro a ha b hb h
    have hA := hcV a ha
    have hB := hcV b hb
    have e1 : b * a = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) := by
      calc b * a = b * a * (ρ * a * ρ⁻¹ * (ρ * a * ρ⁻¹)) := by rw [hV2 _ hA, mul_one]
        _ = b * (a * (ρ * a * ρ⁻¹)) * (ρ * a * ρ⁻¹) := by group
        _ = b * (b * (ρ * b * ρ⁻¹)) * (ρ * a * ρ⁻¹) := by rw [h]
        _ = b * b * (ρ * b * ρ⁻¹) * (ρ * a * ρ⁻¹) := by group
        _ = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) := by rw [hV2 _ hb, one_mul]
    have e2 : ρ * (a * b) * ρ⁻¹ = a * b := by
      calc ρ * (a * b) * ρ⁻¹ = ρ * a * ρ⁻¹ * (ρ * b * ρ⁻¹) := by group
        _ = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) := hVc _ hA _ hB
        _ = b * a := e1.symm
        _ = a * b := hVc _ hb _ ha
    have hab : a * b = 1 := hfix _ (V.mul_mem ha hb) (by
      calc ρ * (a * b) = ρ * (a * b) * ρ⁻¹ * ρ := by group
        _ = a * b * ρ := by rw [e2])
    calc a = a * (b * b) := by rw [hV2 _ hb, mul_one]
      _ = a * b * b := by group
      _ = b := by rw [hab, one_mul]
  have hW : Finite W := Nat.finite_of_card_ne_zero (by rw [hW4]; norm_num)
  let f : W → W := fun e =>
    ⟨e * (ρ * e * ρ⁻¹), W.mul_mem e.2 ((mem_normalizer_iff.mp hρW e).mp e.2)⟩
  have hf : Function.Injective f := fun e₁ e₂ h =>
    Subtype.ext (hinj _ (hWV e₁.2) _ (hWV e₂.2) (congrArg Subtype.val h))
  have hfs := Finite.injective_iff_surjective.mp hf
  obtain ⟨u, huV, huW⟩ : ∃ u ∈ V, u ∉ W := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show V ≤ W from hcon)
    omega
  have hu' : ρ * u * ρ⁻¹ ∉ W := fun h => huW ((mem_normalizer_iff.mp hρW u).mpr h)
  have hidx : (W.subgroupOf V).index = 2 := by
    have h := Subgroup.card_mul_index (W.subgroupOf V)
    rw [Nat.card_congr (subgroupOfEquivOfLe hWV).toEquiv, hW4, hV8] at h
    omega
  have hd : u * (ρ * u * ρ⁻¹) ∈ W := by
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨u, huV⟩)
      (b := ⟨ρ * u * ρ⁻¹, hcV u huV⟩)).2
      (iff_of_false (by rwa [mem_subgroupOf]) (by rwa [mem_subgroupOf]))
    rwa [mem_subgroupOf] at h
  obtain ⟨e, he⟩ := hfs ⟨_, hd⟩
  have heu := hinj e (hWV e.2) u huV (congrArg Subtype.val he)
  exact huW (heu ▸ e.2)

theorem centralizes_or_fpf {V : Subgroup X} (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hV2 : ∀ a ∈ V, a * a = 1) (hV8 : Nat.card V = 8) {ρ : X}
    (hρ : ρ ∈ normalizer (V : Set X)) (hfix : ∀ v ∈ V, ρ * v = v * ρ → v = 1) {τ : X}
    (hτρ : τ * ρ = ρ * τ) :
    τ ∈ centralizer (V : Set X) ∨ ∀ v ∈ V, τ * v = v * τ → v = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hτC, w, hwV, hwτ, hw1⟩ := hcon
  have hτρ' : ρ⁻¹ * τ = τ * ρ⁻¹ := by
    calc ρ⁻¹ * τ = ρ⁻¹ * (τ * ρ) * ρ⁻¹ := by group
      _ = ρ⁻¹ * (ρ * τ) * ρ⁻¹ := by rw [hτρ]
      _ = τ * ρ⁻¹ := by group
  set W := V ⊓ centralizer ({τ} : Set X) with hWdef
  have hWV : W ≤ V := inf_le_left
  have hmemW : ∀ x, x ∈ W ↔ x ∈ V ∧ τ * x = x * τ := fun x => by
    rw [hWdef, mem_inf, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => eq_comm
  have hρW : ρ ∈ normalizer (W : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    rw [hmemW, hmemW, ← mem_normalizer_iff.mp hρ x]
    refine and_congr_right fun _ => ?_
    have h1 : τ * (ρ * x * ρ⁻¹) = ρ * (τ * x) * ρ⁻¹ := by
      calc τ * (ρ * x * ρ⁻¹) = τ * ρ * x * ρ⁻¹ := by group
        _ = ρ * τ * x * ρ⁻¹ := by rw [hτρ]
        _ = ρ * (τ * x) * ρ⁻¹ := by group
    have h2 : ρ * x * ρ⁻¹ * τ = ρ * (x * τ) * ρ⁻¹ := by
      calc ρ * x * ρ⁻¹ * τ = ρ * x * (ρ⁻¹ * τ) := by group
        _ = ρ * x * (τ * ρ⁻¹) := by rw [hτρ']
        _ = ρ * (x * τ) * ρ⁻¹ := by group
    rw [h1, h2]
    constructor
    · intro h
      rw [h]
    · intro h
      have := congrArg (fun y => ρ⁻¹ * y * ρ) h
      simpa [mul_assoc] using this
  have hwW : w ∈ W := (hmemW w).2 ⟨hwV, hwτ⟩
  have hdvd : Nat.card W ∣ 2 ^ 3 := by
    have := Subgroup.card_dvd_of_le hWV
    rwa [hV8] at this
  obtain ⟨i, hi, hWi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases i
  ·
    rw [pow_zero, Subgroup.card_eq_one] at hWi
    rw [hWi] at hwW
    exact hw1 ((mem_bot).mp hwW)
  ·
    rw [pow_one] at hWi
    have hρw : ρ * w * ρ⁻¹ ∈ W := (mem_normalizer_iff.mp hρW w).mp hwW
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : W)).1 hWi
    have h1 := hy ⟨w, hwW⟩ (fun h => hw1 (congrArg Subtype.val h))
    have h2 := hy ⟨ρ * w * ρ⁻¹, hρw⟩ (fun h => by
      have h' : ρ * w * ρ⁻¹ = 1 := congrArg Subtype.val h
      apply hw1
      calc w = ρ⁻¹ * (ρ * w * ρ⁻¹) * ρ := by group
        _ = 1 := by rw [h']; group)
    have h3 : ρ * w * ρ⁻¹ = w := congrArg Subtype.val (h2.trans h1.symm)
    exact hw1 (hfix w hwV (by
      calc ρ * w = ρ * w * ρ⁻¹ * ρ := by group
        _ = w * ρ := by rw [h3]))
  ·
    exact false_of_index_two hWV hVc hV2 hV8 hWi hρ hρW hfix
  ·
    apply hτC
    have hV : Finite V := Nat.finite_of_card_ne_zero (by rw [hV8]; norm_num)
    have hWeq : W = V := Subgroup.eq_of_le_of_card_ge hWV (by rw [hV8, hWi]; norm_num)
    rw [mem_centralizer_iff]
    intro v hv
    rw [← hWeq] at hv
    exact ((hmemW v).1 hv).2.symm

theorem card_modEq_one_of_fpf {V : Subgroup X} [Finite V] {τ : X}
    (hτ : τ ∈ normalizer (V : Set X)) {p : ℕ} [Fact p.Prime]
    (hτp : τ ^ p ∈ centralizer (V : Set X)) (hfix : ∀ v ∈ V, τ * v = v * τ → v = 1) :
    Nat.card V ≡ 1 [MOD p] := by
  classical
  have hc : ∀ v ∈ V, τ * v * τ⁻¹ ∈ V := fun v hv => (mem_normalizer_iff.mp hτ v).mp hv
  let F : Function.End V := fun v => ⟨τ * v * τ⁻¹, hc v v.2⟩
  have hFn : ∀ (n : ℕ) (v : V), (((F ^ n : Function.End V) v : V) : X) = τ ^ n * v * (τ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro v
      rw [pow_zero, pow_zero, inv_one, mul_one, one_mul]
      rfl
    | succ n ih =>
      intro v
      rw [pow_succ]
      show ((F ^ n : Function.End V) (F v) : X) = _
      rw [ih]
      show τ ^ n * (τ * (v : X) * τ⁻¹) * (τ ^ n)⁻¹ = τ ^ (n + 1) * v * (τ ^ (n + 1))⁻¹
      group
  have hF1 : F ^ p ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    rw [pow_one, hFn p v]
    have h := mem_centralizer_iff.mp hτp v v.2
    calc τ ^ p * (v : X) * (τ ^ p)⁻¹ = v * τ ^ p * (τ ^ p)⁻¹ := by rw [h]
      _ = v := by group
  have : Fintype V := Fintype.ofFinite V
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := p) (n := 1) hF1
  have hfp : Fintype.card (Function.fixedPoints F) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (by simp [F])⟩, fun x => ?_⟩
    obtain ⟨v, hv⟩ := x
    apply Subtype.ext
    apply Subtype.ext
    have h1 : τ * (v : X) * τ⁻¹ = v := congrArg Subtype.val hv
    refine hfix v v.2 ?_
    calc τ * (v : X) = τ * v * τ⁻¹ * τ := by group
      _ = v * τ := by rw [h1]
  rw [hfp, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

theorem seven_dvd_orderOf_of_fpf [Finite X] {V : Subgroup X}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1)
    (hV8 : Nat.card V = 8) {ρ : X} (hρ : ρ ∈ normalizer (V : Set X))
    (hfix : ∀ v ∈ V, ρ * v = v * ρ → v = 1) : 7 ∣ orderOf ρ := by
  classical
  have hex : ∃ k, 0 < k ∧ ρ ^ k ∈ centralizer (V : Set X) :=
    ⟨orderOf ρ, orderOf_pos ρ, by rw [pow_orderOf_eq_one]; exact one_mem _⟩
  obtain ⟨hc0, hcC⟩ := Nat.find_spec hex
  have hmin : ∀ k, 0 < k → k < Nat.find hex → ρ ^ k ∉ centralizer (V : Set X) :=
    fun k hk hkc hC => Nat.find_min hex hkc ⟨hk, hC⟩
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra h
    push Not at h
    have hV : V = ⊥ := eq_bot_iff.mpr fun v hv => (mem_bot).mpr (h v hv)
    rw [hV, Subgroup.card_bot] at hV8
    norm_num at hV8
  have hc1 : Nat.find hex ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hcC
    exact hv₀1 (hfix v₀ hv₀ (mem_centralizer_iff.mp hcC v₀ hv₀).symm)
  have hp : (Nat.find hex).minFac.Prime := Nat.minFac_prime hc1
  have : Fact (Nat.find hex).minFac.Prime := ⟨hp⟩
  have hpc : (Nat.find hex).minFac ∣ Nat.find hex := Nat.minFac_dvd _
  have hcp : Nat.find hex / (Nat.find hex).minFac < Nat.find hex := Nat.div_lt_self hc0 hp.one_lt
  have hcp0 : 0 < Nat.find hex / (Nat.find hex).minFac :=
    Nat.div_pos (Nat.le_of_dvd hc0 hpc) hp.pos
  have hτC := hmin _ hcp0 hcp
  have hτp : (ρ ^ (Nat.find hex / (Nat.find hex).minFac)) ^ (Nat.find hex).minFac ∈
      centralizer (V : Set X) := by
    rw [← pow_mul, Nat.div_mul_cancel hpc]
    exact hcC
  have hτfix := (centralizes_or_fpf hVc hV2 hV8 hρ hfix (pow_mul_comm' ρ _)).resolve_left hτC
  have hmod := card_modEq_one_of_fpf ((normalizer _).pow_mem hρ _) hτp hτfix
  rw [hV8] at hmod
  have hp7 : (Nat.find hex).minFac = 7 :=
    (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp ((Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm)
  have hcn : Nat.find hex ∣ orderOf ρ := by
    have hr : ρ ^ (orderOf ρ % Nat.find hex) ∈ centralizer (V : Set X) := by
      have h1 : ρ ^ (orderOf ρ % Nat.find hex) =
          ((ρ ^ Nat.find hex) ^ (orderOf ρ / Nat.find hex))⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_mul, ← pow_add, Nat.mod_add_div, pow_orderOf_eq_one]
      rw [h1]
      exact inv_mem (pow_mem hcC _)
    by_contra hnd
    exact hmin _ (Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h))
      (Nat.mod_lt _ hc0) hr
  rw [← hp7]
  exact hpc.trans hcn

end CFSG.ComponentClassification.GrSLit.L34Facts
