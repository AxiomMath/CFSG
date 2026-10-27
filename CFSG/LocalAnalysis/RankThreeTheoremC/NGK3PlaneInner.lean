module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P D : Subgroup X} {z : X}

omit [Finite X] in
private theorem inner_pow_conj_eq {a e w : X} (hw : Commute w a) (h : a * e * a⁻¹ = w * e)
    (n : ℕ) : a ^ n * e * (a ^ n)⁻¹ = w ^ n * e := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hwn : a * w ^ n = w ^ n * a := (hw.pow_left n).symm.eq
    calc a ^ (n + 1) * e * (a ^ (n + 1))⁻¹ = a * (a ^ n * e * (a ^ n)⁻¹) * a⁻¹ := by group
      _ = a * (w ^ n * e) * a⁻¹ := by rw [ih]
      _ = w ^ n * (a * e * a⁻¹) := by rw [← mul_assoc a, hwn]; group
      _ = w ^ (n + 1) * e := by rw [h, pow_succ, mul_assoc]

omit [Finite X] in
private theorem inner_conj_pair {a b ζ : X} (hab : a * b * a⁻¹ = ζ * b) (ha : Commute ζ a)
    (hb : Commute ζ b) (m n : ℕ) :
    (a ^ m * (b⁻¹) ^ n) * a * (a ^ m * (b⁻¹) ^ n)⁻¹ = ζ ^ n * a ∧
    (a ^ m * (b⁻¹) ^ n) * b * (a ^ m * (b⁻¹) ^ n)⁻¹ = ζ ^ m * b := by
  have h1 : a ^ m * b * (a ^ m)⁻¹ = ζ ^ m * b := inner_pow_conj_eq ha hab m
  have hba : b⁻¹ * a * (b⁻¹)⁻¹ = ζ * a := by
    have h' : a * b = ζ * b * a := by
      calc a * b = a * b * a⁻¹ * a := by group
        _ = ζ * b * a := by rw [hab]
    have hζb : b⁻¹ * ζ * b = ζ := by rw [mul_assoc, hb.eq, inv_mul_cancel_left]
    calc b⁻¹ * a * (b⁻¹)⁻¹ = b⁻¹ * (a * b) := by group
      _ = b⁻¹ * (ζ * b * a) := by rw [h']
      _ = (b⁻¹ * ζ * b) * a := by group
      _ = ζ * a := by rw [hζb]
  have h2 : (b⁻¹) ^ n * a * ((b⁻¹) ^ n)⁻¹ = ζ ^ n * a := inner_pow_conj_eq hb.inv_right hba n
  have h3 : a ^ m * a * (a ^ m)⁻¹ = a := by group
  have h4 : (b⁻¹) ^ n * b * ((b⁻¹) ^ n)⁻¹ = b := by group
  have hc : a ^ m * ζ ^ n = ζ ^ n * a ^ m := ((ha.pow_left n).pow_right m).symm.eq
  constructor
  · calc (a ^ m * (b⁻¹) ^ n) * a * (a ^ m * (b⁻¹) ^ n)⁻¹
        = a ^ m * ((b⁻¹) ^ n * a * ((b⁻¹) ^ n)⁻¹) * (a ^ m)⁻¹ := by group
      _ = a ^ m * (ζ ^ n * a) * (a ^ m)⁻¹ := by rw [h2]
      _ = (a ^ m * ζ ^ n) * a * (a ^ m)⁻¹ := by group
      _ = ζ ^ n * (a ^ m * a * (a ^ m)⁻¹) := by rw [hc]; group
      _ = ζ ^ n * a := by rw [h3]
  · calc (a ^ m * (b⁻¹) ^ n) * b * (a ^ m * (b⁻¹) ^ n)⁻¹
        = a ^ m * ((b⁻¹) ^ n * b * ((b⁻¹) ^ n)⁻¹) * (a ^ m)⁻¹ := by group
      _ = a ^ m * b * (a ^ m)⁻¹ := by rw [h4]
      _ = ζ ^ m * b := h1

private theorem inner_exists_closure_pair (hcard : Nat.card D = 3 ^ 3)
    (hnc : ¬ IsMulCommutative D) :
    ∃ d₁ ∈ D, ∃ d₂ ∈ D, d₁ * d₂ ≠ d₂ * d₁ ∧ closure ({d₁, d₂} : Set X) = D := by
  obtain ⟨d₁, hd₁, d₂, hd₂, hne⟩ : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hnc (IsMulCommutative.of_setLike_mul_comm hcon)
  refine ⟨d₁, hd₁, d₂, hd₂, hne, ?_⟩
  set C : Subgroup X := closure ({d₁, d₂} : Set X) with hC
  have hle : C ≤ D := by
    rw [hC, closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hd₁, hd₂⟩
  have hmem₁ : d₁ ∈ C := subset_closure (Set.mem_insert _ _)
  have hmem₂ : d₂ ∈ C := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hnc' : ¬ IsMulCommutative C := fun hCc => hne (setLike_mul_comm hmem₁ hmem₂)
  have hdvd : Nat.card C ∣ 3 ^ 3 := hcard ▸ card_dvd_of_le hle
  have hcyc : Nat.card C ∣ 3 → False := fun h3 =>
    hnc' (isCyclic_of_card_dvd_prime h3).isMulCommutative
  obtain ⟨m, hm, hCm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases m
  · exact (hcyc (by rw [hCm]; norm_num)).elim
  · exact (hcyc (by rw [hCm]; norm_num)).elim
  · exact (hnc' (IsPGroup.isMulCommutative_of_card_eq_prime_sq hCm)).elim
  · exact eq_of_le_of_card_ge hle (by rw [hcard, hCm])

theorem PlaneData.exists_inner (h : PlaneData P D z)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ zpowers z)
    (hcen : ∀ d ∈ D, (∀ e ∈ D, d * e = e * d) → d ∈ zpowers z) :
    ∀ x ∈ P, (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ zpowers z) →
      ∃ δ ∈ D, ∀ d ∈ D, δ⁻¹ * x * d = d * (δ⁻¹ * x) := by
  have _ := hcen
  intro x hxP hx
  have hDP : D ≤ P := h.plane.1
  have hZc : ∀ w ∈ zpowers z, ∀ g ∈ P, Commute w g := by
    intro w hw g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
    exact (show Commute z g from h.zc g hg).zpow_left n
  obtain ⟨d₁, hd₁, d₂, hd₂, hne, hgen⟩ := inner_exists_closure_pair h.card h.plane.2.1
  have hζZ : d₁ * d₂ * d₁⁻¹ * d₂⁻¹ ∈ zpowers z := hcomm d₁ hd₁ d₂ hd₂
  set ζ : X := d₁ * d₂ * d₁⁻¹ * d₂⁻¹
  have hζ1 : ζ ≠ 1 := fun h1 => hne (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1))
  have hζo : orderOf ζ = 3 := by
    have hdvd : orderOf ζ ∣ orderOf z := orderOf_dvd_of_mem_zpowers hζZ
    rw [h.zo] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.1 h1) hζ1
    · exact h3
  have hZζ : zpowers ζ = zpowers z :=
    eq_of_le_of_card_ge (zpowers_le.2 hζZ) (by rw [Nat.card_zpowers, Nat.card_zpowers, hζo, h.zo])
  have hk : ∀ d ∈ D, ∃ k : ℕ, x * d * x⁻¹ = ζ ^ k * d := by
    intro d hd
    have hmem := hx d hd
    rw [← hZζ, ← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, mul_inv_eq_iff_eq_mul.1 hk.symm⟩
  obtain ⟨k₁, hk₁⟩ := hk d₁ hd₁
  obtain ⟨k₂, hk₂⟩ := hk d₂ hd₂
  have hab : d₁ * d₂ * d₁⁻¹ = ζ * d₂ := mul_inv_eq_iff_eq_mul.1 rfl
  obtain ⟨hδ₁, hδ₂⟩ :=
    inner_conj_pair hab (hZc ζ hζZ d₁ (hDP hd₁)) (hZc ζ hζZ d₂ (hDP hd₂)) k₂ k₁
  set δ : X := d₁ ^ k₂ * (d₂⁻¹) ^ k₁
  have key : ∀ d : X, δ * d * δ⁻¹ = x * d * x⁻¹ → δ⁻¹ * x * d = d * (δ⁻¹ * x) := by
    intro d hd
    calc δ⁻¹ * x * d = δ⁻¹ * (x * d * x⁻¹) * x := by group
      _ = δ⁻¹ * (δ * d * δ⁻¹) * x := by rw [hd]
      _ = d * (δ⁻¹ * x) := by group
  have hle : D ≤ centralizer ({δ⁻¹ * x} : Set X) := by
    rw [← hgen, closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨mem_centralizer_singleton_iff.2 (key _ (hδ₁.trans hk₁.symm)).symm,
      mem_centralizer_singleton_iff.2 (key _ (hδ₂.trans hk₂.symm)).symm⟩
  exact ⟨δ, mul_mem (pow_mem hd₁ _) (pow_mem (inv_mem hd₂) _),
    fun d hd => (mem_centralizer_singleton_iff.1 (hle hd)).symm⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
