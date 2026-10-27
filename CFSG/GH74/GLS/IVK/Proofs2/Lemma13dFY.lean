module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma13dFY

theorem exists_pow_eq_mul_pow {A : Type*} [Group A] {Y X : Subgroup A}
    (hXnorm : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X) {x σ : A} (hx : x ∈ X) (hσ : σ ∈ Y) (m : ℕ) :
    ∃ x' ∈ X, (x * σ) ^ m = x' * σ ^ m := by
  induction m with
  | zero => exact ⟨1, X.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨x', hx', h⟩ := ih
    refine ⟨x * (σ * x' * σ⁻¹), X.mul_mem hx (hXnorm σ hσ x' hx'), ?_⟩
    rw [pow_succ', h]
    group

theorem commute_of_mem_map_fitting {A : Type*} [Group A] [Finite A] (Y : Subgroup A) {a b : A}
    (ha : a ∈ (CFSG.fittingSubgroup ↥Y).map Y.subtype)
    (hb : b ∈ (CFSG.fittingSubgroup ↥Y).map Y.subtype)
    (hab : (orderOf a).Coprime (orderOf b)) : Commute a b := by
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
  have hord : ∀ c : ↥Y, ∀ hc : c ∈ CFSG.fittingSubgroup ↥Y,
      orderOf (⟨c, hc⟩ : ↥(CFSG.fittingSubgroup ↥Y)) = orderOf (Y.subtype c) := by
    intro c hc
    rw [Subgroup.orderOf_mk, Subgroup.coe_subtype, Subgroup.orderOf_coe]
  have key := Group.IsNilpotent.commute_of_orderOf_coprime (G := ↥(CFSG.fittingSubgroup ↥Y))
    (x := ⟨a', ha'⟩) (y := ⟨b', hb'⟩) (by rw [hord, hord]; exact hab)
  exact congrArg (fun z : ↥(CFSG.fittingSubgroup ↥Y) => Y.subtype (z : ↥Y)) key.eq

theorem exists_prime_power_part {A : Type*} [Group A] [Finite A] {Y X S : Subgroup A}
    (F : Subgroup A) (hSY : S ≤ Y) (hXnorm : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {x₁ σ' : A} (hx₁ : x₁ ∈ X) (hσ'S : σ' ∈ S) (hσ' : orderOf σ' = ℓ)
    (hy₁ : x₁ * σ' ∈ F) :
    ∃ x₂ ∈ X, ∃ τ ∈ S, ∃ a : ℕ, x₂ * τ ∈ F ∧ orderOf τ = ℓ ∧ orderOf (x₂ * τ) ∣ ℓ ^ a := by
  obtain ⟨a, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (x₁ * σ')).ne' ℓ hℓ.ne_one
  obtain ⟨x₂, hx₂, h₂⟩ := exists_pow_eq_mul_pow hXnorm hx₁ (hSY hσ'S) m
  refine ⟨x₂, hx₂, σ' ^ m, S.pow_mem hσ'S m, a, h₂ ▸ F.pow_mem hy₁ m, ?_, ?_⟩
  · rw [Nat.Coprime.orderOf_pow, hσ']
    rw [hσ']
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).2 hm
  · rw [← h₂]
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, ← hn]
    exact pow_orderOf_eq_one _

end Lemma13dFY

theorem le_fitting_map {A : Type*} [Group A] [Finite A] (Y X : Subgroup A) (hXY : X ≤ Y)
    (hXnorm : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hXcyc : IsCyclic X) :
    X ≤ (CFSG.fittingSubgroup ↥Y).map Y.subtype := by
  have := hXcyc
  have hNnorm : (X.subgroupOf Y).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hXnorm (g : A) g.2 (n : A) hn⟩
  have hNnil : Group.IsNilpotent (X.subgroupOf Y) :=
    Group.nilpotent_of_mulEquiv (G := X) (Subgroup.subgroupOfEquivOfLe hXY).symm
  have hle : X.subgroupOf Y ≤ CFSG.fittingSubgroup ↥Y := le_sSup ⟨hNnorm, hNnil⟩
  have hmap := Subgroup.map_mono (f := Y.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hXY] at hmap

theorem fitting_le_of_no_commute {A : Type*} [Group A] [Finite A] (Y X S : Subgroup A)
    (hXY : X ≤ Y) (hSY : S ≤ Y)
    (hXnorm : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hXcyc : IsCyclic X) (_hXS : X ⊓ S = ⊥)
    (hYXS : ∀ y ∈ Y, ∃ x ∈ X, ∃ σ ∈ S, y = x * σ)
    (hkey : ∀ σ ∈ S, ∀ ℓ : ℕ, ℓ.Prime → orderOf σ = ℓ →
      ∃ s : ℕ, s.Prime ∧ s ≠ ℓ ∧ s ∣ Nat.card X ∧ ∀ x ∈ X, orderOf x = s → σ * x ≠ x * σ) :
    (CFSG.fittingSubgroup ↥Y).map Y.subtype ≤ X := by
  intro y hyF
  by_contra hyX
  have hXF := le_fitting_map Y X hXY hXnorm hXcyc
  have hyY : y ∈ Y := Subgroup.map_subtype_le _ hyF
  obtain ⟨x, hx, σ, hσS, rfl⟩ := hYXS y hyY
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hyX (by simpa using hx)
  have hn0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  have hn1 : orderOf σ ≠ 1 := fun h => hσ1 (orderOf_eq_one_iff.1 h)
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn1
  have hσ'ord : orderOf (σ ^ (orderOf σ / ℓ)) = ℓ := orderOf_pow_orderOf_div hn0 hℓn
  obtain ⟨x₁, hx₁, hy₁⟩ := Lemma13dFY.exists_pow_eq_mul_pow hXnorm hx (hSY hσS) (orderOf σ / ℓ)
  obtain ⟨x₂, hx₂, τ, hτS, a, hy₂F, hτ, hy₂ord⟩ :=
    Lemma13dFY.exists_prime_power_part (Y := Y) ((CFSG.fittingSubgroup ↥Y).map Y.subtype) hSY hXnorm
      hℓ hx₁ (S.pow_mem hσS _) hσ'ord (hy₁ ▸ Subgroup.pow_mem _ hyF _)
  obtain ⟨s, hs, hsℓ, hsX, hcomm⟩ := hkey τ hτS ℓ hℓ hτ
  have := Fact.mk hs
  obtain ⟨x₀', hx₀'⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) s hsX
  have hx₀X : (x₀' : A) ∈ X := x₀'.2
  have hx₀ord : orderOf (x₀' : A) = s := by rw [Subgroup.orderOf_coe]; exact hx₀'
  have hcop : (orderOf (x₂ * τ)).Coprime (orderOf (x₀' : A)) := by
    rw [hx₀ord]
    exact (((Nat.coprime_primes hℓ hs).2 hsℓ.symm).pow_left a).coprime_dvd_left hy₂ord
  have hcom := Lemma13dFY.commute_of_mem_map_fitting Y hy₂F (hXF hx₀X) hcop
  refine hcomm (x₀' : A) hx₀X hx₀ord ?_
  have hXc : x₂ * (x₀' : A) = (x₀' : A) * x₂ := by
    have := (IsCyclic.commGroup (α := ↥X)).mul_comm ⟨x₂, hx₂⟩ x₀'
    exact congrArg Subtype.val this
  refine mul_left_cancel (a := x₂) ?_
  calc x₂ * (τ * (x₀' : A)) = x₂ * τ * (x₀' : A) := by rw [mul_assoc]
    _ = (x₀' : A) * (x₂ * τ) := hcom.eq
    _ = (x₀' : A) * x₂ * τ := by rw [mul_assoc]
    _ = x₂ * (x₀' : A) * τ := by rw [hXc]
    _ = x₂ * ((x₀' : A) * τ) := by rw [mul_assoc]

end CFSG.GH74.GLS.IVK.Proofs2
