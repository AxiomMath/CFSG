module

public import CFSG.GH74.Uniqueness.Bender.Out

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem A6.conj_injective {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : Bender.BenderType K n i e) : Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : g ∈ center K := by
    rw [mem_center_iff]
    intro y
    have := congrArg (fun σ : MulAut K => σ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = (g * y * g⁻¹) * g := by rw [this]
      _ = g * y := by group
  rw [h.center_eq_bot, mem_bot] at hg'
  exact hg'

theorem A6.exists_not_inner_of_card_gt
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : Bender.BenderType K n i e) (E : Subgroup (MulAut K)) (hsq : ∀ σ ∈ E, σ * σ = 1)
    (hcard : 2 ^ n < Nat.card E) : ∃ σ ∈ E, ¬ ∃ g : K, ∀ x : K, σ x = g * x * g⁻¹ := by
  by_contra hall'
  have hall : ∀ σ ∈ E, ∃ g : K, ∀ x : K, σ x = g * x * g⁻¹ := fun σ hσ => by
    by_contra hne
    exact hall' ⟨σ, hσ, hne⟩
  have hinj := A6.conj_injective h
  set E₁ : Subgroup K := E.comap (MulAut.conj : K →* MulAut K) with hE₁
  have hmap : E₁.map (MulAut.conj : K →* MulAut K) = E := by
    apply le_antisymm (map_comap_le _ _)
    intro σ hσ
    obtain ⟨g, hg⟩ := hall σ hσ
    have hσg : σ = MulAut.conj g := MulEquiv.ext fun x => by rw [hg x, MulAut.conj_apply]
    refine ⟨g, ?_, hσg.symm⟩
    change MulAut.conj g ∈ E
    rw [← hσg]
    exact hσ
  have hE₁sq : ∀ k ∈ E₁, k * k = 1 := fun k hk =>
    hinj (by rw [map_mul, map_one]; exact hsq _ hk)
  have hle := h.card_le_of_sq_eq_one E₁ hE₁sq
  rw [← hmap, Subgroup.card_map_of_injective hinj] at hcard
  omega

theorem A6.card_psl2_four : Nat.card (Theory.Comparator.PSL2Model 2) = 60 := by
  rw [show Nat.card (Theory.Comparator.PSL2Model 2) = 2 ^ 2 * ((2 ^ 2) ^ 2 - 1) from
    Bender.card_psl2_even 2 (by norm_num)]
  norm_num

theorem A6.card_outer_unitary_four {K : Type} [Group K] [Finite K] {e : ℕ}
    (h : Bender.BenderType K 2 3 e) : Nat.card (Outer K) = 4 := by
  have : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    DFunLike.coe_injective
  obtain ⟨Dd, hDd, -, hcard, -, hq⟩ := h.outer_unitary
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Dd, hq, hcard]
  norm_num

theorem A6.card_le_of_unitary_four {K : Type} [Group K] [Finite K] {e : ℕ}
    (h : Bender.BenderType K 2 3 e) (Q : Subgroup (MulAut K)) (hQ : IsPGroup 2 Q)
    (hQc : ∀ σ ∈ Q, ∀ τ ∈ Q, σ * τ = τ * σ) {v : MulAut K} (hvQ : v ∈ Q) (hv2 : v * v = 1)
    (hout : ¬ ∃ g : K, ∀ x : K, v x = g * x * g⁻¹) : Nat.card Q ≤ 2 ^ 4 := by
  classical
  have : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    DFunLike.coe_injective
  have hinj := A6.conj_injective h
  set C : Subgroup K := Q.comap (MulAut.conj : K →* MulAut K) with hC
  have hCv : C ≤ Bender.autFixed v := by
    intro k hk
    have h1 : MulAut.conj k * v = v * MulAut.conj k := hQc _ hk v hvQ
    have h2 : v * MulAut.conj k * v⁻¹ = MulAut.conj (v k) := by
      refine MulEquiv.ext fun x => ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
        map_mul, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    have h3 : MulAut.conj (v k) = MulAut.conj k := by
      rw [← h2, ← h1, mul_inv_cancel_right]
    exact hinj h3
  have hCp : IsPGroup 2 C := by
    have h1 : IsPGroup 2 (C.map (MulAut.conj : K →* MulAut K)) := hQ.to_le (map_comap_le _ _)
    exact h1.of_equiv (C.equivMapOfInjective _ hinj).symm
  have hC4 : Nat.card C ≤ 4 := by
    obtain ⟨φ⟩ := h.fixed_unitary v hv2 hout
    have h60 : Nat.card (Bender.autFixed v) = 60 := by
      rw [Nat.card_congr φ.toEquiv, A6.card_psl2_four]
    have hdvd : Nat.card C ∣ 60 := h60 ▸ Subgroup.card_dvd_of_le hCv
    obtain ⟨k, hk⟩ := hCp.exists_card_eq
    rw [hk] at hdvd ⊢
    by_contra hlt
    have hk3 : 3 ≤ k := by
      by_contra hk3
      interval_cases k <;> simp_all
    have : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 hk3).trans hdvd
    norm_num at this
  set f : ↥Q →* Outer K := (QuotientGroup.mk' (OuterAutomorphisms.inner K)).comp Q.subtype with hf
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card Q := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : Nat.card f.ker ≤ Nat.card C := by
    have hle : f.ker.map Q.subtype ≤ C.map (MulAut.conj : K →* MulAut K) := by
      rintro _ ⟨σ, hσ, rfl⟩
      have hσI : (σ : MulAut K) ∈ OuterAutomorphisms.inner K :=
        (QuotientGroup.eq_one_iff _).mp hσ
      change (σ : MulAut K) ∈ (MulAut.conj : K →* MulAut K).range at hσI
      obtain ⟨g, hg⟩ := hσI
      refine ⟨g, ?_, hg⟩
      change MulAut.conj g ∈ Q
      rw [hg]
      exact σ.2
    have h1 := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective Q.subtype_injective,
      Subgroup.card_map_of_injective hinj] at h1
  have hrange : Nat.card f.range ≤ 4 := by
    rw [← A6.card_outer_unitary_four h]
    exact Subgroup.card_le_card_group (H := f.range)
  calc Nat.card Q = Nat.card f.ker * Nat.card f.range := hcard.symm
    _ ≤ 4 * 4 := Nat.mul_le_mul (hker.trans hC4) hrange
    _ = 2 ^ 4 := by norm_num

end CFSG.GH74.Uniqueness
