module

public import CFSG.LargeExtraspecial.S4CESmallPlus
public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.LargeExtraspecial.S10Iso
public import CFSG.LargeExtraspecial.S10ModelC
public import CFSG.LargeExtraspecial.S10ModelD
public import CFSG.LargeExtraspecial.S4CEToolTwo
public import CFSG.LargeExtraspecial.S4Lin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

theorem sq_σ₁_spec : (S10.σ₁ ^ 2).2 = 1 ∧ (S10.σ₁ ^ 2) ^ 3 = 1 ∧ S10.σ₁ ^ 2 ≠ 1 := by
  decide +kernel

theorem sq_σ₂_spec : (S10.σ₂ ^ 2).1 = 1 ∧ (S10.σ₂ ^ 2) ^ 3 = 1 ∧ S10.σ₂ ^ 2 ≠ 1 := by
  decide +kernel

theorem mul_comm_of_snd_eq_one_of_fst_eq_one {γ δ : S10.Gm} (hγ : γ.2 = 1) (hδ : δ.1 = 1) :
    γ * δ = δ * γ :=
  Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hδ, mul_one, one_mul])
    (by rw [Prod.snd_mul, Prod.snd_mul, hγ, mul_one, one_mul])

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem ker_eq_bot_of_omegaPair_plus_four {K : Type*} [Group K] [Finite K]
    {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) (hP : S10.PlusType4 Q) (ha0 : a ≠ 0) (hQa : Q a = 0)
    (h : CEHyp π E a (omegaGroup Q hQ) (pointRadical Q a)) : π.ker = ⊥ := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  obtain ⟨φ, hφ, hφa⟩ := S10.exists_isometry_M2_base h4 hQ hP ha0 hQa
  set ψ := S10.psi φ with hψdef
  have hψinj : Function.Injective ψ := S10.psi_injective
  have hψr : ψ.range = omegaGroup Q hQ := S10.range_psi hφ hQ
  have hψa : ∀ γ, ψ γ a = a ↔ S10.act γ S10.E00 = S10.E00 := by
    intro γ
    rw [S10.psi_apply, hφa, LinearEquiv.symm_apply_eq, hφa]
  have hE₀X : pointRadical Q a ≤ omegaGroup Q hQ := by
    rw [← h.map_eq, ← h.range_eq]
    exact map_le_range π E
  have hstab : ∀ t ∈ pointRadical Q a,
      t = ψ 1 ∨ t = ψ S10.τ₁ ∨ t = ψ S10.τ₂ ∨ t = ψ (S10.τ₁ * S10.τ₂) := by
    intro t ht
    obtain ⟨γ, rfl⟩ : t ∈ ψ.range := hψr ▸ hE₀X ht
    rcases (S10.act_E00_iff γ).mp ((hψa γ).mp ht.2.1) with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hET : (pointRadical Q a : Set (V ≃ₗ[ZMod 2] V)) =
      {ψ 1, ψ S10.τ₁, ψ S10.τ₂, ψ (S10.τ₁ * S10.τ₂)} := by
    refine Set.eq_of_subset_of_ncard_le (fun t ht => hstab t ht) ?_ (Set.toFinite _)
    have hc : (pointRadical Q a : Set (V ≃ₗ[ZMod 2] V)).ncard = 4 := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, card_pointRadical hQ ha0 hQa, h4]
      rfl
    rw [hc]
    refine (Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
      (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_))))
    rw [Set.ncard_singleton]
  have hmemE₀ : ∀ γ ∈ ({S10.τ₁, S10.τ₂} : Set S10.Gm), ψ γ ∈ pointRadical Q a := by
    rintro γ (rfl | rfl)
    · change _ ∈ (pointRadical Q a : Set (V ≃ₗ[ZMod 2] V))
      rw [hET]
      simp
    · change _ ∈ (pointRadical Q a : Set (V ≃ₗ[ZMod 2] V))
      rw [hET]
      simp
  obtain ⟨t₁, ht₁E, ht₁⟩ : ψ S10.τ₁ ∈ E.map π := h.map_eq ▸ hmemE₀ _ (Or.inl rfl)
  obtain ⟨t₂, ht₂E, ht₂⟩ : ψ S10.τ₂ ∈ E.map π := h.map_eq ▸ hmemE₀ _ (Or.inr rfl)
  have hEone : ∀ e ∈ E, π e = 1 → e = 1 := fun e he hπ =>
    h.eq_of_mem he (one_mem E) (by rw [hπ, map_one])
  have ht₁t₁ : t₁ * t₁ = 1 := hEone _ (mul_mem ht₁E ht₁E) (by
    rw [map_mul, ht₁, ← map_mul, S10.τ₁_sq, map_one])
  have ht₂t₂ : t₂ * t₂ = 1 := hEone _ (mul_mem ht₂E ht₂E) (by
    rw [map_mul, ht₂, ← map_mul, S10.τ₂_sq, map_one])
  have ht₁₂ : t₁ * t₂ = t₂ * t₁ := h.eq_of_mem (mul_mem ht₁E ht₂E) (mul_mem ht₂E ht₁E) (by
    rw [map_mul, map_mul, ht₁, ht₂, ← map_mul, ← map_mul, S10.τ₁_τ₂_comm])
  have hrange : ∀ γ, ψ γ ∈ π.range := fun γ => by
    rw [h.range_eq, ← hψr]
    exact ⟨γ, rfl⟩
  obtain ⟨y₁', hy₁'⟩ := hrange S10.σ₁
  obtain ⟨y₂', hy₂'⟩ := hrange S10.σ₂
  obtain ⟨hσ₁2, hσ₁3, -⟩ := S10.σ₁_spec
  obtain ⟨hσ₂1, hσ₂3, -⟩ := S10.σ₂_spec
  obtain ⟨y₁, hy₁3, ht₁y₁, hπy₁⟩ := h.exists_lift_of_inv ht₁t₁
    (by rw [hy₁', ← map_pow, hσ₁3, map_one])
    (by rw [ht₁, hy₁', ← map_inv, ← map_mul, ← map_mul, S10.τ₁_inv _ hσ₁2 hσ₁3, map_inv])
  obtain ⟨y₂, hy₂3, ht₂y₂, hπy₂⟩ := h.exists_lift_of_inv ht₂t₂
    (by rw [hy₂', ← map_pow, hσ₂3, map_one])
    (by rw [ht₂, hy₂', ← map_inv, ← map_mul, ← map_mul, S10.τ₂_inv _ hσ₂1 hσ₂3, map_inv])
  rw [hy₁', ← map_pow] at hπy₁
  rw [hy₂', ← map_pow] at hπy₂
  obtain ⟨hs₁2, hs₁3, hs₁1⟩ := sq_σ₁_spec
  obtain ⟨hs₂1, hs₂3, hs₂1'⟩ := sq_σ₂_spec
  have hcen : ∀ {x y : K} {α β : S10.Gm}, π x = ψ α → π y = ψ β → α.2 = 1 → β.1 = 1 →
      ⁅x, y⁆ ∈ center K := fun hx hy hα hβ => h.mem_center_of_mem_ker (by
    rw [map_commutatorElement, hx, hy, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_snd_eq_one_of_fst_eq_one hα hβ),
      map_one])
  have hτ₁2 : S10.τ₁.2 = 1 := S10.mem_Γ₁.mp S10.τ₁_mem_Γ₁
  have hτ₂1 : S10.τ₂.1 = 1 := S10.mem_Γ₂.mp S10.τ₂_mem_Γ₂
  have hc₁ : ⁅t₁, y₂⁆ = 1 := commutatorElement_eq_one_of_inv (hcen ht₁ hπy₂ hτ₁2 hs₂1)
    (by rw [← ht₁₂, mul_inv_cancel_right]) ht₂y₂ hy₂3
  have hc₂ : ⁅t₂, y₁⁆ = 1 := commutatorElement_eq_one_of_inv
    (by rw [← commutatorElement_inv]; exact inv_mem (hcen hπy₁ ht₂ hs₁2 hτ₂1))
    (by rw [ht₁₂, mul_inv_cancel_right]) ht₁y₁ hy₁3
  have hty : t₁ * y₂ = y₂ * t₁ := commutatorElement_eq_one_iff_mul_comm.mp hc₁
  have hty' : t₂ * y₁ = y₁ * t₂ := commutatorElement_eq_one_iff_mul_comm.mp hc₂
  have hc₃ : ⁅y₂, y₁⁆ = 1 := commutatorElement_eq_one_of_inv
    (by rw [← commutatorElement_inv]; exact inv_mem (hcen hπy₁ hπy₂ hs₁2 hs₂1))
    (by rw [hty, mul_inv_cancel_right]) ht₁y₁ hy₁3
  have hyy : y₂ * y₁ = y₁ * y₂ := commutatorElement_eq_one_iff_mul_comm.mp hc₃
  set R : Fin 4 → Subgroup K := ![zpowers y₁, zpowers y₂, zpowers t₁, zpowers t₂] with hRdef
  have hR : ∀ i j : Fin 4, i < j → R j ≤ normalizer (R i : Set K) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij <;> simp only [hRdef]
    · exact zpowers_le_normalizer_of_commute hyy
    · exact zpowers_le_normalizer_of_inv ht₁t₁ ht₁y₁
    · exact zpowers_le_normalizer_of_commute hty'
    · exact zpowers_le_normalizer_of_commute hty
    · exact zpowers_le_normalizer_of_inv ht₂t₂ ht₂y₂
    · exact zpowers_le_normalizer_of_commute ht₁₂.symm
  set H := ⨆ i, R i with hH
  have hHcard : Nat.card H ≤ 36 := by
    refine (card_iSup_le_prod R hR).trans ?_
    rw [Fin.prod_univ_four]
    simp only [hRdef, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Nat.card_zpowers]
    have o1 : orderOf y₁ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hy₁3
    have o2 : orderOf y₂ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hy₂3
    have o3 : orderOf t₁ ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, ht₁t₁])
    have o4 : orderOf t₂ ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, ht₂t₂])
    calc orderOf y₁ * orderOf y₂ * orderOf t₁ * orderOf t₂ ≤ 3 * 3 * 2 * 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul o1 o2) o3) o4
      _ = 36 := by norm_num
  have hy₁H : y₁ ∈ H := le_iSup R 0 (mem_zpowers y₁)
  have hy₂H : y₂ ∈ H := le_iSup R 1 (mem_zpowers y₂)
  have ht₁H : t₁ ∈ H := le_iSup R 2 (mem_zpowers t₁)
  have ht₂H : t₂ ∈ H := le_iSup R 3 (mem_zpowers t₂)
  have hXH : omegaGroup Q hQ ≤ H.map π := by
    rw [← hψr]
    rintro _ ⟨γ, rfl⟩
    obtain ⟨i, -, j, -, hγ1⟩ := S10.Γ₁_gen _ hs₁2 hs₁3 hs₁1 (γ.1, 1) rfl
    obtain ⟨k, -, l, -, hγ2⟩ := S10.Γ₂_gen _ hs₂1 hs₂3 hs₂1' (1, γ.2) rfl
    refine ⟨t₁ ^ j * y₁ ^ i * (t₂ ^ l * y₂ ^ k), mul_mem (mul_mem (pow_mem ht₁H j)
      (pow_mem hy₁H i)) (mul_mem (pow_mem ht₂H l) (pow_mem hy₂H k)), ?_⟩
    rw [S10.eq_mul_of_factors γ, hγ1, hγ2]
    simp only [map_mul, map_pow, ht₁, hπy₁, ht₂, hπy₂]
  have hXcard : Nat.card (omegaGroup Q hQ) = 36 := by
    rw [← hψr, ← S10.card_Gm]
    exact Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv.symm
  have hHZ : H ⊓ π.ker = ⊥ :=
    inf_ker_eq_bot_of_card_le π (hHcard.trans (hXcard ▸ card_le_of_le hXH))
  have hEH : E ≤ H := by
    intro e he
    have hπe : π e ∈ (pointRadical Q a : Set (V ≃ₗ[ZMod 2] V)) := h.map_eq ▸ ⟨e, he, rfl⟩
    rw [hET] at hπe
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hπe
    rcases hπe with h1 | h1 | h1 | h1
    · rw [hEone e he (by rw [h1, map_one])]
      exact one_mem H
    · rw [h.eq_of_mem he ht₁E (h1.trans ht₁.symm)]
      exact ht₁H
    · rw [h.eq_of_mem he ht₂E (h1.trans ht₂.symm)]
      exact ht₂H
    · rw [h.eq_of_mem he (mul_mem ht₁E ht₂E) (by rw [h1, map_mul, map_mul, ht₁, ht₂])]
      exact mul_mem ht₁H ht₂H
  exact h.ker_eq_bot_of_le hHZ hXH (k := 1) (by rwa [Eb_one])

end CFSG.LargeExtraspecial.S4
