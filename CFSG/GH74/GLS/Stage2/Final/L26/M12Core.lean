module

public import CFSG.GH74.GLS.Stage2.Final.L26.G2Lift

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

theorem key_s3 : ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 →
    ∃ x : Equiv.Perm (Fin 3), ⁅x, σ⁆ ≠ 1 ∧ ⁅x, σ⁆ ^ 3 = 1 := by
  decide +kernel

theorem exists_conj_of_card_three {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y = 192)
    {A P : Subgroup Y} (hA : Nat.card ↥A = 3) (hP : Nat.card ↥P = 3) :
    ∃ c : Y, ∀ a ∈ A, c * a * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hidxA : ¬ 3 ∣ A.index := by
    have := Subgroup.card_mul_index A
    rw [hA, hY] at this
    omega
  have hidxP : ¬ 3 ∣ P.index := by
    have := Subgroup.card_mul_index P
    rw [hP, hY] at this
    omega
  have hPA : IsPGroup 3 ↥A := IsPGroup.of_card (n := 1) (by rw [hA]; norm_num)
  have hPP : IsPGroup 3 ↥P := IsPGroup.of_card (n := 1) (by rw [hP]; norm_num)
  let YA : Sylow 3 Y := hPA.toSylow hidxA
  let YP : Sylow 3 Y := hPP.toSylow hidxP
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y YA YP
  refine ⟨c, fun a ha => ?_⟩
  have hmem : c * a * c⁻¹ ∈ ((c • YA : Sylow 3 Y) : Subgroup Y) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj c) _ ha
  rw [hc] at hmem
  exact hmem

theorem le_O2Of_commutator_of_perm3 {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 192)
    {W A : Subgroup Y} [hW : W.Normal] (e : (Y ⧸ W) ≃* Equiv.Perm (Fin 3))
    (hA : Nat.card ↥A = 3) (hWA : ⁅W, A⁆ = W) {y : Y} (hy2 : y * y = 1) (hyW : y ∉ W) :
    W ≤ O2Of ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ := by
  have hN : (⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆).Normal := commutator_top_normal _
  let π : Y →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' W)
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective W)
  have hπy2 : π y * π y = 1 := by rw [← map_mul, hy2, map_one]
  have hπy1 : π y ≠ 1 := by
    intro h
    apply hyW
    have h1 : e (QuotientGroup.mk y) = 1 := h
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨τ, hτ1, hτ3⟩ := key_s3 (π y) hπy2 hπy1
  obtain ⟨x, hx⟩ := hπs τ
  have hmN : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_zpowers y)
  have hπm : π ⁅x, y⁆ = ⁅τ, π y⁆ := by rw [map_commutatorElement, hx]
  obtain ⟨n, hn⟩ : ∃ n : Y, n = ⁅x, y⁆ ^ 64 := ⟨_, rfl⟩
  have hnN : n ∈ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ := hn ▸ Subgroup.pow_mem _ hmN _
  have hn3 : n ^ 3 = 1 := by
    rw [hn, ← pow_mul]
    have := pow_card_eq_one' (G := Y) (x := ⁅x, y⁆)
    rw [hY] at this
    exact this
  have hn1 : n ≠ 1 := by
    intro h1
    apply hτ1
    have h2 : π n = 1 := by rw [h1, map_one]
    rw [hn, map_pow, hπm] at h2
    have h3 : ⁅τ, π y⁆ ^ 64 = ⁅τ, π y⁆ ^ 1 := by
      have : (64 : ℕ) = 3 * 21 + 1 := by norm_num
      rw [this, pow_add, pow_mul, hτ3, one_pow, one_mul]
    rw [h3, pow_one] at h2
    exact h2
  have hord : orderOf n = 3 := orderOf_eq_prime hn3 hn1
  have hP3 : Nat.card ↥(Subgroup.zpowers n) = 3 := by rw [Nat.card_zpowers, hord]
  obtain ⟨c, hc⟩ := exists_conj_of_card_three hY hA hP3
  have hAN : A ≤ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ := by
    intro a ha
    have h1 : c * a * c⁻¹ ∈ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ :=
      (Subgroup.zpowers_le.mpr hnN) (hc a ha)
    have h2 := hN.conj_mem _ h1 c⁻¹
    have h3 : c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a := by group
    rwa [h3] at h2
  have hAodd : ∀ a ∈ A, Nat.Coprime (orderOf a) 2 := by
    intro a ha
    have h1 : orderOf (⟨a, ha⟩ : ↥A) ∣ Nat.card ↥A := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hA] at h1
    have : orderOf a ∣ 3 := h1
    exact Nat.Coprime.coprime_dvd_left this (by norm_num)
  have hAT : A ≤ O2Of ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ :=
    fun a ha => mem_O2Of_of_odd (hAN ha) (hAodd a ha)
  have hTn : (O2Of ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆).Normal := O2Of_normal _
  rw [← hWA]
  refine Subgroup.commutator_le.2 fun w _ a ha => ?_
  have : ⁅w, a⁆ = (w * a * w⁻¹) * a⁻¹ := by simp [commutatorElement_def]
  rw [this]
  exact Subgroup.mul_mem _ (hTn.conj_mem a (hAT ha) w) (Subgroup.inv_mem _ (hAT ha))

end CFSG.GH74.GLS.Stage2.Final.L26
