module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryParabThreeRankNode
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSU

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.LieType.CurtisTits

section Scalar

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem inv_mul_mem_center_of_mat_eq_scalar_mul {x y : SU σ n} {u : F}
    (h : mat σ n x = Matrix.scalar (Fin n) u * mat σ n y) :
    y⁻¹ * x ∈ Subgroup.center (SU σ n) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply mat_injective
  have hy : mat σ n y⁻¹ * mat σ n y = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hc : ∀ M : Matrix (Fin n) (Fin n) F,
      Matrix.scalar (Fin n) u * M = M * Matrix.scalar (Fin n) u :=
    fun M => (Matrix.scalar_commute u (fun r => mul_comm _ r) M).eq
  have e : mat σ n y⁻¹ * mat σ n x = Matrix.scalar (Fin n) u := by
    rw [h, ← Matrix.mul_assoc, ← hc, Matrix.mul_assoc, hy, Matrix.mul_one]
  simp only [map_mul]
  rw [e]
  exact (hc _).symm

end Scalar

theorem map_eq_one_of_mem_center_of_center_eq_bot {G W : Type*} [Group G] [Group W]
    (hW : Subgroup.center W = ⊥) {π : G →* W} (hπ : Function.Surjective π) {z : G}
    (hz : z ∈ Subgroup.center G) : π z = 1 := by
  have h : π z ∈ Subgroup.center W := Subgroup.map_center_le_center hπ ⟨z, hz, rfl⟩
  rwa [hW, Subgroup.mem_bot] at h

section FieldFour

variable {F : Type*} [Field F] (hF : Nat.card F = (2 ^ 1) ^ 2)

include hF in
theorem pow_three_eq_one_of_ne_zero_of_card_four {x : F} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 x hx)
  rw [Nat.card_units, hF] at h
  have h' := congrArg Units.val h
  simpa using h'

end FieldFour

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2)

theorem zero_succ_lt_six : (⟨0, by norm_num⟩ : Fin (6 / 2)).val + 1 < 6 / 2 := by norm_num

include hF in
theorem exists_inv_shortTorus_mul_mem_center_six {t : SU (unitaryInvolution F 2 1) 6}
    (ht : t ∈ diagSubgroup (unitaryInvolution F 2 1) 6) :
    ∃ c : Fˣ, (shortTorus (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF)
      (lowIdx_ne_succ zero_succ_lt_six) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (c : F))⁻¹ * t ∈
        Subgroup.center (SU (unitaryInvolution F 2 1) 6) := by
  obtain ⟨τ, hτ⟩ := ht
  have hσ : ∀ x : F, unitaryInvolution F 2 1 x = x ^ 2 := fun x => by
    rw [unitaryInvolution_apply, pow_one]
  have hu : ∀ s, τ s ^ 2 * τ (Fin.rev s) = 1 := fun s => by
    rw [← hσ]
    exact unitary_of_coe_eq_diagonal hτ s
  have hne : ∀ s, τ s ≠ 0 := fun s h => by
    have := hu s
    rw [h] at this
    simp at this
  have h3 : ∀ s, τ s ^ 3 = 1 := fun s => pow_three_eq_one_of_ne_zero_of_card_four hF (hne s)
  have hdet : τ 0 * τ 1 * τ 2 * τ 3 * τ 4 * τ 5 = 1 := by
    have h := t.2.1
    rw [hτ, det_diagonal, Fin.prod_univ_six] at h
    exact h
  have hu0 : τ 0 ^ 2 * τ 5 = 1 := hu 0
  have hu1 : τ 1 ^ 2 * τ 4 = 1 := hu 1
  have hu2 : τ 2 ^ 2 * τ 3 = 1 := hu 2
  have e0 := h3 0
  have e1 := h3 1
  have e2 := h3 2
  have n0 := hne 0
  have n2 := hne 2
  have h5 : τ 5 = τ 0 := by linear_combination (-τ 5) * e0 + τ 0 * hu0
  have h4 : τ 4 = τ 1 := by linear_combination (-τ 4) * e1 + τ 1 * hu1
  have h3' : τ 3 = τ 2 := by linear_combination (-τ 3) * e2 + τ 2 * hu2
  have hx2 : (τ 0 * τ 1 * τ 2) ^ 2 = 1 := by
    rw [h5, h4, h3'] at hdet
    linear_combination hdet
  have hx3 : (τ 0 * τ 1 * τ 2) ^ 3 = 1 := by
    rw [mul_pow, mul_pow, e0, e1, e2]
    ring
  have habc : τ 0 * τ 1 * τ 2 = 1 := by
    linear_combination (-(τ 0 * τ 1 * τ 2)) * hx2 + hx3
  set c : Fˣ := Units.mk0 (τ 0 * (τ 2)⁻¹) (mul_ne_zero n0 (inv_ne_zero n2)) with hc
  refine ⟨c, inv_mul_mem_center_of_mat_eq_scalar_mul (u := τ 2) ?_⟩
  rw [mat_apply, hτ, mat_apply, coe_shortTorus _ _ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero,
    Matrix.scalar_apply, diagonal_mul_diagonal, hc, Units.val_mk0]
  congr 1
  funext s
  fin_cases s
  all_goals simp only [shortTorusFun, hσ]
  all_goals simp (config := {decide := true}) only [Fin.isValue, ite_true, ite_false,
    Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one]
  · field_simp
  · field_simp
    linear_combination τ 2 ^ 2 * habc - τ 0 * τ 1 * e2
  · ring
  · rw [h3', mul_one]
  · rw [h4]
    field_simp
    linear_combination (-(τ 1 * τ 2)) * e0 + τ 0 ^ 2 * habc
  · rw [h5]
    field_simp
    linear_combination e0 - e2

include hF in
theorem card_map_torus_le_three_six {W : Type*} [Group W] (hW : Subgroup.center W = ⊥)
    {π : SU (unitaryInvolution F 2 1) 6 →* W} (hπ : Function.Surjective π) :
    Nat.card ((⨆ i, levelTorus (unitaryInvolution F 2 1) (n := 6) i).map π) ≤ 3 := by
  set f : Fˣ → W := fun c => π (shortTorus (unitaryInvolution F 2 1)
    (unitaryInvolution_involutive hF) (lowIdx_ne_succ zero_succ_lt_six) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) (c : F)) with hf
  have hsub : (((⨆ i, levelTorus (unitaryInvolution F 2 1) (n := 6) i).map π :
      Subgroup W) : Set W) ⊆ Set.range f := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨c, hc⟩ := exists_inv_shortTorus_mul_mem_center_six hF
      (iSup_le (fun k => levelTorus_le_diagSubgroup k) ht)
    refine ⟨c, ?_⟩
    have h1 := map_eq_one_of_mem_center_of_center_eq_bot hW hπ hc
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  calc Nat.card ((⨆ i, levelTorus (unitaryInvolution F 2 1) (n := 6) i).map π)
      ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
    _ ≤ Nat.card Fˣ := Finite.card_range_le f
    _ = 3 := by rw [Nat.card_units, hF]; norm_num

include hF in
theorem not_dvd_card_of_su_six {W : Type} [Group W] [Finite W] (hW : Subgroup.center W = ⊥)
    (α : SU (unitaryInvolution F 2 1) 6 →* W) (hα : Function.Surjective α)
    (hker : α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) 6))
    (T : Sylow 2 W) (J : Subgroup W)
    (hNJ : Subgroup.normalizer ((T : Subgroup W) : Set W) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup W) : Set W))
    (hperf : ∀ U : Subgroup W, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ¬ 27 ∣ Nat.card J := by
  have : Finite (SU (unitaryInvolution F 2 1) 6) := Finite.of_injective _ Subtype.val_injective
  set k : Fin (6 / 2) := ⟨2, by norm_num⟩ with hkdef
  have hk : ¬k.val + 1 < 6 / 2 := by simp only [hkdef]; omega
  obtain ⟨ζ, π', hQ, hLJ, hTJ, hUJ, hdec⟩ :=
    exists_lastNode_decomposition_su hF (by norm_num) hk α hα hker T J hNJ hJ hperf
  set L := (rankOne (rootDatum hF 6).rootGroup k).map π' with hL
  set Tt := (⨆ i, levelTorus (unitaryInvolution F 2 1) (n := 6) i).map π' with hTt
  set U := (posUnipotentExcept (rootDatum hF 6) k).map π' with hU
  have hprod : ∀ z ∈ J, ∃ a ∈ Tt ⊔ L, ∃ b ∈ U, z = a * b := by
    intro z hz
    obtain ⟨l, hl, t, ht, u, hu, rfl⟩ := hdec z hz
    refine ⟨π' l * π' t, mul_mem (Subgroup.mem_sup_right ⟨l, hl, rfl⟩)
      (Subgroup.mem_sup_left ⟨t, ht, rfl⟩), π' u, ⟨u, hu, rfl⟩, ?_⟩
    rw [map_mul, map_mul]
  have h1 := card_dvd_mul_of_forall_mem_mul (sup_le hTJ hLJ) hUJ hprod
  have hTL : Tt ≤ Subgroup.normalizer (L : Set W) :=
    (Subgroup.map_mono (iSup_torus_le_normalizer_rankOne hQ.ct k)).trans
      (Subgroup.le_normalizer_map π')
  have h2 := card_sup_dvd_mul Tt L hTL
  have h3 : Nat.card L ∣ 6 := (Subgroup.card_map_dvd _ _).trans
    (su_last_even_card hF (by decide) hk).dvd
  have h4 : Nat.card Tt ≤ 3 := card_map_torus_le_three_six hF hW hQ.surj
  have hU2 : IsPGroup 2 U := ((isPGroup_iSup_pos hQ.extras hQ.pGroup).to_le
    (posUnipotentExcept_le_posUnipotent (D := rootDatum hF 6) k)).map π'
  obtain ⟨b, hb⟩ := hU2.exists_card_eq
  intro h27
  have h5 : 27 ∣ Nat.card Tt * 6 * 2 ^ b := by
    refine h27.trans (h1.trans ?_)
    rw [hb]
    exact Nat.mul_dvd_mul (h2.trans (Nat.mul_dvd_mul_left _ h3)) dvd_rfl
  have h6 : 27 ∣ Nat.card Tt * 6 :=
    (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 27 2)).dvd_of_dvd_mul_right h5
  have h7 : 0 < Nat.card Tt := Nat.card_pos
  omega

end CFSG.AGLEmbedding
