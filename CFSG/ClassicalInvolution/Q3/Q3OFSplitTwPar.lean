module

public import CFSG.ClassicalInvolution.Q3.Q3PPKlein
public import CFSG.ClassicalInvolution.Q3.Q3PPInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3PP

section Parity

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_sq_eq_one_of_odd {P : Subgroup G} (hP : Odd (Nat.card P)) {w : G} (hw : w ∈ P)
    (h : w * w = 1) : w = 1 := by
  have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h2 : orderOf w ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hw
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · rw [h3] at h2
    exact absurd (hP.of_dvd_nat h2) (by decide)

theorem eq_bot_of_parity {x z : G} {J : Set G} (hJ2 : ∀ j ∈ J, j * j = 1)
    (hJc : ∀ j ∈ J, j * x = x * j)
    (hJf : ∀ j ∈ J, ∀ r ∈ involutionOddCore x, r * j = j * r → r = 1) (hz : z ∈ J)
    (hpar : z ∈ Subgroup.closure (Set.image2 (· * ·) J J)) :
    involutionOddCore x = ⊥ := by
  have hodd : Odd (Nat.card (involutionOddCore x)) := by
    rw [involutionOddCore_eq_oddCoreIn]
    exact odd_card_oddCoreIn _
  have hinv : ∀ j ∈ J, ∀ w ∈ involutionOddCore x, j * w * j⁻¹ = w⁻¹ := fun j hj w hw =>
    (fpf_inverts_of_finite (W := involutionOddCore x) (hJ2 j hj)
      (fun w' hw' => by
        rw [involutionOddCore_eq_oddCoreIn] at hw' ⊢
        exact conj_mem_oddCoreIn (Subgroup.mem_centralizer_singleton_iff.mpr (hJc j hj)) hw')
      (fun w' hw' h => hJf j hj w' hw' (mul_inv_eq_iff_eq_mul.mp h).symm)).1 w hw
  have hsub : Set.image2 (· * ·) J J ⊆
      (Subgroup.centralizer (involutionOddCore x : Set G) : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : b * w * b⁻¹ = w⁻¹ := hinv b hb w hw
    have h2 : a * w⁻¹ * a⁻¹ = w := by
      have := hinv a ha w⁻¹ ((involutionOddCore x).inv_mem hw)
      rw [this]
      exact inv_inv w
    have h3 : a * b * w * (a * b)⁻¹ = w := by
      calc a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
        _ = w := by rw [h1, h2]
    exact (mul_inv_eq_iff_eq_mul.mp h3).symm
  have hzc : z ∈ Subgroup.centralizer (involutionOddCore x : Set G) :=
    (Subgroup.closure_le _).mpr hsub hpar
  refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
  have hc : z * w = w * z := (Subgroup.mem_centralizer_iff.mp hzc w hw).symm
  have h1 : z * w * z⁻¹ = w⁻¹ := hinv z hz w hw
  have h2 : z * w * z⁻¹ = w := by rw [hc]; group
  have hww : w * w = 1 := by
    have : w⁻¹ = w := h1.symm.trans h2
    calc w * w = w⁻¹ * w := by rw [this]
      _ = 1 := inv_mul_cancel w
  exact eq_one_of_sq_eq_one_of_odd hodd hw hww

end Parity

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

@[expose] def OddFixLe (K : Subgroup G) (w x : G) : Prop :=
  oddCoreIn (centralizingLayer (conjClass3 K) {w} ⊓ Subgroup.centralizer ({x} : Set G)) ≤
    oddCoreIn (centralizingLayer (conjClass3 K) {w})

@[expose] def ParityAt (K K₁ : Subgroup G) (z₁ z₂ : G) : Prop :=
  ∃ W : Set G, (∀ w ∈ W, (∃ M ∈ conjClass3 K, IsClassicalMember3 M w) ∧ w ≠ z₁ ∧
      K₁ ≤ Subgroup.centralizer ({w} : Set G) ∧ w * z₂ = z₂ * w) ∧
    z₂ ∈ Subgroup.closure (Set.image2 (· * ·) (insert z₂ W) (insert z₂ W))

theorem involutionOddCore_prod_eq_bot_of_parityAt (hOA : OddAutLayerRigidHyp)
    (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hP : ParityAt K K₁ z₁ z₂)
    (hO : ∀ w : G, (∃ M ∈ conjClass3 K, IsClassicalMember3 M w) → w ≠ z₁ →
      K₁ ≤ Subgroup.centralizer ({w} : Set G) → w * z₂ = z₂ * w → OddFixLe K w (z₁ * z₂)) :
    involutionOddCore (z₁ * z₂) = ⊥ := by
  obtain ⟨W, hW, hpar⟩ := hP
  have hΩ := hR.inClass.conjInvariant
  have hxz₂ : z₂ * (z₁ * z₂) = (z₁ * z₂) * z₂ := by
    calc z₂ * (z₁ * z₂) = (z₂ * z₁) * z₂ := (mul_assoc _ _ _).symm
      _ = (z₁ * z₂) * z₂ := by rw [h.mul_comm₁₂]
  have hfz₂ : ∀ r ∈ involutionOddCore (z₁ * z₂), r * z₂ = z₂ * r → r = 1 := by
    intro r hr hrz
    have hr' : r ∈ involutionOddCore (z₂ * z₁) := by
      rw [← h.mul_comm₁₂]
      exact hr
    have hmem : r ∈ involutionOddCore (z₂ * z₁) ⊓ Subgroup.centralizer ({z₂} : Set G) :=
      ⟨hr', Subgroup.mem_centralizer_singleton_iff.mpr hrz⟩
    rw [h.swapEdge.oddCore_inf_centralizer_eq_bot hOA hR hnab] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfz : ∀ r ∈ involutionOddCore (z₁ * z₂), r * z₁ = z₁ * r → r = 1 := by
    intro r hr hrz
    have hmem : r ∈ involutionOddCore (z₁ * z₂) ⊓ Subgroup.centralizer ({z₁} : Set G) :=
      ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hrz⟩
    rw [h.oddCore_inf_centralizer_eq_bot hOA hR hnab] at hmem
    exact Subgroup.mem_bot.mp hmem
  refine eq_bot_of_parity (J := insert z₂ W) (z := z₂) ?_ ?_ ?_ (Set.mem_insert _ _) hpar
  · intro j hj
    rcases hj with hj | hj
    · rw [hj]
      exact h.sq₂
    · obtain ⟨⟨M, hM, hcl⟩, -, -, -⟩ := hW j hj
      exact Q3NT.mul_self_eq_one_of_orderOf_eq_two hcl.orderOf_eq_two
  · intro j hj
    rcases hj with hj | hj
    · rw [hj]
      exact hxz₂
    · obtain ⟨-, -, hKj, hjz⟩ := hW j hj
      have h1 : z₁ * j = j * z₁ := Subgroup.mem_centralizer_singleton_iff.mp (hKj h.cls₁.mem)
      calc j * (z₁ * z₂) = (j * z₁) * z₂ := (mul_assoc _ _ _).symm
        _ = (z₁ * j) * z₂ := by rw [h1]
        _ = z₁ * (j * z₂) := mul_assoc _ _ _
        _ = z₁ * (z₂ * j) := by rw [hjz]
        _ = (z₁ * z₂) * j := (mul_assoc _ _ _).symm
  · intro j hj
    rcases hj with hj | hj
    · rw [hj]
      exact hfz₂
    · obtain ⟨⟨M, hM, hcl⟩, hne, hKj, hjz⟩ := hW j hj
      exact fixedPointFree_of_witness hΩ (hO j ⟨M, hM, hcl⟩ hne hKj hjz)
        (involutionOddCore_eq_bot_of_member hR hM hcl) (le_centralizingLayer ⟨h.mem₁, hKj⟩)
        h.le_centralizer_prod₁ h.cls₁.mem hfz

end Edge

end CFSG.ClassicalInvolution.Q3.Q3OF
