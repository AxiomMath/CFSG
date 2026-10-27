module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eOrbit

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open Finset

theorem pi_eq_std {π : Equiv.Perm (Fin 8)} (hfix : ∀ z, π z ≠ z) (hpa : ∀ z, π z ∈ a₀ ↔ z ∈ a₀)
    (hpB : ∀ z, π z ∈ B₀ ↔ z ∈ B₀) : ∀ z, π z = π₀ z := by
  have key : ∀ z y : Fin 8, (y ∈ a₀ ↔ z ∈ a₀) → (y ∈ B₀ ↔ z ∈ B₀) → y ≠ z → y = π₀ z := by
    decide +kernel
  exact fun z => key z (π z) (hpa z) (hpB z) (hfix z)

@[expose] def g₁ : Equiv.Perm (Fin 8) := Equiv.swap 2 4 * Equiv.swap 3 5

theorem g₁_sign : Equiv.Perm.sign g₁ = 1 := by decide +kernel

theorem g₁_a₀ : a₀.map g₁.toEmbedding = B₀ := by decide +kernel

theorem g₁_symm_eq : ∀ z, g₁.symm z = ![0, 1, 4, 5, 2, 3, 6, 7] z := by decide +kernel

theorem π₀_symm_eq : ∀ z, π₀.symm z = ![1, 0, 3, 2, 5, 4, 7, 6] z := by decide +kernel

theorem π₀_eq : ∀ z, π₀ z = ![1, 0, 3, 2, 5, 4, 7, 6] z := by decide +kernel

theorem ind_24_eq : ∀ z, ind {2, 4} z = ![0, 0, 1, 0, 1, 0, 0, 0] z := by decide +kernel

theorem std_comm_wr {v : Fin 8 → ZMod 2} {e : ZMod 2} (hv : ∀ z, v z + v (π₀ z) = e) :
    (⟨fun z => (v 2 + v 4) * ind {2, 4} z, g₁⟩ : Wr 8) * ⟨v, π₀⟩ =
      (⟨v, π₀⟩ : Wr 8) * ⟨fun z => (v 2 + v 4) * ind {2, 4} z, g₁⟩ := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  simp only [π₀_eq, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7
  refine Wr.ext (funext fun z => ?_) ?_
  · rw [mul_vec, mul_vec]
    simp only [mul_vec, g₁_symm_eq, π₀_symm_eq, ind_24_eq]
    fin_cases z <;> simp
    all_goals
      clear hv h0 h1 h6 h7
      revert h2 h3 h4 h5
      generalize v 2 = a2
      generalize v 3 = a3
      generalize v 4 = a4
      generalize v 5 = a5
      generalize e = ee
      revert a2 a3 a4 a5 ee
      decide
  · show g₁ * π₀ = π₀ * g₁
    decide +kernel

theorem g₁_mem_aeSub (δ : ZMod 2) :
    (⟨fun z => δ * ind {2, 4} z, g₁⟩ : Wr 8) ∈ aeSub 8 := by
  refine ⟨?_, g₁_sign⟩
  show wsum (⟨fun z => δ * ind {2, 4} z, g₁⟩ : Wr 8) = 0
  simp only [wsum, Fin.sum_univ_eight, ind_24_eq]
  simp
  exact zmod_two_add_self δ

theorem mkQ_ofPerm_mem_aeBar8 {σ : Equiv.Perm (Fin 8)} (hσ : Equiv.Perm.sign σ = 1) :
    mkQ 8 (ofPerm σ) ∈ aeBar8 := by
  refine ⟨ofPerm σ, ⟨?_, hσ⟩, rfl⟩
  show wsum (ofPerm σ) = 0
  unfold wsum ofPerm
  simp

theorem exists_cent_vq {X : AEQ 8} (hX : X ∈ aeBar8) (hXX : X * X = 1)
    {a β : Finset (Fin 8)} (ha : a.card = 4) (hβ : β.card = 4) (haβ : (a ∩ β).card = 2)
    (hfix : ∀ z, permQ 8 X z ≠ z) (hpa : ∀ z, permQ 8 X z ∈ a ↔ z ∈ a)
    (hpβ : ∀ z, permQ 8 X z ∈ β ↔ z ∈ β) :
    ∃ J ∈ aeBar8, J * X = X * J ∧ J * vq a * J⁻¹ = vq β := by
  obtain ⟨hc₀, hcB, hcab⟩ := a₀_B₀_cross
  obtain ⟨n₁, hn₁, hn₁a, hn₁β⟩ := exists_even_perm_cross ha hβ haβ hc₀ hcB hcab
  set N : AEQ 8 := mkQ 8 (ofPerm n₁) with hN
  have hNmem : N ∈ aeBar8 := mkQ_ofPerm_mem_aeBar8 hn₁
  have hNperm : permQ 8 N = n₁ := rfl
  set X' : AEQ 8 := N * X * N⁻¹ with hX'
  have hX'mem : X' ∈ aeBar8 := aeBar8.mul_mem (aeBar8.mul_mem hNmem hX) (aeBar8.inv_mem hNmem)
  have hX'X' : X' * X' = 1 := by
    calc X' * X' = N * (X * X) * N⁻¹ := by rw [hX']; group
      _ = 1 := by rw [hXX]; group
  have hpX' : ∀ z, permQ 8 X' z = n₁ (permQ 8 X (n₁.symm z)) := by
    intro z
    rw [hX', map_mul, map_mul, map_inv, hNperm]
    rfl
  have hfix' : ∀ z, permQ 8 X' z ≠ z := by
    intro z h
    rw [hpX'] at h
    have h2 : permQ 8 X (n₁.symm z) = n₁.symm z := by
      apply n₁.injective
      rw [h, Equiv.apply_symm_apply]
    exact hfix _ h2
  have hpa' : ∀ z, permQ 8 X' z ∈ a₀ ↔ z ∈ a₀ := by
    intro z
    rw [hpX', hn₁a, hpa, ← hn₁a (n₁.symm z), Equiv.apply_symm_apply]
  have hpβ' : ∀ z, permQ 8 X' z ∈ B₀ ↔ z ∈ B₀ := by
    intro z
    rw [hpX', hn₁β, hpβ, ← hn₁β (n₁.symm z), Equiv.apply_symm_apply]
  have hstd := pi_eq_std hfix' hpa' hpβ'
  obtain ⟨ξ, hξ, hξX⟩ := hX'mem
  have hξperm : ∀ z, ξ.perm z = π₀ z := fun z => by
    have : permQ 8 (mkQ 8 ξ) z = π₀ z := by rw [hξX]; exact hstd z
    exact this
  have hξeq : ξ = ⟨ξ.vec, π₀⟩ := Wr.ext rfl (Equiv.ext hξperm)
  have hξξ : ξ * ξ = 1 ∨ ξ * ξ = allOnes 8 := by
    have h1 : mkQ 8 (ξ * ξ) = 1 := by rw [map_mul, hξX, hX'X']
    exact mem_piSub.mp ((QuotientGroup.eq_one_iff _).mp h1)
  obtain ⟨e, he⟩ : ∃ e : ZMod 2, ∀ z, ξ.vec z + ξ.vec (π₀ z) = e := by
    have hsq : ∀ z, (ξ * ξ).vec z = ξ.vec z + ξ.vec (π₀ z) := by
      intro z
      rw [mul_vec, show ξ.perm = π₀ from Equiv.ext hξperm, π₀_symm_eq, π₀_eq]
    rcases hξξ with h | h
    · exact ⟨0, fun z => by rw [← hsq, h]; rfl⟩
    · exact ⟨1, fun z => by rw [← hsq, h]; rfl⟩
  set ω : Wr 8 := ⟨fun z => (ξ.vec 2 + ξ.vec 4) * ind {2, 4} z, g₁⟩ with hω
  have hωmem : ω ∈ aeSub 8 := g₁_mem_aeSub _
  have hcomm : ω * ξ = ξ * ω := by
    have := std_comm_wr he
    rw [← hξeq] at this
    exact this
  set J' : AEQ 8 := mkQ 8 ω with hJ'
  have hJ'mem : J' ∈ aeBar8 := ⟨ω, hωmem, rfl⟩
  have hJ'X' : J' * X' = X' * J' := by
    rw [hJ', ← hξX, ← map_mul, ← map_mul, hcomm]
  have hJ'v : J' * vq a₀ * J'⁻¹ = vq B₀ := by
    rw [conj_vq]
    have : permQ 8 J' = g₁ := rfl
    rw [this, g₁_a₀]
  have hNa : N * vq a * N⁻¹ = vq a₀ := by
    rw [conj_vq, hNperm, map_eq_of_iff hn₁a]
  have hNB : N⁻¹ * vq B₀ * N⁻¹⁻¹ = vq β := by
    rw [conj_vq, map_inv, hNperm]
    have h' : ∀ z, n₁⁻¹ z ∈ β ↔ z ∈ B₀ := fun z => by
      have := hn₁β (n₁⁻¹ z)
      rw [Equiv.Perm.inv_def]
      simpa using this.symm
    rw [Equiv.Perm.inv_def] at *
    exact congrArg vq (map_eq_of_iff (g := n₁.symm) (fun z => h' z))
  refine ⟨N⁻¹ * J' * N, aeBar8.mul_mem (aeBar8.mul_mem (aeBar8.inv_mem hNmem) hJ'mem) hNmem, ?_, ?_⟩
  · calc N⁻¹ * J' * N * X = N⁻¹ * (J' * (N * X * N⁻¹)) * N := by group
      _ = N⁻¹ * (X' * J') * N := by rw [← hX', hJ'X']
      _ = X * (N⁻¹ * J' * N) := by rw [hX']; group
  · calc N⁻¹ * J' * N * vq a * (N⁻¹ * J' * N)⁻¹
        = N⁻¹ * (J' * (N * vq a * N⁻¹) * J'⁻¹) * N⁻¹⁻¹ := by group
      _ = vq β := by rw [hNa, hJ'v, hNB]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
