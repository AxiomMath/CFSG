module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILe

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit OutInv

variable {k : Type} [Field k]

theorem eq_one_or_eq_of_comm_rowOJ [Fintype k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (hq : Fintype.card k % 2 = 1) (δ : kˣ) (h2 : (2 : k) ≠ 0)
    (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k)) (R : GL (Fin 4) k)
    (hR : (rowOHom δ ψ).range ≤ CatalogueBGraphForm.isometryGroup 4 k R)
    (x : MulAut (projectiveSL 4 k))
    (hx : ∀ g, Commute x (conjAut 4 k (rowOHom δ ψ g))) :
    x = 1 ∨ x = conjAut 4 k R⁻¹ * dualAut 4 k := by
  have hβ : ∀ g, Commute (conjAut 4 k R⁻¹ * dualAut 4 k) (conjAut 4 k (rowOHom δ ψ g)) :=
    fun g => by
      have h1 := isometryGroup_le_comap_centralizer (m := 4) (k := k) R⁻¹
      rw [inv_inv] at h1
      have h3 := h1 (hR ⟨g, rfl⟩)
      rw [mem_comap, mem_centralizer_singleton_iff] at h3
      exact h3.symm
  have hinner : ∀ (B : GL (Fin 4) k) (σ : k ≃+* k),
      (∀ g, Commute (conjAut 4 k B * fieldAut 4 k σ) (conjAut 4 k (rowOHom δ ψ g))) →
        conjAut 4 k B * fieldAut 4 k σ = 1 := by
    intro B σ hB
    have hσ := fieldAut_eq_one_of_comm hq δ h2 ψ B σ fun g => (hB g).eq
    subst hσ
    rw [map_one, mul_one] at hB ⊢
    exact conjAut_eq_one_of_comm (p := p) δ h2 ψ B fun g => (hB g).eq
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (by norm_num : 3 ≤ 4)
  obtain ⟨B, σ, ε, hε, rfl⟩ := hform x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · left
    simp only [pow_zero, mul_one] at hx ⊢
    exact hinner B σ hx
  · right
    simp only [pow_one] at hx ⊢
    have hdd : dualAut 4 k * dualAut 4 k = 1 :=
      (standard_automorphism_transport (K := k) (n := 4)).2.2.2.1
    have hy : (conjAut 4 k R⁻¹ * dualAut 4 k)⁻¹ *
        (conjAut 4 k B * fieldAut 4 k σ * dualAut 4 k) =
          conjAut 4 k (GeneralLinearGroup.inverseTranspose (R * B)) * fieldAut 4 k σ := by
      rw [_root_.mul_inv_rev, dualAut_inv, map_inv, inv_inv]
      calc dualAut 4 k * conjAut 4 k R * (conjAut 4 k B * fieldAut 4 k σ * dualAut 4 k)
          = dualAut 4 k * conjAut 4 k (R * B) * fieldAut 4 k σ * dualAut 4 k := by
            rw [map_mul]; group
        _ = conjAut 4 k (GeneralLinearGroup.inverseTranspose (R * B)) *
              (dualAut 4 k * fieldAut 4 k σ) * dualAut 4 k := by
            rw [LinearFlag.dualAut_mul_conjAut]; group
        _ = conjAut 4 k (GeneralLinearGroup.inverseTranspose (R * B)) * fieldAut 4 k σ *
              (dualAut 4 k * dualAut 4 k) := by
            rw [LinearFlag.dualAut_mul_fieldAut]; group
        _ = _ := by rw [hdd, mul_one]
    have h1 := hinner _ σ fun g => by
      have := (hβ g).inv_left.mul_left (hx g)
      rwa [hy] at this
    rw [← hy] at h1
    exact (inv_mul_eq_one.mp h1).symm

theorem outer_cent_L4 (F : Type) [Field F] [Fintype F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hF : Fintype.card F = p ^ f) {φ : MulAut (projectiveSL 4 F)} (hφ2 : φ ^ 2 = 1)
    (hφ : φ ∉ (conjAut 4 F).range) {J' : Subgroup (projectiveSL 4 F)} (hJφ : J' ≤ fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (fixSub φ)))
    (hJm : Blueprint.LieModel (↥J' ⧸ center ↥J') .PSL 2 p (2 * f))
    (ψ' : MulAut (projectiveSL 4 F)) (hψ : ∀ x ∈ J', ψ' x = x) : ψ' ∈ zpowers φ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow hF
  have hk : Nat.card F = p ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hq : Fintype.card F % 2 = 1 := by
    rw [hF]
    exact Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  obtain ⟨δ, -, ψ, R, C, -, -, hφC, -, -, hL, hiso, -⟩ :=
    selectorRowO_of_component hp hp2 hf hk hφ2 hφ hJφ hJ hJm
  rw [MonoidHom.id_apply] at hφC
  rw [Subgroup.map_id] at hL
  set χ := conjAut 4 F C with hχ
  have hcomm : ∀ g, Commute (χ⁻¹ * ψ' * χ) (conjAut 4 F (rowOHom δ ψ g)) := by
    intro g
    have hmem : χ * conjAut 4 F (rowOHom δ ψ g) * χ⁻¹ ∈
        J'.map (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)) := by
      rw [hL]
      exact ⟨conjAut 4 F (rowOHom δ ψ g), ⟨g, rfl⟩, rfl⟩
    obtain ⟨j, hj, hje⟩ := hmem
    have hc : Commute ψ' (MulAut.conj j) := by
      have h1 : ψ' * MulAut.conj j * ψ'⁻¹ = MulAut.conj (ψ' j) := CSL.mul_conj_mul_inv ψ' j
      rw [hψ j hj] at h1
      calc ψ' * MulAut.conj j = ψ' * MulAut.conj j * ψ'⁻¹ * ψ' := by group
        _ = MulAut.conj j * ψ' := by rw [h1]
    have h3 := hc.map (MulAut.conj χ⁻¹).toMonoidHom
    have e1 : (MulAut.conj χ⁻¹).toMonoidHom ψ' = χ⁻¹ * ψ' * χ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e2 : (MulAut.conj χ⁻¹).toMonoidHom (MulAut.conj j) = conjAut 4 F (rowOHom δ ψ g) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hje, inv_inv]
      group
    rwa [e1, e2] at h3
  rcases eq_one_or_eq_of_comm_rowOJ (p := p) hq δ h2 ψ R hiso _ hcomm with h | h
  · have : ψ' = 1 := by
      calc ψ' = χ * (χ⁻¹ * ψ' * χ) * χ⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this]
    exact one_mem _
  · have : ψ' = φ := by
      calc ψ' = χ * (χ⁻¹ * ψ' * χ) * χ⁻¹ := by group
        _ = φ := by rw [h, hφC]
    rw [this]
    exact mem_zpowers φ

end OIL

end CFSG.ComponentClassification.CatFactsL4U4
