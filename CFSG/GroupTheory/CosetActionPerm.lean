module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.GroupTheory

theorem exists_hom_perm_ker_eq_normalCore {X : Type*} [Group X] [Finite X] (U P : Subgroup X)
    {n : ℕ} (hidx : U.relIndex P = n) :
    ∃ (ρ : ↥P →* Equiv.Perm (Fin n)) (i₀ : Fin n),
      ρ.ker = (U.subgroupOf P).normalCore ∧ ∀ u : ↥P, (u : X) ∈ U → ρ u i₀ = i₀ := by
  classical
  set S : Subgroup ↥P := U.subgroupOf P with hS
  have hcard : Nat.card (↥P ⧸ S) = n := by rw [← Subgroup.index_eq_card]; exact hidx
  let eqv : (↥P ⧸ S) ≃ Fin n := (Finite.equivFin _).trans (finCongr hcard)
  let ρ : ↥P →* Equiv.Perm (Fin n) :=
    (eqv.permCongrHom).toMonoidHom.comp (MulAction.toPermHom ↥P (↥P ⧸ S))
  have hker : ρ.ker = S.normalCore := by
    rw [Subgroup.normalCore_eq_ker]
    ext x
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  refine ⟨ρ, eqv (QuotientGroup.mk 1), hker, fun u hu => ?_⟩
  have hmk : (u • (QuotientGroup.mk 1 : ↥P ⧸ S)) = QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    simpa [hS, Subgroup.mem_subgroupOf] using hu
  simp [ρ, Equiv.permCongrHom, hmk]

theorem perm3_eq_one_of_pow_three {σ : Equiv.Perm (Fin 3)} {i : Fin 3} (h3 : σ ^ 3 = 1)
    (hi : σ i = i) : σ = 1 := by
  revert σ i
  decide

theorem perm3_sq_eq_one {σ : Equiv.Perm (Fin 3)} {i : Fin 3} (hi : σ i = i) : σ ^ 2 = 1 := by
  revert σ i
  decide

theorem perm3_eq_of_fixed {σ τ : Equiv.Perm (Fin 3)} {i : Fin 3} (hσ : σ i = i) (hτ : τ i = i)
    (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) : σ = τ := by
  revert σ τ i
  decide

theorem perm3_inv_conj {τ κ : Equiv.Perm (Fin 3)} (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hκ3 : κ ^ 3 = 1) : τ * κ * τ⁻¹ * κ = 1 := by
  revert τ κ
  decide

theorem perm3_conj_eq_or_eq_inv (σ : Equiv.Perm (Fin 3)) {κ : Equiv.Perm (Fin 3)}
    (hκ3 : κ ^ 3 = 1) : σ * κ * σ⁻¹ = κ ∨ σ * κ * σ⁻¹ = κ⁻¹ := by
  revert σ κ
  decide

theorem le_normalizer_zpowers_sup_of_perm3 {G : Type*} [Group G] {P Q : Subgroup G}
    (ρ₁ ρ₂ : ↥P →* Equiv.Perm (Fin 3))
    (hker : ∀ x : ↥P, ρ₁ x = 1 → ρ₂ x = 1 → (x : G) ∈ Q)
    (hQn : P ≤ Subgroup.normalizer (Q : Set G)) {g : ↥P} (hg1 : ρ₁ g = 1) (hg3 : g ^ 3 = 1) :
    P ≤ Subgroup.normalizer ((Subgroup.zpowers (g : G) ⊔ Q : Subgroup G) : Set G) := by
  have hκ3 : ρ₂ g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have hconj_mem : ∀ y : ↥P,
      (y : G) * (g : G) * (y : G)⁻¹ ∈ (Subgroup.zpowers (g : G) ⊔ Q : Subgroup G) := by
    intro y
    let c : ↥P := y * g * y⁻¹
    have hcval : (c : G) = (y : G) * (g : G) * (y : G)⁻¹ := by
      show ((y * g * y⁻¹ : ↥P) : G) = _
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have hc1 : ρ₁ c = 1 := by
      show ρ₁ (y * g * y⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hg1]
      simp
    have hc2 : ρ₂ c = ρ₂ y * ρ₂ g * (ρ₂ y)⁻¹ := by
      show ρ₂ (y * g * y⁻¹) = _
      rw [map_mul, map_mul, map_inv]
    rw [← hcval]
    rcases perm3_conj_eq_or_eq_inv (ρ₂ y) hκ3 with h | h
    · have hz : ((g⁻¹ * c : ↥P) : G) ∈ Q := by
        refine hker (g⁻¹ * c) ?_ ?_
        · show ρ₁ (g⁻¹ * c) = 1
          rw [map_mul, map_inv, hg1, hc1]
          simp
        · show ρ₂ (g⁻¹ * c) = 1
          rw [map_mul, map_inv, hc2, h]
          simp
      have heq : (c : G) = (g : G) * ((g⁻¹ * c : ↥P) : G) := by
        rw [show (c : G) = ((g * (g⁻¹ * c) : ↥P) : G) from
          congrArg Subtype.val (show c = g * (g⁻¹ * c) from (mul_inv_cancel_left g c).symm)]
        rw [Subgroup.coe_mul]
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers (g : G)))
        (Subgroup.mem_sup_right hz)
    · have hz : ((g * c : ↥P) : G) ∈ Q := by
        refine hker (g * c) ?_ ?_
        · show ρ₁ (g * c) = 1
          rw [map_mul, hg1, hc1, one_mul]
        · show ρ₂ (g * c) = 1
          rw [map_mul, hc2, h]
          simp
      have heq : (c : G) = (g : G)⁻¹ * ((g * c : ↥P) : G) := by
        rw [show (c : G) = ((g⁻¹ * (g * c) : ↥P) : G) from
          congrArg Subtype.val (show c = g⁻¹ * (g * c) from (inv_mul_cancel_left g c).symm)]
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heq]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers (g : G))))
        (Subgroup.mem_sup_right hz)
  have hconj : ∀ y : ↥P, (Subgroup.zpowers (g : G) ⊔ Q : Subgroup G) ≤
      (Subgroup.zpowers (g : G) ⊔ Q : Subgroup G).comap
        (MulAut.conj (y : G)).toMonoidHom := by
    intro y
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      show MulAut.conj (y : G) (g : G) ∈ _
      simpa [MulAut.conj_apply] using hconj_mem y
    · intro q hq
      exact Subgroup.mem_sup_right ((Subgroup.le_normalizer_iff.mp hQn) (y : G) y.2 q hq)
  refine Subgroup.le_normalizer_iff.mpr ?_
  intro x hx m hm
  have := Subgroup.mem_comap.mp (hconj ⟨x, hx⟩ hm)
  simpa [MulAut.conj_apply] using this

end CFSG.GroupTheory
