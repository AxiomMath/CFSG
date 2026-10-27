module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] {x₁ x₂ lam rho : G} {P : Subgroup G}

private theorem baseGrp_map_conj_le (h1 : rho * x₁ * rho⁻¹ = x₁⁻¹ * x₂)
    (h2 : rho * x₂ * rho⁻¹ = x₁⁻¹) :
    (baseGrp x₁ x₂).map (MulAut.conj rho : G →* G) ≤ baseGrp x₁ x₂ := by
  have hmap : (baseGrp x₁ x₂).map (MulAut.conj rho : G →* G) =
      closure ({rho * x₁ * rho⁻¹, rho * x₂ * rho⁻¹} : Set G) := by
    rw [baseGrp, MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [hmap, Subgroup.closure_le]
  rintro y (hy : y ∈ ({rho * x₁ * rho⁻¹, rho * x₂ * rho⁻¹} : Set G))
  rcases hy with rfl | rfl
  · rw [h1]
    exact Subgroup.mul_mem (baseGrp x₁ x₂)
      (Subgroup.inv_mem (baseGrp x₁ x₂) (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  · rw [h2]
    exact Subgroup.inv_mem (baseGrp x₁ x₂) (Subgroup.subset_closure (by simp))

private theorem conj_inv_x₂ (h2 : rho * x₂ * rho⁻¹ = x₁⁻¹) :
    rho * x₂⁻¹ * rho⁻¹ = x₁ := by
  have h := congrArg (fun t : G => t⁻¹) h2
  simpa [mul_inv_rev, mul_assoc] using h

private theorem conj_inv_x₁ (h1 : rho * x₁ * rho⁻¹ = x₁⁻¹ * x₂) :
    rho * x₁⁻¹ * rho⁻¹ = x₂⁻¹ * x₁ := by
  have h := congrArg (fun t : G => t⁻¹) h1
  simpa [mul_inv_rev, mul_assoc] using h

private theorem baseGrp_map_conj_ge (h1 : rho * x₁ * rho⁻¹ = x₁⁻¹ * x₂)
    (h2 : rho * x₂ * rho⁻¹ = x₁⁻¹) :
    baseGrp x₁ x₂ ≤ (baseGrp x₁ x₂).map (MulAut.conj rho : G →* G) := by
  have hx₁ : x₁ ∈ (baseGrp x₁ x₂).map (MulAut.conj rho : G →* G) := by
    refine Subgroup.mem_map.mpr ⟨x₂⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · change (MulAut.conj rho) x₂⁻¹ = x₁
      rw [MulAut.conj_apply, conj_inv_x₂ h2]
  have hx₂ : x₂ ∈ (baseGrp x₁ x₂).map (MulAut.conj rho : G →* G) := by
    refine Subgroup.mem_map.mpr ⟨x₂⁻¹ * x₁, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))
    · change (MulAut.conj rho) (x₂⁻¹ * x₁) = x₂
      rw [map_mul, MulAut.conj_apply, MulAut.conj_apply, conj_inv_x₂ h2, h1]
      group
  rw [baseGrp, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with h | h
  · rw [h]; exact hx₁
  · rw [h]; exact hx₂

private theorem baseGrp_map_conj_eq (h1 : rho * x₁ * rho⁻¹ = x₁⁻¹ * x₂)
    (h2 : rho * x₂ * rho⁻¹ = x₁⁻¹) :
    (baseGrp x₁ x₂).map (MulAut.conj rho : G →* G) = baseGrp x₁ x₂ :=
  le_antisymm (baseGrp_map_conj_le h1 h2) (baseGrp_map_conj_ge h1 h2)

private theorem conj_rho_eq_self_of_mem (hP : ∀ a ∈ P, rho * a = a * rho) {a : G}
    (ha : a ∈ P) : (MulAut.conj rho : G →* G) a = a := by
  change (MulAut.conj rho) a = a
  rw [MulAut.conj_apply, hP a ha, mul_assoc, mul_inv_cancel, mul_one]

private theorem map_conj_eq_self_of_commute (hP : ∀ a ∈ P, rho * a = a * rho) :
    P.map (MulAut.conj rho : G →* G) = P := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    rw [Subgroup.mem_comap]
    rwa [conj_rho_eq_self_of_mem hP ha]
  · intro a ha
    exact Subgroup.mem_map.mpr ⟨a, ha, conj_rho_eq_self_of_mem hP ha⟩

private theorem commutator_mul_left_of_commute {a b c : G} (hab : Commute a b)
    (hac : Commute a c) : ⁅a * b, c⁆ = ⁅b, c⁆ := by
  have h1 : ⁅a, c⁆ = 1 := hac.commutator_eq
  rw [commutatorElement_mul_left_eq_conj_mul, h1, mul_one]
  rw [conjugate_commutatorElement, hab.eq, hac.eq]
  group

private theorem commutator_mul_left_of_commute_eq {a b c : G} (hab : Commute a b)
    (hac : Commute a c) : ⁅a * b, c⁆ = b * (c * b⁻¹ * c⁻¹) := by
  rw [commutator_mul_left_of_commute hab hac, commutatorElement_def]
  group

theorem rho_mem_normalizer_sup_baseGrp [Finite G] (h1 : rho * x₁ * rho⁻¹ = x₁⁻¹ * x₂)
    (h2 : rho * x₂ * rho⁻¹ = x₁⁻¹) (hP : ∀ a ∈ P, rho * a = a * rho) :
    rho ∈ normalizer ((P ⊔ baseGrp x₁ x₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    map_conj_eq_self_of_commute hP, baseGrp_map_conj_eq h1 h2]

theorem sup_baseGrp_inf_centralizer_rho
    (hPA : ∀ a ∈ P, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a) (hP : ∀ a ∈ P, rho * a = a * rho)
    (hcr : ∀ w ∈ baseGrp x₁ x₂, rho * w = w * rho → w = 1) :
    (P ⊔ baseGrp x₁ x₂) ⊓ centralizer ({rho} : Set G) = P := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxW, hxC⟩ := hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hPA).mp hxW
    have hxcomm : (a * b) * rho = rho * (a * b) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    have harho : a * rho = rho * a := (hP a ha).symm
    have hbcomm : b * rho = rho * b := by
      have h1 : a * (b * rho) = a * (rho * b) := by
        calc a * (b * rho) = (a * b) * rho := by group
          _ = rho * (a * b) := hxcomm
          _ = (rho * a) * b := by group
          _ = (a * rho) * b := by rw [harho]
          _ = a * (rho * b) := by group
      exact mul_left_cancel h1
    have hb1 : b = 1 := hcr b hb hbcomm.symm
    rw [hb1, mul_one]
    exact ha
  · intro x hx
    exact ⟨Subgroup.mem_sup_left hx,
      Subgroup.mem_centralizer_singleton_iff.mpr (hP x hx).symm⟩

theorem commutator_sup_baseGrp_rho (h : WreathRel x₁ x₂ lam) (h1 : rho * x₁ * rho⁻¹ = x₁⁻¹ * x₂)
    (h2 : rho * x₂ * rho⁻¹ = x₁⁻¹) (hPA : ∀ a ∈ P, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a)
    (hP : ∀ a ∈ P, rho * a = a * rho) :
    ⁅P ⊔ baseGrp x₁ x₂, zpowers rho⁆ = baseGrp x₁ x₂ := by
  have hN : rho ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact baseGrp_map_conj_eq h1 h2
  have hNk : ∀ k : ℤ, rho ^ k ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    fun k => Subgroup.zpow_mem _ hN k
  have hcomm_x₂ : ⁅x₂, rho⁆ = x₂ * x₁ := by
    rw [commutatorElement_def]
    rw [show x₂ * rho * x₂⁻¹ * rho⁻¹ = x₂ * (rho * x₂⁻¹ * rho⁻¹) from by group,
      conj_inv_x₂ h2]
  have hcomm_x₁ : ⁅x₁, rho⁆ = x₁ ^ 2 * x₂⁻¹ := by
    rw [commutatorElement_def]
    rw [show x₁ * rho * x₁⁻¹ * rho⁻¹ = x₁ * (rho * x₁⁻¹ * rho⁻¹) from by group,
      conj_inv_x₁ h1]
    have hx2inv_comm : x₂⁻¹ * x₁ = x₁ * x₂⁻¹ := by
      have hc : Commute x₁ x₂ := h.comm
      exact hc.inv_right.eq.symm
    rw [hx2inv_comm, pow_two]
    group
  have hx2x1sq : x₂ * x₁ ^ 2 = x₁ ^ 2 * x₂ := by
    have hc : Commute x₂ x₁ := h.comm.symm
    exact (hc.pow_right 2).eq
  have hprod : (x₂ * x₁) * (x₁ ^ 2 * x₂⁻¹) = x₁ ^ 3 := by
    rw [h.comm.symm]
    rw [show (x₁ * x₂) * (x₁ ^ 2 * x₂⁻¹) = x₁ * (x₂ * x₁ ^ 2) * x₂⁻¹ from by group,
      hx2x1sq]
    group
  have hx1four : x₁ ^ 4 = 1 := by
    simpa [h.ord_x₁] using pow_orderOf_eq_one x₁
  have hx1_eq : (x₁ ^ 3) ^ 3 = x₁ := by
    rw [← pow_mul, show (3 * 3 : ℕ) = 4 * 2 + 1 from by norm_num, pow_add, pow_mul, hx1four]
    simp
  have hx2_eq : x₁⁻¹ * (x₂ * x₁) = x₂ := by
    rw [← h.comm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hx1W : x₁ ∈ P ⊔ baseGrp x₁ x₂ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hx2W : x₂ ∈ P ⊔ baseGrp x₁ x₂ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hrho : rho ∈ zpowers rho := Subgroup.mem_zpowers rho
  have hx2x1 : x₂ * x₁ ∈ ⁅P ⊔ baseGrp x₁ x₂, zpowers rho⁆ := by
    have hmem := Subgroup.commutator_mem_commutator (H₁ := P ⊔ baseGrp x₁ x₂)
      (H₂ := zpowers rho) hx2W hrho
    rwa [hcomm_x₂] at hmem
  have hx1sqx2inv : x₁ ^ 2 * x₂⁻¹ ∈ ⁅P ⊔ baseGrp x₁ x₂, zpowers rho⁆ := by
    have hmem := Subgroup.commutator_mem_commutator (H₁ := P ⊔ baseGrp x₁ x₂)
      (H₂ := zpowers rho) hx1W hrho
    rwa [hcomm_x₁] at hmem
  have hx1cubed : x₁ ^ 3 ∈ ⁅P ⊔ baseGrp x₁ x₂, zpowers rho⁆ := by
    have hmem := Subgroup.mul_mem _ hx2x1 hx1sqx2inv
    rwa [hprod] at hmem
  have hx1 : x₁ ∈ ⁅P ⊔ baseGrp x₁ x₂, zpowers rho⁆ := by
    have hmem := Subgroup.pow_mem _ hx1cubed 3
    rwa [hx1_eq] at hmem
  have hx2 : x₂ ∈ ⁅P ⊔ baseGrp x₁ x₂, zpowers rho⁆ := by
    have hmem := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx1) hx2x1
    rwa [hx2_eq] at hmem
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hPA).mp hg₁
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
    have hab : Commute a b := hPA a ha b hb
    have har : Commute a (rho ^ k) :=
      (show Commute a rho from (hP a ha).symm).zpow_right k
    rw [commutator_mul_left_of_commute_eq hab har]
    have hb' : rho ^ k * b⁻¹ * (rho ^ k)⁻¹ ∈ baseGrp x₁ x₂ := by
      have hmem := (Subgroup.mem_normalizer_iff (H := baseGrp x₁ x₂)).mp (hNk k) b
      have hb'' : rho ^ k * b * (rho ^ k)⁻¹ ∈ baseGrp x₁ x₂ := hmem.mp hb
      have heq : rho ^ k * b⁻¹ * (rho ^ k)⁻¹ = (rho ^ k * b * (rho ^ k)⁻¹)⁻¹ := by
        group
      rw [heq]
      exact Subgroup.inv_mem _ hb''
    exact Subgroup.mul_mem _ hb hb'
  · rw [baseGrp, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]; exact hx1
    · rw [h]; exact hx2

end CFSG.OddStandard.SmallF3.HarrisU33
