module

public import CFSG.ClassicalInvolution.AschTight.TzConj

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem exists_abelian_of_isWreathed [Finite G] {R V J : Subgroup G} {t : G}
    (hVN : V ≤ Subgroup.normalizer (R : Set G)) (hVJ : V ≤ J)
    (hsq : ∃ w ∈ V, w * w = t) (hwr : IsWreathed (R ⊔ V))
    (hJ : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hRJ : R ⊓ J = ⊥) :
    ∃ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
      Nat.card R ≤ 2 * Nat.card ↥(R ⊓ B) ∧ ∀ v ∈ V, ∀ y ∈ R ⊓ B, v * y = y * v := by
  obtain ⟨a, c, b, -, -, hac, -, hb2, hbac, hbca, hcl⟩ := hwr
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, Subgroup.zpowers a ⊔ Subgroup.zpowers c = B := ⟨_, rfl⟩
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_sup_zpowers hac (hB ▸ hx) (hB ▸ hy)
  have hconj : ∀ i j : ℤ, b * (a ^ i * c ^ j) * b⁻¹ = c ^ i * a ^ j := by
    intro i j
    rw [show b * (a ^ i * c ^ j) * b⁻¹ = (b * a * b⁻¹) ^ i * (b * c * b⁻¹) ^ j by
      rw [conj_zpow, conj_zpow]; group, hbac, hbca]
  have hbB : b ∈ Subgroup.normalizer (B : Set G) := by
    refine mem_normalizer_of_mul_self_eq_one hb2 fun x hx => ?_
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac (hB ▸ hx)
    rw [hconj, ← hB]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _))
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _))
  have hP : R ⊔ V = B ⊔ Subgroup.zpowers b := by
    rw [← hcl, ← hB, Set.insert_eq, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
      sup_assoc]
  have hPcard : Nat.card ↥(R ⊔ V) ≤ Nat.card B * 2 := by
    have e : Nat.card ↥(R ⊔ V) =
        Nat.card ↥(((B ⊔ Subgroup.zpowers b : Subgroup G) : Set G)) := by rw [hP]; rfl
    rw [e, Subgroup.coe_mul_of_right_le_normalizer_left B _ (Subgroup.zpowers_le.mpr hbB)]
    refine Set.natCard_mul_le.trans (Nat.mul_le_mul_left _ ?_)
    change Nat.card ↥(Subgroup.zpowers b) ≤ 2
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hb2))
  have hBP : B ≤ R ⊔ V := by
    rw [hP]
    exact le_sup_left
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := R ⊔ V)
  rw [inf_eq_left.mpr hBP] at h1
  have hne : B.relIndex (R ⊔ V) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hidx : B.relIndex (R ⊔ V) ≤ 2 := by
    have hpos : 0 < Nat.card B := Nat.card_pos
    nlinarith
  have hidxR : B.relIndex R ≤ 2 := (Subgroup.relIndex_le_of_le_right le_sup_left hne).trans hidx
  obtain ⟨w, hwV, hwt⟩ := hsq
  have htB : t ∈ B :=
    hwt ▸ mul_self_mem_of_mem_sup_zpowers hb2 hbB (hP ▸ Subgroup.mem_sup_right hwV)
  refine ⟨B, hBc, ?_, ?_⟩
  · have h2 := Subgroup.relIndex_mul_card (H := B) (K := R)
    rw [inf_comm] at h2
    nlinarith
  · intro v hv y hy
    have hyt : y ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hBc y hy.2 t htB
    have hyJ := hJ hyt
    have hc : y * v * y⁻¹ * v⁻¹ ∈ R ⊓ J := by
      refine ⟨?_, ?_⟩
      · have h3 : v * y⁻¹ * v⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hVN hv) _).mp (R.inv_mem hy.1)
        have e : y * v * y⁻¹ * v⁻¹ = y * (v * y⁻¹ * v⁻¹) := by group
        rw [e]
        exact R.mul_mem hy.1 h3
      · have h3 : y * v * y⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hyJ _).mp (hVJ hv)
        exact J.mul_mem h3 (J.inv_mem (hVJ hv))
    rw [hRJ, Subgroup.mem_bot] at hc
    calc v * y = (y * v * y⁻¹ * v⁻¹)⁻¹ * (y * v) := by group
      _ = y * v := by rw [hc, inv_one, one_mul]

end CFSG.ClassicalInvolution.Disconnected.AschTight
