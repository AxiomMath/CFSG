module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64L

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
  [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal]
include d

theorem bar_r_sq : bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.r_mem_Y = 1 := by
  rw [bar_mul, bar_eq_one_iff, d.c.sq_of_not_mem d.hr d.hru]
  exact d.U_le_X d.c.z_mem_U

theorem bar_t_sq : bar 𝕏(K, J) d.t_mem_Y * bar 𝕏(K, J) d.t_mem_Y = 1 := by
  rw [bar_mul, bar_eq_one_iff, d.c.symm.sq_of_not_mem d.ht d.htv]
  exact d.V_le_X d.c.j_mem_V

omit d in
theorem bar_rho (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t) :
    bar 𝕏(K, J) d.rho_mem_Y = bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y := rfl

theorem bar_mem_closure {y : G} (hy : y ∈ pairNormalizers K J z j) :
    bar 𝕏(K, J) hy ∈ Subgroup.closure {bar 𝕏(K, J) d.r_mem_Y, bar 𝕏(K, J) d.t_mem_Y} := by
  set C := Subgroup.closure ({bar 𝕏(K, J) d.r_mem_Y, bar 𝕏(K, J) d.t_mem_Y} :
    Set (↥(pairNormalizers K J z j) ⧸ (𝕏(K, J)).subgroupOf (pairNormalizers K J z j))) with hC
  let W : Subgroup G := (C.comap (QuotientGroup.mk' _)).map (pairNormalizers K J z j).subtype
  have hmemW : ∀ {g : G} (hg : g ∈ pairNormalizers K J z j), bar 𝕏(K, J) hg ∈ C → g ∈ W :=
    fun hg h => ⟨⟨_, hg⟩, h, rfl⟩
  have hWmem : ∀ {g : G} (hg : g ∈ pairNormalizers K J z j), g ∈ W → bar 𝕏(K, J) hg ∈ C := by
    rintro g hg ⟨y', hy'C, rfl⟩
    exact hy'C
  have hXW : 𝕏(K, J) ≤ W := fun x hx => hmemW (d.c.X_le_Y hx) (by
    rw [(bar_eq_one_iff _ _).mpr hx]
    exact C.one_mem)
  have hrW : Subgroup.zpowers r ≤ W :=
    Subgroup.zpowers_le.mpr (hmemW d.r_mem_Y (Subgroup.subset_closure (by simp)))
  have htW : Subgroup.zpowers t ≤ W :=
    Subgroup.zpowers_le.mpr (hmemW d.t_mem_Y (Subgroup.subset_closure (by simp)))
  have hYW : pairNormalizers K J z j ≤ W :=
    d.c.Y_le.trans (sup_le (sup_le hXW (d.R_le.trans (sup_le hXW hrW)))
      (d.T_le.trans (sup_le hXW htW)))
  exact hWmem hy (hYW hy)

theorem normal_form
    (q : ↥(pairNormalizers K J z j) ⧸ (𝕏(K, J)).subgroupOf (pairNormalizers K J z j)) :
    ∃ i : ℤ, q = bar 𝕏(K, J) d.rho_mem_Y ^ i ∨
      q = bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.rho_mem_Y ^ i := by
  have hgen : ∀ q, q ∈ Subgroup.closure {bar 𝕏(K, J) d.r_mem_Y, bar 𝕏(K, J) d.t_mem_Y} := by
    intro q
    obtain ⟨g, hg, rfl⟩ := exists_bar_eq _ q
    exact d.bar_mem_closure hg
  rw [d.bar_rho]
  exact dihedral_normal_form d.bar_r_sq d.bar_t_sq hgen q

theorem bar_r_conj_zpow (i : ℤ) : bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.rho_mem_Y ^ i *
    (bar 𝕏(K, J) d.r_mem_Y)⁻¹ = (bar 𝕏(K, J) d.rho_mem_Y ^ i)⁻¹ := by
  rw [d.bar_rho]
  exact dihedral_conj_zpow d.bar_r_sq d.bar_t_sq i

theorem exists_of_conj_z {y : G} (hy : y ∈ pairNormalizers K J z j) (hyz : y * z * y⁻¹ = z) :
    ∃ k : ℤ, bar 𝕏(K, J) hy = bar 𝕏(K, J) d.rho_mem_Y ^ (3 * k) ∨
      bar 𝕏(K, J) hy = bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.rho_mem_Y ^ (3 * k) := by
  obtain ⟨i, h | h⟩ := d.normal_form (bar 𝕏(K, J) hy)
  · have h' := h
    rw [bar_zpow] at h'
    have e := conj_eq_of_bar_eq _ hy _ h' d.c.X_le_centralizer_z
    rw [hyz] at e
    obtain ⟨k, rfl⟩ := (d.c.conj_rho_zpow_z_eq_iff d.hr d.hru d.ht d.htv i).mp e.symm
    exact ⟨k, Or.inl h⟩
  · have h' := h
    rw [bar_zpow, bar_mul] at h'
    have e := conj_eq_of_bar_eq _ hy _ h' d.c.X_le_centralizer_z
    rw [hyz] at e
    have e2 : (r * t) ^ i * z * ((r * t) ^ i)⁻¹ = z := by
      calc (r * t) ^ i * z * ((r * t) ^ i)⁻¹ =
            r⁻¹ * ((r * (r * t) ^ i) * z * (r * (r * t) ^ i)⁻¹) * r := by group
        _ = r⁻¹ * z * r := by rw [← e]
        _ = r⁻¹ * (r * z * r⁻¹) * r := by rw [d.c.conj_z d.hr]
        _ = z := by group
    obtain ⟨k, rfl⟩ := (d.c.conj_rho_zpow_z_eq_iff d.hr d.hru d.ht d.htv i).mp e2
    exact ⟨k, Or.inr h⟩

theorem exists_of_conj_z_j {y : G} (hy : y ∈ pairNormalizers K J z j) (hyz : y * z * y⁻¹ = z)
    (hyj : y * j * y⁻¹ = j) : ∃ k : ℤ, bar 𝕏(K, J) hy = bar 𝕏(K, J) d.rho_mem_Y ^ (3 * k) := by
  obtain ⟨k, h | h⟩ := d.exists_of_conj_z hy hyz
  · exact ⟨k, h⟩
  · exfalso
    rw [bar_zpow, bar_mul] at h
    have e := conj_eq_of_bar_eq _ hy _ h d.c.X_le_centralizer_j
    rw [hyj] at e
    have e2 : (r * (r * t) ^ (3 * k)) * j * (r * (r * t) ^ (3 * k))⁻¹ = z * j := by
      calc (r * (r * t) ^ (3 * k)) * j * (r * (r * t) ^ (3 * k))⁻¹ =
            r * ((r * t) ^ (3 * k) * j * ((r * t) ^ (3 * k))⁻¹) * r⁻¹ := by group
        _ = z * j := by rw [d.conj_rho_zpow_three_j, d.c.conj_j_of_not_mem d.hr d.hru]
    exact d.c.zj_ne_j (e2.symm.trans e.symm)

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
