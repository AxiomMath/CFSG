module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.LayerSimple
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CompPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.PerfectAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotCores
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotR
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotYBasic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C] {c : CInv C} {t : C} {R J K O Y : Subgroup C}

theorem bar_R_le_layer (hC : CCore c) (hR : RData c R) : c.bar R ≤ CFSG.layer c.Qt := by
  exact le_layer_of_selfCentralizing (pPrimeCore_Qt_eq_bot hC) (pCore_Qt_eq_bot hC)
    (bar_R_isPGroup hR) (bar_R_ne_bot hR) (bar_R_cent hR) (bar_R_irr hR)

theorem bar_R_selfCentAbelian (hC : CCore c) (hR : RData c R) :
    SelfCentAbelian (c.bar R) := by
  exact ⟨bar_R_comm hR, bar_R_cent hR, bar_R_le_layer hC hR⟩

theorem card_components_Qt_le (hC : CCore c) (hR : RData c R) :
    Nat.card {K : Subgroup c.Qt // CFSG.IsComponent K} ≤ 12 := by
  exact card_components_le (pPrimeCore_Qt_eq_bot hC) (pCore_Qt_eq_bot hC)
    (bar_R_selfCentAbelian hC hR) (le_of_eq (bar_R_card hR))

theorem bar_Y_normalizes_components (hC : CCore c) (hR : RData c R) (hJ : JData c t R J)
    (hK : KDataC c t R J K O Y) (hF : U42Facts) :
    ∀ K' : Subgroup c.Qt, CFSG.IsComponent K' → ∀ y ∈ c.bar Y, ∀ k ∈ K', y * k * y⁻¹ ∈ K' := by
  obtain ⟨X, hXgrp, π, hπsurj, hπker, hX⟩ := hK.quot
  letI : Group X := hXgrp
  let ψ : ↥K →* c.Qt := c.qmap.comp K.subtype
  let Y' : Subgroup ↥K := Y.subgroupOf K
  have hperm : ∀ n : ℕ, n ≤ 26 → ∀ φ : X →* Equiv.Perm (Fin n),
      ∀ a ∈ commutator X, φ a = 1 := hF.perm X hX
  have hker : ∀ k ∈ π.ker, ∀ K' : Subgroup c.Qt, CFSG.IsComponent K' → ∀ m ∈ K',
      ψ k * m * (ψ k)⁻¹ ∈ K' := by
    intro k hk K' hK' m hm
    have hkO : (k : C) ∈ O := by
      rw [hπker] at hk
      exact Subgroup.mem_subgroupOf.mp hk
    have hψ : ψ k ∈ c.bar O := Subgroup.mem_map.mpr ⟨(k : C), hkO, rfl⟩
    have hle : c.bar O ≤ CFSG.layer c.Qt :=
      le_trans (bar_O_le_bar_R hK) (bar_R_le_layer hC hR)
    have hnorm : ψ k ∈ normalizer (K' : Set c.Qt) :=
      CFSG.LocalCores.layer_le_normalizer hK' (hle hψ)
    exact (Subgroup.mem_normalizer_iff.mp hnorm m).mp hm
  have hY' : ⁅Y', Y'⁆ = Y' := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hK.Y_le, hK.Y_perfect]
  have hn : Nat.card {K : Subgroup c.Qt // CFSG.IsComponent K} ≤ 26 :=
    le_trans (card_components_Qt_le hC hR) (by norm_num)
  have hmain := normalizes_components_of_perfect hperm π hπsurj ψ hker hn hY'
  intro K' hK' y hy k hk
  rcases Subgroup.mem_map.mp hy with ⟨y0, hy0Y, rfl⟩
  have hy' : (⟨y0, hK.Y_le hy0Y⟩ : ↥K) ∈ Y' := by
    rw [Subgroup.mem_subgroupOf]
    exact hy0Y
  have h := hmain ⟨y0, hK.Y_le hy0Y⟩ hy' K' hK' k hk
  simpa [ψ] using h

theorem bar_Y_hlat1 (hR : RData c R) (hJ : JData c t R J) (hK : KDataC c t R J K O Y) :
    ∀ M : Subgroup c.Qt, M ≤ c.bar R → (∀ y ∈ c.bar Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M) →
      Nat.card ↥M ≤ 2 ^ 7 → ∀ y ∈ c.bar Y, ∀ m ∈ M, y * m = m * y := by
  intro M hM hMn hMc
  exact centralizes_of_card_le_of_lattice (Yb := c.bar Y) (Rb := c.bar R) (Ob := c.bar O)
    (Vb := c.bar (closure {t, c.z}))
    (c.bar_perfect hK.Y_perfect) (bar_R_comm hR) (bar_Y_normalizes_R hJ hK)
    (bar_O_le_bar_R hK) (bar_V_le_bar_O hK) (card_bar_V hK) (bar_Y_normalizes_V hK)
    (bar_Y_comm_R_mem_bar_O hR hJ hK) (bar_lattice hK) hM hMn hMc

theorem bar_Y_hlat2 (hR : RData c R) (hJ : JData c t R J) (hK : KDataC c t R J K O Y) :
    ∃ y ∈ c.bar Y, ∃ r ∈ c.bar R, y * r ≠ r * y := by
  by_contra hcon
  push Not at hcon
  exact not_centralizes_of_lattice (Yb := c.bar Y) (Rb := c.bar R) (Ob := c.bar O)
    (Vb := c.bar (closure {t, c.z}))
    (bar_O_le_bar_R hK)
    (fun a ha b hb => bar_R_comm hR a (bar_O_le_bar_R hK ha) b (bar_O_le_bar_R hK hb))
    (card_bar_O hK) (bar_V_le_bar_O hK) (card_bar_V hK) (bar_lattice hK) hcon

theorem exists_component (hC : CCore c) (hR : RData c R) (hJ : JData c t R J)
    (hK : KDataC c t R J K O Y) (hF : U42Facts) :
    ∃ L1 : Subgroup c.Qt, CFSG.IsComponent L1 ∧ CFSG.layer c.Qt = L1 ∧ c.bar R ≤ L1 := by
  exact exists_unique_component (pPrimeCore_Qt_eq_bot hC) (pCore_Qt_eq_bot hC)
    (bar_R_sq hR) (bar_R_comm hR) (bar_R_ne_bot hR) (bar_R_cent hR)
    (le_of_eq (bar_R_card hR)) (bar_R_irr hR) (bar_Y_normalizes_R hJ hK)
    (bar_Y_normalizes_components hC hR hJ hK hF) (bar_Y_hlat1 hR hJ hK)
    (bar_Y_hlat2 hR hJ hK)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
