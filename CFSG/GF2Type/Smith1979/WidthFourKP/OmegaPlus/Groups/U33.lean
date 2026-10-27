module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Model28
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.LayerData

public section

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open CFSG.OddStandard.SmallF3.HarrisU33.K28
open CFSG.Blueprint
open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

private def innerW2 : Pm := fx₁ * fg3 * fx₁⁻¹

private def outerH : Pm := fx₂ ^ 2 * frho⁻¹ * flam

private def outerW2 : Pm := outerH * frho * outerH⁻¹

private theorem innerW2_pow : innerW2 ^ 3 = 1 := by decide +kernel

private theorem innerW2_comm_fz : innerW2 * fz = fz * innerW2 := by decide +kernel

private theorem inner_pair_cube_ne : (fg3 * innerW2) ^ 3 ≠ 1 := by decide +kernel

private theorem outerW2_comm_ftau : outerW2 * ftau = ftau * outerW2 := by decide +kernel

private theorem outerW2_pow : outerW2 ^ 3 = 1 := by decide +kernel

private theorem outer_pair_cube_ne : (frho * outerW2) ^ 3 ≠ 1 := by decide +kernel

private theorem outerH_mem : outerH ∈ QP.originalSubgroup := by
  unfold outerH
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ fx₂_mem 2)
    (Subgroup.inv_mem _ frho_mem)) flam_mem

private theorem innerW2_mem :
    innerW2 ∈ QP.originalSubgroup := by
  unfold innerW2
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ fx₁_mem fg3_mem) (Subgroup.inv_mem _ fx₁_mem)

private theorem outerW2_mem :
    outerW2 ∈ QP.originalSubgroup := by
  unfold outerW2
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ outerH_mem frho_mem)
    (Subgroup.inv_mem _ outerH_mem)

private theorem conj_fixed_pair {G : Type*} [Group G] {c s w₁ w₂ : G}
    (h₁ : Commute w₁ s) (h₂ : Commute w₂ s)
    (hp₁ : w₁ ^ 3 = 1) (hp₂ : w₂ ^ 3 = 1) (hp : (w₁ * w₂) ^ 3 ≠ 1) :
    Commute (c * w₁ * c⁻¹) (c * s * c⁻¹) ∧
      Commute (c * w₂ * c⁻¹) (c * s * c⁻¹) ∧
      (c * w₁ * c⁻¹) ^ 3 = 1 ∧ (c * w₂ * c⁻¹) ^ 3 = 1 ∧
      ((c * w₁ * c⁻¹) * (c * w₂ * c⁻¹)) ^ 3 ≠ 1 := by
  let φ : MulAut G := MulAut.conj c
  have hφ : ∀ x : G, φ x = c * x * c⁻¹ := by intro x; simp [φ, MulAut.conj_apply]
  have hc₁ : Commute (φ w₁) (φ s) := by simpa [hφ] using h₁.conj c
  have hc₂ : Commute (φ w₂) (φ s) := by simpa [hφ] using h₂.conj c
  have hpow₁ : (φ w₁) ^ 3 = 1 := by
    have h := map_pow φ w₁ 3
    rw [hp₁, map_one] at h
    simpa [hφ] using h.symm
  have hpow₂ : (φ w₂) ^ 3 = 1 := by
    have h := map_pow φ w₂ 3
    rw [hp₂, map_one] at h
    simpa [hφ] using h.symm
  have hprod : ((φ w₁) * (φ w₂)) ^ 3 ≠ 1 := by
    intro h
    apply hp
    have h' : φ ((w₁ * w₂) ^ 3) = 1 := by
      rw [map_pow, map_mul]
      exact h
    exact (MulEquiv.map_eq_one_iff φ).mp h'
  exact ⟨hc₁, hc₂, hpow₁, hpow₂, hprod⟩

private theorem conj_mem {c w : Pm} (hc : c ∈ QP.originalSubgroup)
    (hw : w ∈ QP.originalSubgroup) : c * w * c⁻¹ ∈ QP.originalSubgroup :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hw) (Subgroup.inv_mem _ hc)

private theorem fixed_pair_of_model
    {X : Type} [Group X] (m : Model28 X) {τ : MulAut X} (u₁ u₂ : Pm)
    (hu₁ : u₁ ∈ QP.originalSubgroup) (hu₂ : u₂ ∈ QP.originalSubgroup)
    (hc₁ : u₁ * m.ι τ = m.ι τ * u₁) (hc₂ : u₂ * m.ι τ = m.ι τ * u₂)
    (hp₁ : u₁ ^ 3 = 1) (hp₂ : u₂ ^ 3 = 1) (hp : (u₁ * u₂) ^ 3 ≠ 1) :
    ∃ y₁ y₂ : X, τ y₁ = y₁ ∧ τ y₂ = y₂ ∧ y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ (y₁ * y₂) ^ 3 ≠ 1 := by
  let y₁ : X := m.e.symm ⟨u₁, hu₁⟩
  let y₂ : X := m.e.symm ⟨u₂, hu₂⟩
  have hε₁ : m.ε y₁ = u₁ := by simp [y₁, Model28.ε]
  have hε₂ : m.ε y₂ = u₂ := by simp [y₂, Model28.ε]
  have hfix₁ : τ y₁ = y₁ := by
    apply m.ε_injective
    rw [m.ε_apply τ y₁, hε₁, ← hc₁]
    group
  have hfix₂ : τ y₂ = y₂ := by
    apply m.ε_injective
    rw [m.ε_apply τ y₂, hε₂, ← hc₂]
    group
  have hpow₁ : y₁ ^ 3 = 1 := by
    apply m.ε_injective
    rw [map_pow, hε₁, hp₁, map_one]
  have hpow₂ : y₂ ^ 3 = 1 := by
    apply m.ε_injective
    rw [map_pow, hε₂, hp₂, map_one]
  have hprod : (y₁ * y₂) ^ 3 ≠ 1 := by
    intro h0
    apply hp
    have h1 : m.ε ((y₁ * y₂) ^ 3) = m.ε (1 : X) := by rw [h0]
    rw [map_pow, map_mul, hε₁, hε₂, map_one] at h1
    exact h1
  exact ⟨y₁, y₂, hfix₁, hfix₂, hpow₁, hpow₂, hprod⟩

theorem exists_fixed_pair_of_lieModel_u33
    {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSU 3 3 1) {τ : MulAut X} (hτ1 : τ ≠ 1)
    (hτ2 : τ * τ = 1) :
    ∃ y₁ y₂ : X, τ y₁ = y₁ ∧ τ y₂ = y₂ ∧ y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ (y₁ * y₂) ^ 3 ≠ 1 := by
  obtain ⟨m⟩ := exists_model28 h
  have hσA : m.ι τ ∈ QA.originalSubgroup := m.ι_mem τ
  have hσ2 : m.ι τ * m.ι τ = 1 := by simpa [map_mul] using congrArg m.ι hτ2
  have hσ1 : m.ι τ ≠ 1 := fun h1 => hτ1 (m.ι_injective (by simpa using h1))
  by_cases hσP : m.ι τ ∈ QP.originalSubgroup
  · obtain ⟨c, hcP, hcσ⟩ := invol_conj_fz hσP hσ2 hσ1
    have hs : m.ι τ = c⁻¹ * fz * (c⁻¹)⁻¹ := by rw [← hcσ]; group
    have hc := conj_fixed_pair (c := c⁻¹) (s := fz) (w₁ := fg3) (w₂ := innerW2)
      fg3_pow.2.2 innerW2_comm_fz fg3_pow.1 innerW2_pow inner_pair_cube_ne
    exact fixed_pair_of_model m _ _
      (conj_mem (c := c⁻¹) (Subgroup.inv_mem _ hcP) fg3_mem)
      (conj_mem (c := c⁻¹) (Subgroup.inv_mem _ hcP) innerW2_mem)
      (by rw [hs]; exact hc.1)
      (by rw [hs]; exact hc.2.1)
      hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  · obtain ⟨c, hcP, hcσ⟩ := outer_invol_conj_ftau hσA hσP hσ2
    have hs : m.ι τ = c * ftau * c⁻¹ := hcσ.symm
    have hc := conj_fixed_pair (c := c) (s := ftau) (w₁ := frho) (w₂ := outerW2)
      ftau_frho.symm outerW2_comm_ftau frho_pow.1 outerW2_pow outer_pair_cube_ne
    exact fixed_pair_of_model m _ _
      (conj_mem hcP frho_mem)
      (conj_mem hcP outerW2_mem)
      (by rw [hs]; exact hc.1)
      (by rw [hs]; exact hc.2.1)
      hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2

theorem false_of_u33
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {τ : MulAut X} {B : Subgroup X} (D : LayerData X A τ B)
    (h : CFSG.Blueprint.LieModel X .PSU 3 3 1) : False := by
  obtain ⟨y₁, y₂, h₁, h₂, h₁3, h₂3, hprod⟩ :=
    exists_fixed_pair_of_lieModel_u33 h D.ne_one (D.sq_A τ D.mem_A)
  exact D.false_of_W2 h₁ h₂ h₁3 h₂3 hprod

end CFSG.GF2Type.Smith1979.OmegaPlus
