module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K1a
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharCls
public import CFSG.GH74.KGroups.L3EpsLin

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

section Conj

variable {L : Type*} [Group L]

theorem k1_conj_mul_inv (r : MulAut L) (a : L) :
    r * MulAut.conj a * r⁻¹ = MulAut.conj (r a) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem k1_comm_conj (r : MulAut L) (d : L) :
    MulAut.conj d * r * (MulAut.conj d)⁻¹ * r⁻¹ = MulAut.conj (d * (r d)⁻¹) := by
  calc MulAut.conj d * r * (MulAut.conj d)⁻¹ * r⁻¹
      = MulAut.conj d * (r * MulAut.conj d⁻¹ * r⁻¹) := by rw [map_inv]; group
    _ = MulAut.conj d * MulAut.conj (r d⁻¹) := by rw [k1_conj_mul_inv]
    _ = MulAut.conj (d * (r d)⁻¹) := by rw [← map_mul, map_inv]

end Conj

section Core

variable {F : Type} [Field F]

theorem k1_proj_comm {g : SL(3, F)} (hg : g ∈ CenD F) :
    proj 3 F g * tInv = tInv * proj 3 F g := by
  rw [tInv, ← map_mul, ← map_mul, mem_CenD.mp hg]

theorem k1_conj_injective :
    Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : a ∈ Subgroup.center (projectiveSL 3 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * a = (a * g * a⁻¹) * a := by rw [this]
      _ = a * g := by group
  rw [center_projectiveSL_three_eq_bot, Subgroup.mem_bot] at hc
  exact hc

variable [Finite F]

theorem k1_inner_eq_one (h2 : (2 : F) ≠ 0) (p : ℕ) [Fact p.Prime] [CharP F p]
    {R : Subgroup (MulAut (projectiveSL 3 F))} (hR : IsPGroup p ↥R)
    (hRζ : ∀ r ∈ R, r tInv = tInv)
    (hRn : ∀ d : projectiveSL 3 F, d * tInv = tInv * d → ∀ r ∈ R,
      MulAut.conj d * r * (MulAut.conj d)⁻¹ ∈ R)
    (a : projectiveSL 3 F) (ha : MulAut.conj a ∈ R) : a = 1 := by
  set W : Subgroup (projectiveSL 3 F) := R.comap (MulAut.conj : projectiveSL 3 F →* MulAut _)
    with hW
  have hWp : IsPGroup p ↥W := hR.comap_of_injective _ k1_conj_injective
  have hWD : ∀ w ∈ W, w * tInv = tInv * w := by
    intro w hw
    have h1 := hRζ _ hw
    rw [MulAut.conj_apply] at h1
    calc w * tInv = (w * tInv * w⁻¹) * w := by group
      _ = tInv * w := by rw [h1]
  have hWn : ∀ d : projectiveSL 3 F, d * tInv = tInv * d → ∀ w ∈ W, d * w * d⁻¹ ∈ W := by
    intro d hd w hw
    have h1 := hRn d hd _ hw
    rw [Subgroup.mem_comap] at hw ⊢
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hWbot : W = ⊥ := by
    by_contra hne
    have hN : ∀ g ∈ CenD F, proj 3 F g ∈ normalizer (W : Set (projectiveSL 3 F)) := by
      intro g hg
      have hd : proj 3 F g * tInv = tInv * proj 3 F g := k1_proj_comm hg
      have hdi : (proj 3 F g)⁻¹ * tInv = tInv * (proj 3 F g)⁻¹ :=
        (Commute.inv_left (show Commute (proj 3 F g) tInv from hd)).eq
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨hWn _ hd w, fun hw => ?_⟩
      have := hWn _ hdi _ hw
      simpa [mul_assoc] using this
    rcases classify_p_subgroup h2 p W hWp hne hN with h | h
    · have hmem : proj 3 F (elP 1 0) ∈ W := by
        rw [h]
        exact Subgroup.mem_map_of_mem _ (mem_radP.mpr ⟨1, 0, rfl⟩)
      have hCen : elP (1 : F) 0 ∈ CenD F := mem_CenD_of_commute h2 (hWD _ hmem)
      have := (entries_of_mem_CenD h2 hCen).2.2.1
      simp [coe_elP] at this
    · have hmem : proj 3 F (elM 1 0) ∈ W := by
        rw [h]
        exact Subgroup.mem_map_of_mem _ (mem_radM.mpr ⟨1, 0, rfl⟩)
      have hCen : elM (1 : F) 0 ∈ CenD F := mem_CenD_of_commute h2 (hWD _ hmem)
      have := (entries_of_mem_CenD h2 hCen).1
      simp [coe_elM] at this
  have haW : a ∈ W := by rw [hW, Subgroup.mem_comap]; exact ha
  rw [hWbot, Subgroup.mem_bot] at haW
  exact haW

theorem k1_fix_centralizer (h2 : (2 : F) ≠ 0) (p : ℕ) [Fact p.Prime] [CharP F p]
    {R : Subgroup (MulAut (projectiveSL 3 F))} (hR : IsPGroup p ↥R)
    (hRζ : ∀ r ∈ R, r tInv = tInv)
    (hRn : ∀ d : projectiveSL 3 F, d * tInv = tInv * d → ∀ r ∈ R,
      MulAut.conj d * r * (MulAut.conj d)⁻¹ ∈ R)
    {r : MulAut (projectiveSL 3 F)} (hr : r ∈ R) {d : projectiveSL 3 F}
    (hd : d * tInv = tInv * d) : r d = d := by
  have h1 := R.mul_mem (hRn d hd r hr) (R.inv_mem hr)
  rw [k1_comm_conj] at h1
  have h3 := k1_inner_eq_one h2 p hR hRζ hRn _ h1
  have h4 : r d = d := by
    have : d = r d := by
      calc d = (d * (r d)⁻¹) * r d := by group
        _ = r d := by rw [h3, one_mul]
    exact this.symm
  exact h4

theorem k1_core (h2 : (2 : F) ≠ 0) (p : ℕ) [Fact p.Prime] [CharP F p] (hpF : p ∣ Nat.card F)
    {R : Subgroup (MulAut (projectiveSL 3 F))} (hR : IsPGroup p ↥R)
    (hRζ : ∀ r ∈ R, r tInv = tInv)
    (hRn : ∀ d : projectiveSL 3 F, d * tInv = tInv * d → ∀ r ∈ R,
      MulAut.conj d * r * (MulAut.conj d)⁻¹ ∈ R) :
    R = ⊥ := by
  refine eq_bot_iff.mpr fun r hr => ?_
  rw [Subgroup.mem_bot]
  have hfix : ∀ g ∈ CenD F, r (proj 3 F g) = proj 3 F g := fun g hg =>
    k1_fix_centralizer h2 p hR hRζ hRn hr (k1_proj_comm hg)
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have hk' : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact k1_aut_eq_one_of_fix_block p h2 hpF r hk' (fun t => hfix _ (k1_xU_mem_CenD t))
    (fun t => hfix _ (k1_xL_mem_CenD t)) (hfix _ k1_dg_mem_CenD)

end Core

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
