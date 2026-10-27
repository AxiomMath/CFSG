module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLCore

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Gr

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL (conjProj apply_proj_eq_of_commute)

section Conj

variable {P : Type} [Group P]

theorem eq_one_of_conj (α i₀ : MulAut P)
    (h₀ : ∀ R₀ : Subgroup (MulAut P), Odd (Nat.card R₀) → (∀ r ∈ R₀, r * i₀ = i₀ * r) →
      (∀ s : P, i₀ s = s → Odd (orderOf s) → ∀ r ∈ R₀,
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R₀) → ∀ r ∈ R₀, r = 1)
    {R : Subgroup (MulAut P)} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * (α * i₀ * α⁻¹) = α * i₀ * α⁻¹ * r)
    (hRc : ∀ s : P, (α * i₀ * α⁻¹) s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r ∈ R, r = 1 := by
  set c : MulAut (MulAut P) := MulAut.conj α⁻¹ with hc
  set R₀ := R.map c.toMonoidHom with hR₀
  have hmem : ∀ r ∈ R, α⁻¹ * r * α ∈ R₀ := fun r hr => ⟨r, hr, by simp [hc]⟩
  have hR₀odd : Odd (Nat.card R₀) := by
    rw [hR₀, Subgroup.card_map_of_injective c.injective]
    exact hRodd
  have hR₀i : ∀ r ∈ R₀, r * i₀ = i₀ * r := by
    rintro _ ⟨r, hr, rfl⟩
    have h := hRi r hr
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc α⁻¹ * r * α * i₀ = α⁻¹ * (r * (α * i₀ * α⁻¹)) * α := by group
      _ = α⁻¹ * (α * i₀ * α⁻¹ * r) * α := by rw [h]
      _ = i₀ * (α⁻¹ * r * α) := by group
  have hR₀c : ∀ s : P, i₀ s = s → Odd (orderOf s) → ∀ r ∈ R₀,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R₀ := by
    rintro s hs hso _ ⟨r, hr, rfl⟩
    have hs' : (α * i₀ * α⁻¹) (α s) = α s := by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hs]
    have hso' : Odd (orderOf (α s)) := by rwa [MulEquiv.orderOf_eq]
    have h := hmem _ (hRc (α s) hs' hso' r hr)
    have e : α⁻¹ * (MulAut.conj (α s) * r * (MulAut.conj (α s))⁻¹) * α =
        MulAut.conj s * (α⁻¹ * r * α) * (MulAut.conj s)⁻¹ := by
      rw [conj_apply_eq]
      group
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← e]
    exact h
  have h₀R := h₀ R₀ hR₀odd hR₀i hR₀c
  intro r hr
  have h1 := h₀R _ (hmem r hr)
  calc r = α * (α⁻¹ * r * α) * α⁻¹ := by group
    _ = 1 := by rw [h1]; group

end Conj

theorem center_eq_bot_of_conj_injective {T : Type} [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) : center T = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  apply hinj
  rw [map_one]
  ext x
  rw [MulAut.conj_apply, MulAut.one_apply, (mem_center_iff.mp hz x).symm, mul_inv_cancel_right]

theorem conj_range_normal {T : Type} [Group T] :
    (MulAut.conj : T →* MulAut T).range.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ φ
  exact ⟨φ x, conj_apply_eq φ x⟩

section Fix

variable {n : ℕ} {K : Type} [Field K]

theorem conjProj_ker_le
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) :
    (conjProj n K).ker ≤ center (Matrix.SpecialLinearGroup (Fin n) K) := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have h1 : proj n K y = 1 := hinj (by rw [map_one]; exact hy)
  exact scalars_le_center n K (proj_eq_one_iff.1 h1)

theorem conjProj_range :
    (conjProj n K).range = (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (proj_surjective n K),
    ← MonoidHom.range_eq_map]

theorem fix_of_le_iSup {ι : Type*} {F : ι → Subgroup (Matrix.SpecialLinearGroup (Fin n) K)}
    {r : MulAut (projectiveSL n K)} (hfix : ∀ i, ∀ g ∈ F i, r (proj n K g) = proj n K g)
    {g : Matrix.SpecialLinearGroup (Fin n) K} (hg : g ∈ ⨆ i, F i) :
    r (proj n K g) = proj n K g := by
  have hle : (⨆ i, F i) ≤ MonoidHom.eqLocus (r.toMonoidHom.comp (proj n K)) (proj n K) :=
    iSup_le fun i g hg => hfix i g hg
  exact hle hg

variable [Finite K]

theorem fix_of_component
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {t : MulAut (projectiveSL n K)} (δ : MulAut (Matrix.SpecialLinearGroup (Fin n) K))
    (hδ : ∀ g, t (proj n K g) = proj n K (δ g))
    {Q₀ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)}
    (hQ₀ : Open.IsComponentOf Q₀ (ClassicalInvolution.Balance.fixedGroup δ))
    {R : Subgroup (MulAut (projectiveSL n K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * t = t * r)
    (hRc : ∀ s, t s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R)
    {r : MulAut (projectiveSL n K)} (hr : r ∈ R) {g : Matrix.SpecialLinearGroup (Fin n) K}
    (hg : g ∈ Q₀) : r (proj n K g) = proj n K g := by
  have hZ := center_eq_bot_of_conj_injective hinj
  have hcomp : ∀ y, t * conjProj n K y * t⁻¹ = conjProj n K (δ y) := by
    intro y
    change t * MulAut.conj (proj n K y) * t⁻¹ = MulAut.conj (proj n K (δ y))
    rw [← hδ, conj_apply_eq]
  have hQ := ClassicalInvolution.Balance.isComponentOf_map_centralizer (conjProj_ker_le hinj) 1
    t δ (fun y => by simpa using hcomp y) hQ₀
  have e : (MulAut.conj (1 : Matrix.SpecialLinearGroup (Fin n) K)).toMonoidHom =
      MonoidHom.id _ := by
    ext
    simp
  rw [e, MonoidHom.comp_id] at hQ
  have : (conjProj n K).range.Normal := by
    rw [conjProj_range]
    exact conj_range_normal
  have hRconj : ∀ s ∈ (conjProj n K).range ⊓ centralizer ({t} : Set _), Odd (orderOf s) →
      ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    intro s hs hso r hr
    rw [conjProj_range] at hs
    exact conj_mem_of_mem_range hZ hRc hs hso hr
  exact apply_proj_eq_of_commute hinj
    (commute_of_isComponentOf (L := (conjProj n K).range) hRodd hRi hRconj hQ hr ⟨g, hg, rfl⟩)

end Fix

end CFSG.ComponentClassification.Foote5.OddLieCore.Gr
