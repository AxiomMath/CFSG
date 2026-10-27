module

public import CFSG.LargeExtraspecial.AS35YSIrrX

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal
  AS35YR

namespace AS35YS

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace LeviInv

variable {F : Frame q} {Y : Submodule (ZMod 2) V}

theorem Xp_le [FiniteDimensional (ZMod 2) V] (h : LeviInv F Y) (hq : q.polarBilin.Nondegenerate)
    (hX : 3 ≤ finrank (ZMod 2) F.Xp) (hYX : Y ≤ F.Xp) (hY0 : Y ≠ ⊥) : F.Xp ≤ Y := by
  have hYnd := h.nondeg hq hX hYX
  obtain ⟨y₀, hy₀, hq₀⟩ := h.exists_ns_mem hq hX hYX hY0
  have hy₀X := hYX hy₀
  have hy₀0 : y₀ ≠ 0 := fun e => by rw [e, QuadraticMap.map_zero] at hq₀; exact zero_ne_one hq₀
  have hdich : ∀ w ∈ F.Xp, q w = 1 → w ∈ Y ∨ ∀ z ∈ Y, polar q z w = 0 := fun w hwX hw =>
    mem_or_perp_of_refl hw fun y hy => h.refl_mem hy₀ hy₀X hq₀ hwX hw hy
  set K := F.Xp ⊓ LinearMap.BilinForm.orthogonal q.polarBilin Y with hK
  have hmemK : ∀ x ∈ K, x ∈ F.Xp ∧ ∀ z ∈ Y, polar q x z = 0 := fun x hx =>
    ⟨hx.1, OrthoF2.mem_orthogonal_iff_polar.mp hx.2⟩
  have hYrestr : (LinearMap.BilinForm.restrict q.polarBilin Y).Nondegenerate := by
    refine ⟨fun z hz => Subtype.ext (hYnd z z.2 fun y' hy' => ?_), fun z hz =>
      Subtype.ext (hYnd z z.2 fun y' hy' => ?_)⟩
    · have := hz ⟨y', hy'⟩
      simpa [polarBilin_apply_apply] using this
    · have := hz ⟨y', hy'⟩
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using this
  have hcompl := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (QuadraticMap.isSymm_polarBilin q).isRefl hYrestr
  have hXle : F.Xp ≤ Y ⊔ K := by
    intro x hx
    have hx' : x ∈ Y ⊔ LinearMap.BilinForm.orthogonal q.polarBilin Y :=
      hcompl.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨z, hz, z', hz', rfl⟩ := Submodule.mem_sup.mp hx'
    refine Submodule.mem_sup.mpr ⟨z, hz, z', ⟨?_, hz'⟩, rfl⟩
    have := F.Xp.sub_mem hx (hYX hz)
    rwa [add_sub_cancel_left] at this
  by_cases hK0 : K = ⊥
  · intro x hx
    have := hXle hx
    rwa [hK0, sup_bot_eq] at this
  exfalso
  have hKnd := h.perp.nondeg hq hX inf_le_left
  obtain ⟨w₀, hw₀K, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
  obtain ⟨hw₀X, hw₀Y⟩ := hmemK w₀ hw₀K
  have hconst : ∀ z ∈ Y, z ≠ 0 → ∀ z' ∈ K, z' ≠ 0 → q z = q z' := by
    intro z hz hz0 z' hz' hz'0
    by_contra hne
    obtain ⟨hz'X, hz'Y⟩ := hmemK z' hz'
    have hpol : polar q z z' = 0 := by rw [polar_comm]; exact hz'Y z hz
    have hsum : q (z + z') = 1 := by
      rw [QuadraticMap.map_add q, hpol, add_zero]
      rcases Frame.zmod2_cases_YR (q z) with h0 | h1 <;>
        rcases Frame.zmod2_cases_YR (q z') with h0' | h1'
      · exact absurd (h0.trans h0'.symm) hne
      · rw [h0, h1', zero_add]
      · rw [h1, h0', add_zero]
      · exact absurd (h1.trans h1'.symm) hne
    rcases hdich _ (F.Xp.add_mem (hYX hz) hz'X) hsum with hmem | hperp
    · have hz'Ymem : z' ∈ Y := by
        have := Y.sub_mem hmem hz
        rwa [add_sub_cancel_left] at this
      exact hz'0 (hYnd z' hz'Ymem hz'Y)
    · apply hz0
      refine hYnd z hz fun y' hy' => ?_
      have := hperp y' hy'
      rw [polar_add_right, polar_comm q y' z', hz'Y y' hy', add_zero] at this
      rw [polar_comm]
      exact this
  have hqY : ∀ z ∈ Y, z ≠ 0 → q z = 1 := by
    intro z hz hz0
    rcases Frame.zmod2_cases_YR (q z) with h0 | h1
    · exfalso
      have hall : ∀ x ∈ Y, q x = 0 := fun x hx => by
        by_cases hx0 : x = 0
        · rw [hx0, QuadraticMap.map_zero]
        · rw [hconst x hx hx0 w₀ hw₀K hw₀0, ← hconst z hz hz0 w₀ hw₀K hw₀0, h0]
      refine hz0 (hYnd z hz fun y' hy' => ?_)
      have := hall _ (Y.add_mem hz hy')
      rwa [QuadraticMap.map_add q, hall z hz, hall y' hy', zero_add, zero_add] at this
    · exact h1
  have hqK : ∀ z' ∈ K, z' ≠ 0 → q z' = 1 := fun z' hz' hz'0 =>
    (hconst y₀ hy₀ hy₀0 z' hz' hz'0).symm.trans hq₀
  obtain ⟨y₂, hy₂, hy₀₂⟩ : ∃ y₂ ∈ Y, polar q y₀ y₂ = 1 := by
    by_contra hcon
    push Not at hcon
    exact hy₀0 (hYnd y₀ hy₀ fun y' hy' => (Frame.zmod2_cases_YR _).resolve_right (hcon y' hy'))
  obtain ⟨w₁, hw₁K, hw₀₁⟩ : ∃ w₁ ∈ K, polar q w₀ w₁ = 1 := by
    by_contra hcon
    push Not at hcon
    exact hw₀0 (hKnd w₀ hw₀K fun y' hy' => (Frame.zmod2_cases_YR _).resolve_right (hcon y' hy'))
  obtain ⟨hw₁X, hw₁Y⟩ := hmemK w₁ hw₁K
  have hy₂0 : y₂ ≠ 0 := fun e => by rw [e, polar_zero_right] at hy₀₂; exact zero_ne_one hy₀₂
  have hw₁0 : w₁ ≠ 0 := fun e => by rw [e, polar_zero_right] at hw₀₁; exact zero_ne_one hw₀₁
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  set u := y₀ + w₀ with hu
  set w := y₂ + w₁ with hw
  have hqu : q u = 0 := by
    rw [hu, QuadraticMap.map_add q, hq₀, hqK w₀ hw₀K hw₀0, polar_comm, hw₀Y y₀ hy₀, add_zero,
      h11]
  have hqw : q w = 0 := by
    rw [hw, QuadraticMap.map_add q, hqY y₂ hy₂ hy₂0, hqK w₁ hw₁K hw₁0, polar_comm,
      hw₁Y y₂ hy₂, add_zero, h11]
  have huw : polar q u w = 0 := by
    rw [hu, hw, polar_add_left, polar_add_right, polar_add_right, hy₀₂, hw₀₁,
      polar_comm q y₀ w₁, hw₁Y y₀ hy₀, hw₀Y y₂ hy₂, add_zero, zero_add, h11]
  have huX : u ∈ F.Xp := F.Xp.add_mem hy₀X hw₀X
  have hwX : w ∈ F.Xp := F.Xp.add_mem (hYX hy₂) hw₁X
  have hS := h.2 u huX w hwX hqu hqw huw y₀ hy₀
  have hpu : polar q y₀ u = 0 := by
    rw [hu, polar_add_right, polar_self_YR, polar_comm, hw₀Y y₀ hy₀, add_zero]
  have hpw : polar q y₀ w = 1 := by
    rw [hw, polar_add_right, hy₀₂, polar_comm, hw₁Y y₀ hy₀, add_zero]
  rw [siegel_apply hqu hqw huw, hpu, hpw, zero_smul, add_zero, one_smul, hu, ← add_assoc,
    add_self_YR, zero_add] at hS
  exact hw₀0 (hYnd w₀ hS hw₀Y)

end LeviInv

end AS35YS

end CFSG.LargeExtraspecial
