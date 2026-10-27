module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAut74Idx

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

variable {Q : Type} [Group Q]

private lemma mem_center_equiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') (z : Q) :
    e z ∈ center Q' ↔ z ∈ center Q := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h x
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e x)
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h x]

theorem mem_chainStab_congr {Q' : Type} [Group Q'] (e : Q ≃* Q') (α : MulAut Q) :
    MulAut.congr e α ∈ chainStab Q' ↔ α ∈ chainStab Q := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun z hz => ?_⟩
    · have hx := h.1 (e x)
      exact (mem_center_equiv e (x⁻¹ * α x)).mp
        (by simpa [MulAut.congr_apply, map_mul, map_inv] using hx)
    · have hz' : e z ∈ center Q' := (mem_center_equiv e z).mpr hz
      have h2 := h.2 (e z) hz'
      exact e.injective (by simpa [MulAut.congr_apply] using h2)
  · intro h
    refine ⟨fun y => ?_, fun w hw => ?_⟩
    · have hx := h.1 (e.symm y)
      have hc : e ((e.symm y)⁻¹ * α (e.symm y)) ∈ center Q' :=
        (mem_center_equiv e ((e.symm y)⁻¹ * α (e.symm y))).mpr hx
      simpa [MulAut.congr_apply, map_mul, map_inv] using hc
    · have hw' : e.symm w ∈ center Q :=
        (mem_center_equiv e (e.symm w)).mp (by simpa using hw)
      have h2 := h.2 (e.symm w) hw'
      change e (α (e.symm w)) = w
      rw [h2, e.apply_symm_apply]

theorem GHI74_index_le_two (hQ : Nonempty (Q ≃* SylSL3_4)) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (φ : P →* MulAut Q) (hfix : ∀ p : P, ∀ z ∈ center Q, φ p z = z) :
    ((chainStab Q).comap φ).index ≤ 2 := by
  let e' : Q ≃* U4 := hQ.some.trans sylLCongr
  let φ' : P →* MulAut U4 := (MulAut.congr e').toMonoidHom.comp φ
  have hfix' : ∀ p : P, ∀ z ∈ center U4, φ' p z = z := by
    intro p z hz
    obtain ⟨z0, rfl⟩ := e'.surjective z
    have hz0 : z0 ∈ center Q := (mem_center_equiv e' z0).mp hz
    show MulAut.congr e' (φ p) (e' z0) = e' z0
    change e' ((φ p) (e'.symm (e' z0))) = e' z0
    rw [e'.symm_apply_apply, hfix p z0 hz0]
  have hcomap : (chainStab U4).comap φ' = (chainStab Q).comap φ := by
    ext p
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    exact mem_chainStab_congr e' (φ p)
  rw [← hcomap]
  exact index_chainStab_comap_le_two hP φ' hfix'

end CFSG.OddStandard.SmallF3.HarrisU33.Outside