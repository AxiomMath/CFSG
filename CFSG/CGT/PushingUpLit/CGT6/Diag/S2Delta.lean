module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.S2

open CFSG.CGT.PushingUpLit.CGT6 Subgroup

variable {V : Type} [CommGroup V] {K K' Y : Subgroup (MulAut V)} {t : MulAut V}

theorem conj_mem (h : DiagPre K K' Y t) {k : MulAut V} (hk : k ∈ K) : t * k * t⁻¹ ∈ K' := by
  rw [h.Kconj]
  exact ⟨k, hk, by simp [MulAut.conj_apply]⟩

noncomputable def delta (h : DiagPre K K' Y t) : K →* MulAut V where
  toFun k := (k : MulAut V) * (t * k * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hc := h.comm (b : MulAut V) b.2 (t * a * t⁻¹) (conj_mem h a.2)
    have e1 : t * ((a : MulAut V) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    simp only [Subgroup.coe_mul]
    rw [e1]
    calc (a : MulAut V) * b * ((t * a * t⁻¹) * (t * b * t⁻¹))
        = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hc]
      _ = _ := by group

theorem delta_mem (h : DiagPre K K' Y t) (k : K) : delta h k ∈ Y :=
  (h.Y_mem _).2 ⟨k, k.2, rfl⟩

noncomputable def deltaY (h : DiagPre K K' Y t) : K →* Y := (delta h).codRestrict Y (delta_mem h)

theorem deltaY_surjective (h : DiagPre K K' Y t) : Function.Surjective (deltaY h) := by
  intro y
  obtain ⟨k, hk, hy⟩ := (h.Y_mem y).1 y.2
  exact ⟨⟨k, hk⟩, Subtype.ext hy.symm⟩

theorem ker_deltaY_le_center (h : DiagPre K K' Y t) : (deltaY h).ker ≤ center K := by
  intro k hk
  have h1 : (k : MulAut V) * (t * k * t⁻¹) = 1 := by
    have := congrArg Subtype.val ((MonoidHom.mem_ker).1 hk)
    simpa [deltaY, delta] using this
  have hk' : (k : MulAut V) ∈ K' := by
    have h2 : t * k * t⁻¹ = (k : MulAut V)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : (k : MulAut V)⁻¹ ∈ K' := h2 ▸ conj_mem h k.2
    simpa using K'.inv_mem h3
  refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
  exact h.comm g g.2 k hk'

theorem center_le_ker_deltaY (h : DiagPre K K' Y t) : center K ≤ (deltaY h).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have : deltaY h z ∈ center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := deltaY_surjective h y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
  rw [h.centerY] at this
  exact this

theorem ker_deltaY_eq_center (h : DiagPre K K' Y t) : (deltaY h).ker = center K :=
  le_antisymm (ker_deltaY_le_center h) (center_le_ker_deltaY h)

end CFSG.CGT.PushingUpLit.CGT6.Diag.S2
