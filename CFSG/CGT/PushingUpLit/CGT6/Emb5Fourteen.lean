module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Conj
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

section Conj

variable {V : Type} [CommGroup V]

theorem conjSub_conjSub (c g : MulAut V) (Y : Subgroup (MulAut V)) :
    CGT6E.conjSub c (CGT6E.conjSub g Y) = CGT6E.conjSub (c * g) Y := by
  unfold CGT6E.conjSub
  rw [Subgroup.map_map]
  congr 1

theorem conjSub_one (Y : Subgroup (MulAut V)) : CGT6E.conjSub 1 Y = Y := by
  ext z
  rw [CGT6E.mem_conjSub]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨z, hz, by simp⟩

theorem mem_normalizer_of_conjSub_eq {Y : Subgroup (MulAut V)} {n : MulAut V}
    (h : CGT6E.conjSub n Y = Y) : n ∈ Subgroup.normalizer (Y : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := CGT6E.conj_mem_conjSub (q := n) hx
    rwa [h] at this
  · intro hx
    have hx' : n * x * n⁻¹ ∈ CGT6E.conjSub n Y := by rwa [h]
    obtain ⟨y, hy, hyx⟩ := CGT6E.mem_conjSub.mp hx'
    have : y = x := by
      have h1 : n * y * n⁻¹ = n * x * n⁻¹ := hyx
      simpa using h1
    rwa [← this]

theorem conjSub_eq_of_mem_normalizer {Y : Subgroup (MulAut V)} {n : MulAut V}
    (h : n ∈ Subgroup.normalizer (Y : Set (MulAut V))) : CGT6E.conjSub n Y = Y := by
  ext z
  rw [CGT6E.mem_conjSub]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp h y).mp hy
  · intro hz
    refine ⟨n⁻¹ * z * n, ?_, by group⟩
    have h' := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem h) z
    have := h'.mp hz
    simpa using this

end Conj

end CFSG.CGT.PushingUpLit.CGT6
