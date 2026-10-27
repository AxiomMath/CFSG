module

public import CFSG.CGT.PushingUpLit.T2K.FourFourA

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_conj_iff' {X : Subgroup G} {g t : G} :
    g⁻¹ * t * g ∈ Subgroup.normalizer (X : Set G) ↔
      t ∈ Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hq x
    have h1 := hq (g⁻¹ * x * g)
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have e2 : g⁻¹ * (t * x * t⁻¹) * g = (g⁻¹ * t * g) * (g⁻¹ * x * g) * (g⁻¹ * t * g)⁻¹ := by
      group
    rw [e2]
    exact h1
  · intro hq x
    have h1 := hq (g * x * g⁻¹)
    rw [mem_map_conj_iff, mem_map_conj_iff] at h1
    have e1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have e2 : g⁻¹ * (t * (g * x * g⁻¹) * t⁻¹) * g = (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1

end CFSG.CGT.PushingUpLit.T2K
