module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResAssemblyA

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

namespace CSide

variable {G : Type} [Group G]

@[expose] def actN (C : Subgroup G) : normalizer (C : Set G) →* MulAut C where
  toFun n := conjAct C (n : G)
    (fun h hh => (mem_normalizer_iff.1 n.2 h).1 hh)
    (fun h hh => by
      have := (mem_normalizer_iff.1 (inv_mem n.2) h).1 hh
      simpa using this)
  map_one' := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    simp [conjAct_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    simp [conjAct_apply, mul_assoc]

theorem actN_apply (C : Subgroup G) (n : normalizer (C : Set G)) (u : C) :
    ((actN C n u : C) : G) = (n : G) * u * (n : G)⁻¹ := rfl

@[expose] noncomputable def actC (C : Subgroup G) (hC : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) :
    egQD C →* MulAut C :=
  QuotientGroup.lift (C.subgroupOf (normalizer (C : Set G))) (actN C) (by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    have hnC : (n : G) ∈ C := mem_subgroupOf.1 hn
    rw [actN_apply]
    have := hC _ hnC u u.2
    show (n : G) * u * (n : G)⁻¹ = u
    rw [mul_inv_eq_iff_eq_mul, this])

theorem actC_mk (C : Subgroup G) (hC : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c)
    (n : normalizer (C : Set G)) : actC C hC (QuotientGroup.mk n) = actN C n := rfl



theorem ker_actC_le_cQuot (C : Subgroup G) (hC : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) :
    (actC C hC).ker ≤ cQuot C := by
  intro y hy
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MonoidHom.mem_ker, actC_mk] at hy
  have hcent : (n : G) ∈ centralizer (C : Set G) := by
    rw [mem_centralizer_iff]
    intro c hc
    have h1 : (n : G) * c * (n : G)⁻¹ = c := by
      have := congrArg (fun φ : MulAut C => ((φ ⟨c, hc⟩ : C) : G)) hy
      simpa [actN_apply] using this
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  exact ⟨n, mem_subgroupOf.2 hcent, rfl⟩

end CSide

end CFSG.EvenSporadicStandard.M24Std
