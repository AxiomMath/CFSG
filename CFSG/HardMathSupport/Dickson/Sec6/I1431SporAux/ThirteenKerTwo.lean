module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.KerTwoDict
public import CFSG.Monster.Existence.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster.Existence

section KerTwoOf

variable {G : Type} [Group G]

theorem exists_kerTwo_of_isTwoACentralizer {u : G} (hu : orderOf u = 2) (h : IsTwoACentralizer u) :
    ∃ π : ↥(cent u) →* NativeSporadic.B, KerTwo u π := by
  obtain ⟨-, hz, ⟨e⟩⟩ := h
  let ψ : (↥(cent u) ⧸ center ↥(cent u)) →* NativeSporadic.B :=
    MonoidHom.mk' (fun x => e x) (fun x y => e.map_mul x y)
  have hψi : Function.Injective ψ := e.injective
  refine ⟨ψ.comp (QuotientGroup.mk' (center ↥(cent u))), ?_⟩
  intro g h hgh
  have h1 : (QuotientGroup.mk g : ↥(cent u) ⧸ center ↥(cent u)) = QuotientGroup.mk h :=
    hψi hgh
  rw [QuotientGroup.eq] at h1
  have h2 : ((g⁻¹ * h : ↥(cent u)) : G) ∈ zpowers u := by
    have := Subgroup.mem_map_of_mem (cent u).subtype h1
    rwa [hz] at this
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 h2
  have hgu : (g : G) * u = u * g := mem_centralizer_singleton_iff.1 g.2
  have hnn : u ^ n = u ^ (n % 2) := by
    have := zpow_mod_orderOf u n
    rw [hu] at this
    simpa using this.symm
  have hh : (h : G) = g * ((g⁻¹ * h : ↥(cent u)) : G) := by
    simp
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1'
  · left
    have : ((g⁻¹ * h : ↥(cent u)) : G) = 1 := by
      rw [← hn, hnn, h0, zpow_zero]
    rw [hh, this, mul_one]
  · right
    have : ((g⁻¹ * h : ↥(cent u)) : G) = u := by
      rw [← hn, hnn, h1', zpow_one]
    rw [hh, this, hgu]

end KerTwoOf

end CFSG.HardMathSupport.Dickson.Sec6.I1431
