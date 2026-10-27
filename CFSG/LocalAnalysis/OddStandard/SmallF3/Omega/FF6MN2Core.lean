module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MHerm3Cent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_N2_core (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {p : OGroup Q} (hp : p * p = piOrth Q) :
    LieModel ↥⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆
        .PSU 3 3 1 ∧
      ⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆ ≤
        omegaGroup hQ ∧
      piOrth Q ∉ ⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆ ∧
      ∀ g ∈ omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)),
        g ∈ ⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆ ∨
          piOrth Q * g ∈
            ⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆ := by
  obtain ⟨E, hEω, hEπ, hEΩ⟩ := ff6m_exists_frame_iso3 hQ hdim hsgn hp
  set C₃ : Subgroup (OGroup (hermForm 3)) :=
    centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3))) with hC₃
  have hC : centralizer ({p} : Set (OGroup Q)) = C₃.map E.toMonoidHom := by
    ext g
    rw [mem_centralizer_singleton_iff, ← hEω, Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨E.symm g, ?_, E.apply_symm_apply g⟩
      rw [hC₃, mem_centralizer_singleton_iff]
      apply E.injective
      rw [map_mul, map_mul, E.apply_symm_apply]
      exact h
    · rintro ⟨x, hx, rfl⟩
      rw [hC₃, mem_centralizer_singleton_iff] at hx
      change E x * E (omegaOrth 3) = E (omegaOrth 3) * E x
      rw [← map_mul, ← map_mul, hx]
  have hD : ⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆ =
      (⁅C₃, C₃⁆).map E.toMonoidHom := by
    rw [hC, Subgroup.map_commutator]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD]
    exact LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective ⁅C₃, C₃⁆ E.toMonoidHom E.injective) herm3_lieModel_derived
  · rw [omegaGroup_eq_commutator hQ (by rw [hdim]; norm_num), _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · rw [hD, herm3_derived_eq]
    intro h
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp h
    have hx' : x = piOrth (hermForm 3) := E.injective (by rw [← hEπ] at hxπ; exact hxπ)
    exact suToOrth3_pi_not_mem (hx' ▸ hx)
  · intro g hg
    obtain ⟨hgΩ, hgC⟩ := Subgroup.mem_inf.mp hg
    rw [hC] at hgC
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hgC
    have hxΩ : x ∈ omegaGroup (hermForm_nondegenerate 3) := (hEΩ x).mp hgΩ
    rw [hD, herm3_derived_eq]
    rcases herm3_mem_cases hxΩ hx with h | h
    · exact Or.inl (Subgroup.mem_map_of_mem _ h)
    · refine Or.inr ?_
      have h' := Subgroup.mem_map_of_mem E.toMonoidHom h
      simpa only [MulEquiv.coe_toMonoidHom, map_mul, hEπ] using h'

end CFSG.OddStandard.SmallF3.Omega
