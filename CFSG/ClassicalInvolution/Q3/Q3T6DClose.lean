module

public import CFSG.ClassicalInvolution.Q3.Q3T6DC4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Three

variable (d : Std20Three K K' J S R R' W V z t)
include d

theorem exists_rho {a₀ : G} (haK : K ≤ Subgroup.centralizer ({a₀} : Set G))
    (haJ : J ≤ Subgroup.centralizer ({a₀} : Set G)) :
    ∃ ρ ∈ Subgroup.centralizer ({a₀} : Set G), ρ * t * ρ⁻¹ = z := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  have hpair : pairNormalizers K J z t ≤ Subgroup.centralizer ({a₀} : Set G) :=
    sup_le (inf_le_left.trans haK) (inf_le_left.trans haJ)
  refine ⟨t₀ * r, (Subgroup.centralizer _).mul_mem (hpair hh.t₀_mem_pair) (hpair hh.r_mem_pair),
    ?_⟩
  calc (t₀ * r) * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
    _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
    _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
    _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
    _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]

theorem twinSet_K' : twinSet (CoreAssembly.conjClass K) K' = {K', K} := by
  ext L
  constructor
  · rintro ⟨hL, z', hz'K', hz'L⟩
    have hzz : z' = z := hz'K'.eq d.late_hzK'
    subst hzz
    have hm : L ∈ twinSet (CoreAssembly.conjClass K) K := ⟨hL, z', d.viol.hzK, hz'L⟩
    rw [d.twins] at hm
    rcases hm with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · subst h
      exact ⟨d.late_mem_K', z, d.late_hzK', d.late_hzK'⟩
    · subst h
      exact ⟨d.late_mem_K, z, d.late_hzK', d.viol.hzK⟩

theorem concl20_4_of_hex (hH : Hex20 (CoreAssembly.conjClass K) K J W) :
    Concl20_4 S K K' J z := by
  refine d.concl20_4_of_98 hH ?_ (d.late_tor hH.JW hH.hW)
  exact (d.late_98 hH.JW hH.hW (X := centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (S.isPGroup'.to_le (fun x hx => hx.1)) (fun x hx => hx.1) (fun x hx => d.cent_comm_t hx)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer hx))).2

theorem cent_le_normalizer' {a : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    a ∈ Subgroup.normalizer (K' : Set G) := by
  have h1 := mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer ha)
  exact mem_normalizer_iff_conjSub_eq.mpr ((d.late_conj_iff (d.hSz ha.1)).mp h1)

end Std20Three

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
