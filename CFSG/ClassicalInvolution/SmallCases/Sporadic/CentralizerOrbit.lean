module

public import CFSG.LocalAnalysis.ComponentInitial.AutomorphismRealization
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem centralizer_mk_eq {M : Type*} [Group M] {H : Subgroup M} {x : M} (hx : x ∈ H) :
    Subgroup.centralizer {(⟨x, hx⟩ : H)} = (Subgroup.centralizer {x}).subgroupOf H := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

theorem centralizerIn_eq_of_orbit {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n)))
    {z : Equiv.Perm (Fin n)}
    (hz : z ∈ P) (K : Subgroup (Equiv.Perm (Fin n)))
    (hKC : K ≤ centralizerIn P z)
    (horb : (K.subgroupOf P).index ≤
      (Set.range fun g : P => g • {p : Fin n | z p = p}).ncard) :
    centralizerIn P z = K := by
  have hH : K.subgroupOf P ≤ Subgroup.centralizer {(⟨z, hz⟩ : P)} := by
    intro g hg
    rw [centralizer_mk_eq hz, Subgroup.mem_subgroupOf]
    have := hKC (Subgroup.mem_subgroupOf.1 hg)
    rw [mem_centralizerIn] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact this.2
  have horb' : (K.subgroupOf P).index ≤
      (Set.range fun g : P => g • {p : Fin n | (⟨z, hz⟩ : P) • p = p}).ncard := horb
  have h := (fixed_point_set_orbit_centralizer_bound (⟨z, hz⟩ : P) _ hH horb').1
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxz⟩ := mem_centralizerIn.1 hx
    have hmem : (⟨x, hxP⟩ : P) ∈ Subgroup.centralizer {(⟨z, hz⟩ : P)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hxz
    rw [← h] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  · exact hKC

theorem index_eq_ncard_orbit {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) {z : Equiv.Perm (Fin n)}
    (hz : z ∈ P) (K : Subgroup (Equiv.Perm (Fin n))) (hKC : K ≤ centralizerIn P z)
    (horb : (K.subgroupOf P).index ≤
      (Set.range fun g : P => g • {p : Fin n | z p = p}).ncard) :
    (K.subgroupOf P).index = (Set.range fun g : P => g • {p : Fin n | z p = p}).ncard := by
  have hH : K.subgroupOf P ≤ Subgroup.centralizer {(⟨z, hz⟩ : P)} := by
    intro g hg
    rw [centralizer_mk_eq hz, Subgroup.mem_subgroupOf]
    have := hKC (Subgroup.mem_subgroupOf.1 hg)
    rw [mem_centralizerIn] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact this.2
  have horb' : (K.subgroupOf P).index ≤
      (Set.range fun g : P => g • {p : Fin n | (⟨z, hz⟩ : P) • p = p}).ncard := horb
  obtain ⟨h1, h2⟩ := fixed_point_set_orbit_centralizer_bound (⟨z, hz⟩ : P) _ hH horb'
  have hstab : K.subgroupOf P = MulAction.stabilizer P {p : Fin n | (⟨z, hz⟩ : P) • p = p} := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← h2 g, ← h1]
  rw [hstab, MulAction.index_stabilizer]
  rfl

end CFSG.ClassicalInvolution
