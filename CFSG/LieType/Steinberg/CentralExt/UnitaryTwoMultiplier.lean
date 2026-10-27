module

public import CFSG.LieType.Steinberg.CentralExt.CoverAssembly
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.Steinberg.CentralExt.SUClosed

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}

include hF in
theorem statedSU_exists_section_of_coprime
    (he : Even n) (hn : 2 ≤ n)
    (E : Type) [Group E] [Finite E] (π : E →* StatedSU n (p ^ f) F) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : p.Coprime (Nat.card π.ker)) :
    ∃ s : StatedSU n (p ^ f) F →* E, ∀ g, π (s g) = g := by
  set ψ := equivStatedSU hF n
  have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.symm.injective]
  obtain ⟨s, hs⟩ := su_exists_section_of_coprime hF he hn
    (π := ψ.symm.toMonoidHom.comp π) (ψ.symm.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hC)
  refine ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective ?_⟩
  exact hs (ψ.symm g)

theorem lieModel_psu_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ 1) ^ 2)
    (hn : 4 ≤ n) :
    CFSG.Blueprint.LieModel (StatedProj (StatedSU n (2 ^ 1) F)) .PSU n 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by omega, fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega⟩, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩

theorem psu_two_hopfMultiplier
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {r : ℕ} (hr : 4 ≤ r) :
    commutator (StatedProj (StatedSU (2 * r) (2 ^ 1) F)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSU (2 * r) (2 ^ 1) F)) ≃*
        Multiplicative (ZMod (Nat.gcd (2 * r) (2 ^ 1 + 1)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := StatedSU (2 * r) (2 ^ 1) F
  set Z := (StatedScalars (Fin (2 * r)) F).subgroupOf H
  have hZc : Z ≤ Subgroup.center H := fun z hz => by
    have hz' : (z : GL (Fin (2 * r)) F) ∈ Subgroup.center (GL (Fin (2 * r)) F) := by
      have h1 := Subgroup.mem_subgroupOf.1 hz
      rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hz' h)
  have : Group.IsPerfect H := isPerfect_statedSU hF (by omega)
  have hsplit := CoverAssembly.exists_section_of_cover_and_coprime (p := 2)
    (θ := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZc)
    (fun P _ _ _ η hη hC h2 => (even_even_dimensional_unitary_prime_field_central_two_cover_trivial
      η hη hC h2 hr (lieModel_psu_two hF (by omega))).1)
    (fun E _ _ π hπ hcen hc => statedSU_exists_section_of_coprime hF ⟨r, two_mul r⟩ (by omega) E
      π hπ hcen hc)
  obtain ⟨hperf, ⟨e⟩⟩ := CoverAssembly.hopfMultiplier_quotient Z hZc hsplit
  have hcard : Nat.card Z = Nat.gcd (2 * r) (2 ^ 1 + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (by omega)).2.2
  have hcyc : IsCyclic Z := (isCyclic_scalars_statedSU hF (by omega)).1
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end CFSG.LieType.Steinberg.CentralExt.SUClosed
