module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryTwoMultiplier

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.CentralExt

namespace CFSG.LieType.Steinberg.CentralExt.SUEvenTwo

theorem statedScalars_subgroupOf_le_center (n q : ℕ) (F : Type) [Field F] :
    (StatedScalars (Fin n) F).subgroupOf (StatedSU n q F) ≤
      Subgroup.center (StatedSU n q F) :=
  fun z hz => by
    have hz' : (z : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
      have h1 := Subgroup.mem_subgroupOf.1 hz
      rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hz' h)

section Certificates


theorem statedSU_exists_section_of_central_two
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2)
    {n : ℕ} (he : Even n) (hn : 8 ≤ n)
    {E : Type} [Group E] [Finite E] {π : E →* StatedSU n (2 ^ 1) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : StatedSU n (2 ^ 1) F →* E, ∀ g, π (s g) = g := by
  have h2 : n % 2 = 0 := Nat.even_iff.1 he
  obtain ⟨r, rfl⟩ : ∃ r, n = 2 * r := ⟨n / 2, by omega⟩
  have hr : 4 ≤ r := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect (StatedSU (2 * r) (2 ^ 1) F) :=
    SUClosed.isPerfect_statedSU hF (by omega)
  exact CoverAssembly.exists_section_of_cover_and_coprime (p := 2)
    (θ := QuotientGroup.mk'
      ((StatedScalars (Fin (2 * r)) F).subgroupOf (StatedSU (2 * r) (2 ^ 1) F)))
    (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact statedScalars_subgroupOf_le_center (2 * r) (2 ^ 1) F)
    (fun P _ _ _ η hη hC hp2 =>
      (even_even_dimensional_unitary_prime_field_central_two_cover_trivial η hη hC hp2 hr
        (SUClosed.lieModel_psu_two hF (by omega))).1)
    (fun E _ _ π hπ hcen hc =>
      SUClosed.statedSU_exists_section_of_coprime hF ⟨r, two_mul r⟩ (by omega) E π hπ hcen hc)
    E π hπ hcen

end Certificates

end CFSG.LieType.Steinberg.CentralExt.SUEvenTwo
