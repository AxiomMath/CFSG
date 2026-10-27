module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesLift
public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank

section SU


theorem statedSU_exists_section_of_central_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (he : Even n) (hn : 4 ≤ n)
    (hq : 4 ≤ 2 ^ f) {E : Type} [Group E] [Finite E] {π : E →* StatedSU n (2 ^ f) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) :
    ∃ s : StatedSU n (2 ^ f) F →* E, ∀ g, π (s g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := CFSG.LieType.Universal.Unitary.equivStatedSU (p := 2) hF n
  have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.symm.injective]
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_central
    (p := 2) hF he hn hq (π := ψ.symm.toMonoidHom.comp π) (ψ.symm.surjective.comp hπ)
    (hker ▸ hcen)
  exact ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective (hs (ψ.symm g))⟩

theorem statedScalars_subgroupOf_le_center {n : ℕ} {F : Type} [Field F]
    (H : Subgroup (GL (Fin n) F)) :
    (StatedScalars (Fin n) F).subgroupOf H ≤ center H := fun z hz => by
  have hz' : (z : GL (Fin n) F) ∈ center (GL (Fin n) F) := by
    have h1 := mem_subgroupOf.1 hz
    rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  exact mem_center_iff.2 fun h => Subtype.ext (mem_center_iff.1 hz' h)

end SU

section Neighbour


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_su6_cover_neighbourCore {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .unitary6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ f) ^ 2 ∧
      ∃ Φ : StatedSU 6 (2 ^ f) F →* G, Φ.range = neighbourCore e N ∧
        Φ.ker ≤ center (StatedSU 6 (2 ^ f) F) := by
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨S, _, hS, ρ, hρ, hker⟩ := exists_surjective_neighbourCore_of_hr8Kind_graph hw hf e hN
    (by decide) (by decide) h
  obtain ⟨F, _, _, hF, ⟨ε⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = (2 ^ f) ^ 2 ∧ Nonempty (S ≃* StatedProj (StatedSU 6 (2 ^ f) F)) := by
    rcases hS with ⟨-, -, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * f) (by rw [hF, ← pow_mul,
    mul_comm])
  set M := StatedSU 6 (2 ^ f) F
  set π : M →* StatedProj M := QuotientGroup.mk' ((StatedScalars (Fin 6) F).subgroupOf M)
  set ρ' : neighbourCore e N →* StatedProj M := ε.toMonoidHom.comp ρ
  have hρ' : Function.Surjective ρ' := ε.surjective.comp hρ
  have hker' : ρ'.ker ≤ center (neighbourCore e N) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact ε.map_eq_one_iff.mp hx
  have : Group.IsPerfect (neighbourCore e N) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := exists_lift_of_central π (QuotientGroup.mk'_surjective _)
    (fun E' _ _ π' hπ' hcen' => statedSU_exists_section_of_central_two hF (by decide)
      (by norm_num) hq4 hπ' hcen') ρ' hρ' hker'
  refine ⟨F, inferInstance, inferInstance, hF, (neighbourCore e N).subtype.comp Φ₀, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
  · intro g hg
    have hg₀ : Φ₀ g = 1 := (neighbourCore e N).subtype_injective (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact statedScalars_subgroupOf_le_center M h1

end Neighbour

end CFSG.SeitzReduction.F4Pilot
