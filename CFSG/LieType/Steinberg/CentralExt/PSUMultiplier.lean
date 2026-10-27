module

public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

namespace CFSG.LieType.Steinberg.CentralExt.SUClosed

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}

include hF in
theorem isPerfect_statedSU (hn : 4 ≤ n) : Group.IsPerfect (StatedSU n (p ^ f) F) := by
  have h := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF) (n := n) (by omega)
    (fun h => by omega)
  rw [SUid_eq_statedSU hF n] at h
  exact h

include hF in
theorem statedSU_exists_section_of_central
    (he : Even n) (hn : 4 ≤ n)
    (hq : 4 ≤ p ^ f) {E : Type} [Group E] [Finite E] {π : E →* StatedSU n (p ^ f) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : StatedSU n (p ^ f) F →* E, ∀ g, π (s g) = g := by
  set ψ := equivStatedSU hF n
  have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.symm.injective]
  obtain ⟨s, hs⟩ := su_exists_section_of_central hF he hn hq
    (π := ψ.symm.toMonoidHom.comp π) (ψ.symm.surjective.comp hπ) (hker ▸ hcen)
  refine ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective ?_⟩
  exact hs (ψ.symm g)

include hF in
theorem psu_hopfMultiplier
    (he : Even n) (hn : 4 ≤ n) (hq : 4 ≤ p ^ f) :
    commutator (StatedProj (StatedSU n (p ^ f) F)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSU n (p ^ f) F)) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ f + 1)))) := by
  set H := StatedSU n (p ^ f) F
  set Z := (StatedScalars (Fin n) F).subgroupOf H
  set q : H →* StatedProj H := QuotientGroup.mk' Z
  have hq' : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Z := QuotientGroup.ker_mk' _
  have hZc : Z ≤ Subgroup.center H := fun z hz => by
    have hz' : (z : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
      have h1 := Subgroup.mem_subgroupOf.1 hz
      rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hz' h)
  have : Group.IsPerfect H := isPerfect_statedSU hF hn
  have hperf : Group.IsPerfect (StatedProj H) := Group.IsPerfect.ofSurjective hq'
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover (StatedProj H)) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (StatedProj H) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq' (hker ▸ hZc)
      fun π hπ hcen => statedSU_exists_section_of_central hF he hn hq hπ hcen)
  have hcard : Nat.card Z = Nat.gcd n (p ^ f + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel hp.out hF (by omega)).2.2
  have hcyc : IsCyclic Z := (isCyclic_scalars_statedSU hF (by omega)).1
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hker).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.SUClosed
