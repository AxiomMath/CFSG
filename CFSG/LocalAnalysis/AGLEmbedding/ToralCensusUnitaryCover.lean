module

public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PerfectOddCoverLift
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.Open.Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace ToralCensus


theorem statedSU_exists_section_of_odd {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 3 ≤ n) (hq : (n, 2 ^ f) ≠ (3, 2))
    {E : Type} [Group E] [Finite E] {π : E →* StatedSU n (2 ^ f) K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ∃ s : StatedSU n (2 ^ f) K →* E, ∀ g, π (s g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases he : Even n
  · set ψ := CFSG.LieType.Universal.Unitary.equivStatedSU hK n
    have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ ψ.symm.injective]
    obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_coprime
      hK he (by omega) (π := ψ.symm.toMonoidHom.comp π) (ψ.symm.surjective.comp hπ)
      (hker ▸ hcen) (by rw [hker]; exact Nat.coprime_two_left.mpr hodd)
    exact ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective (hs (ψ.symm g))⟩
  · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hK hf
      hn he hq hπ hcen

end ToralCensus

@[expose] def KFactCoverUnitary : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    Odd (Nat.card (Subgroup.center ↥L)) →
    ∀ (n q : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = q ^ 2 → 3 ≤ n →
    (n, q) ≠ (3, 2) →
    ∀ e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n q K),
    ∃ ρ : StatedSU n q K →* ↥L, Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (StatedSU n q K) ∧
      ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n q K))


theorem kFactCoverUnitary : KFactCoverUnitary := by
  intro Y _ _ L hL hodd n q K _ _ _ hK hn hq e
  obtain ⟨f, hf, rfl⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have : Group.IsPerfect L := ⟨hL.2.2.1⟩
  set H := StatedSU n (2 ^ f) K
  set D : Subgroup H := (StatedScalars (Fin n) K).subgroupOf H
  obtain ⟨hsurj, hcen, hdvd⟩ := CFSG.SectionRank.EvenCover.pullbackFst_centralQuotientMap
    (D := D) e
  obtain ⟨σ, hσ⟩ := ToralCensus.statedSU_exists_section_of_odd hK hf hn hq hsurj hcen
    (Odd.of_dvd_nat hodd hdvd)
  set ρ : H →* L := (MonoidHom.snd H L).comp
    ((CFSG.SectionRank.EvenCover.pullback (CFSG.SectionRank.EvenCover.centralQuotientMap e)
      (QuotientGroup.mk' D)).subtype.comp σ) with hρ
  have hcomp := CFSG.SectionRank.EvenCover.comp_snd_section σ hσ
  have hker := CFSG.SectionRank.EvenCover.ker_centralQuotientMap e
  obtain ⟨hρs, hρk, -⟩ := CFSG.ShultStronglyClosedTI.PerfectOddCover.lift_surjective_ker
    (QuotientGroup.mk'_surjective D) hker.le hcomp
  refine ⟨ρ, hρs, fun g hg => ?_, fun g => DFunLike.congr_fun hcomp g⟩
  have hgD : g ∈ D := by
    have := hρk hg
    rwa [QuotientGroup.ker_mk'] at this
  have hz : (g : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Subgroup.mem_subgroupOf.mp hgD
  exact Subgroup.mem_center_iff.mpr fun x => Subtype.ext (Subgroup.mem_center_iff.mp hz x)

end CFSG.AGLEmbedding
