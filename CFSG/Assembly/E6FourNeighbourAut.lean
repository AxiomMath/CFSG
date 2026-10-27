module

public import CFSG.Assembly.E6FourNeighbourCfg
public import CFSG.Assembly.E6FourNeighbourModel

import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Aut
import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.Assembly.OrderReductions.Helpers
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.Assembly

open Subgroup
open CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Holds


private theorem e6FourOutInner_five_adjoint {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) :
    E6FourInnerFive (adjointGroup Tag.E6 K) := by
  intro α hα
  have hE : IsElemAbelian 5 (Subgroup.zpowers α) := CFSG.Open.isElemAbelian_zpowers hα
  have hle := CFSG.LocalAnalysis.GLTheoremA.le_conj_range_of_isElemAbelian_E6
    (K := K) (f := 2) hK Nat.prime_five (by norm_num) (by norm_num) (by norm_num) hE
  exact hle (Subgroup.mem_zpowers α)

private theorem e6FourOutInner_perfect_adjoint {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) :
    E6FourInnerPerfect (adjointGroup Tag.E6 K) := by
  intro P hP
  obtain ⟨Θ, -, -, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  let Inn : Subgroup (MulAut (adjointGroup Tag.E6 K)) :=
    (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range
  have hInnNormal : Inn.Normal := CFSG.StandardType.AutSt.normal_range_conj
  haveI : Inn.Normal := hInnNormal
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).2
  haveI : IsCyclic (RingAut K) := hcyc
  letI : CommGroup (RingAut K) := IsCyclic.commGroup
  have hPker : P ≤ Θ.ker := by
    haveI : Group.IsPerfect P := hP
    have hhom : Θ.comp P.subtype = 1 :=
      CFSG.OrderReductions.Helpers.perfect_hom_to_commutative_eq_one P
        (RingAut K × Multiplicative (ZMod (exactE Tag.E6))) (Θ.comp P.subtype)
    intro p hp
    have h1 : (Θ.comp P.subtype) ⟨p, hp⟩ = 1 := by rw [hhom]; rfl
    have h2 : Θ p = 1 := h1
    simpa [MonoidHom.mem_ker] using h2
  have hcomm_d : ∀ a a' : Fin Tag.E6.rank → Kˣ,
      Commute (exactNormalAut Tag.E6 K a 1 0) (exactNormalAut Tag.E6 K a' 1 0) := by
    intro a a'
    rw [commute_iff_eq]
    rw [← rootDiagAut_eq_exactNormalAut, ← rootDiagAut_eq_exactNormalAut]
    show rootDiagAutHom Tag.E6 K a * rootDiagAutHom Tag.E6 K a' =
      rootDiagAutHom Tag.E6 K a' * rootDiagAutHom Tag.E6 K a
    rw [← map_mul, ← map_mul, mul_comm a a']
  have hker_class : ∀ α ∈ Θ.ker, ∃ a : Fin Tag.E6.rank → Kˣ,
      QuotientGroup.mk' Inn α = QuotientGroup.mk' Inn (exactNormalAut Tag.E6 K a 1 0) := by
    intro α hα
    obtain ⟨g, a, hga⟩ := (hker α).1 hα
    refine ⟨a, ?_⟩
    have hαeq : α = MulAut.conj g * exactNormalAut Tag.E6 K a 1 0 :=
      eq_conj_mul_exactNormalAut_of_apply (σ := 1) (ε := 0) fun h => by
        rw [hga h, exactQ_zero, CFSG.StandardType.AutSt.units_map_entrywiseHom_one,
          inv_one, mul_one, mul_one]
    rw [hαeq, map_mul]
    have hconj : QuotientGroup.mk' Inn (MulAut.conj g) = 1 := by
      have hmem : MulAut.conj g ∈ Inn := MonoidHom.mem_range.mpr ⟨g, rfl⟩
      have hker' : MulAut.conj g ∈ (QuotientGroup.mk' Inn).ker := by
        rwa [QuotientGroup.ker_mk']
      rwa [MonoidHom.mem_ker] at hker'
    rw [hconj, one_mul]
  have hker_comm : ⁅Θ.ker, Θ.ker⁆ ≤ Inn := by
    rw [Subgroup.commutator_le]
    intro α₁ h₁ α₂ h₂
    obtain ⟨a₁, hq₁⟩ := hker_class α₁ h₁
    obtain ⟨a₂, hq₂⟩ := hker_class α₂ h₂
    have hq : QuotientGroup.mk' Inn ⁅α₁, α₂⁆ = 1 := by
      rw [map_commutatorElement, hq₁, hq₂,
        ((hcomm_d a₁ a₂).map (QuotientGroup.mk' Inn)).commutator_eq]
    have hmem : ⁅α₁, α₂⁆ ∈ (QuotientGroup.mk' Inn).ker :=
      (MonoidHom.mem_ker (f := QuotientGroup.mk' Inn)).mpr hq
    rwa [QuotientGroup.ker_mk'] at hmem
  have hPP : ⁅P, P⁆ = P := by
    haveI : Group.IsPerfect P := hP
    exact Subgroup.commutator_eq_self
  have hPPle : ⁅P, P⁆ ≤ Inn := (Subgroup.commutator_mono hPker hPker).trans hker_comm
  exact hPP ▸ hPPle

theorem e6FourOutInner_holds : E6FourOutInner := by
  intro J _ _ hJ hZ
  obtain ⟨K, iF, iFin, iC, hK, ⟨e⟩⟩ := e6FourMark_exists_adjointGroup hJ hZ
  letI : Field K := iF
  letI : Finite K := iFin
  letI : CharP K 2 := iC
  refine ⟨?_, ?_⟩
  · exact E6FourInnerFive.of_mulEquiv e (e6FourOutInner_five_adjoint hK)
  · exact E6FourInnerPerfect.of_mulEquiv e (e6FourOutInner_perfect_adjoint hK)

end Holds

end CFSG.Assembly

end
