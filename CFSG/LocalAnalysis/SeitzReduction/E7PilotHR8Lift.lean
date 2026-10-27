module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourBLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftSchur
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotHR8

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.LieType.Universal.Spin (quadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.OmegaPilot (OmegaOvergroup)


theorem injective_of_surjective_of_le_center_spinPlus {F : Type} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) {P : Type*} [Group P] [Group.IsPerfect P]
    (π : P →* spinGroup (quadPlus 6 F)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center P) : Function.Injective π := by
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_exists_section_of_central
      three_le_rank_D6 hF hπ hker
  exact F4Pilot.injective_of_section_of_perfect π hker σ hσ

theorem exists_spinGroup_mulEquiv_of_lieModel {Y : Type} [Group Y] {Kc : Subgroup Y}
    (hKc : CFSG.IsQuasisimple Kc) {f : ℕ} (hf : 1 ≤ f)
    (hm : LieModel (Kc ⧸ center Kc) .POmegaPlus 6 2 (2 * f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (Kc ≃* spinGroup (quadPlus 6 F)) := by
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := statedClassicalModel_of_lieModel_POmegaPlus_E7 hm
  have : CharP F 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hF
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hZ := center_spinGroup_quadPlus_eq_bot F
  set ε : Kc ⧸ center Kc ≃* spinGroup (quadPlus 6 F) :=
    (eF.trans (CFSG.LieType.Universal.Spin.spinQuotientCenterEquivQuadPlus
      three_le_rank_D6).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with hε
  set η : Kc →* spinGroup (quadPlus 6 F) := ε.toMonoidHom.comp (QuotientGroup.mk' (center Kc))
    with hη
  have hηs : Function.Surjective η := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Kc := by
    ext x
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : Group.IsPerfect Kc := hKc.1
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    ⟨MulEquiv.ofBijective η ⟨injective_of_surjective_of_le_center_spinPlus hF4 η hηs hηker.le,
      hηs⟩⟩⟩

section Core

variable {G : Type} [Group G] [Finite G]

theorem nonempty_spinGroup_mulEquiv_centralizerPerfectCore_of_omegaOvergroup {X : Subgroup G}
    {t : G} (ht : orderOf t = 2) (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDt : D ≤ centralizer ({t} : Set G)) {f : ℕ} (hf : 1 ≤ f)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hC : ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)))
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : IsComponent Kb)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kb)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hov : OmegaOvergroup Kb (Kb.normalizerMonoidHom ⟨_, hsN⟩) 6 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (spinGroup (quadPlus 6 F) ≃* centralizerPerfectCore X) := by
  set π := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) with hπ
  set t' : centralizer (X : Set G) := ⟨t, htX⟩ with ht'def
  set s : (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) := π t' with hsdef
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer
      (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, F4Pilot.coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hsK : s ∉ Kb := fun hsK =>
    hov.1 (F4Pilot.normalizerMonoidHom_mem_range_conj Kb hsN hsK)
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hsD : s ∈ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hlist : LieModel (Kb ⧸ center Kb) .POmegaPlus 6 2 (2 * f) :=
    hov.2.2.resolve_right (OmegaPilot.not_omegaSmall_of_ne (six_ne_four_pair f))
  obtain ⟨F, _, _, _, hF, ⟨eK⟩⟩ := exists_spinGroup_mulEquiv_of_lieModel hKb.1 hf hlist
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hOut : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
      (eK.trans (spinEquivPerpLevi F))).2.mpr isSolvable_outer_perpLevi_E7
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot (centralizer (X : Set G))) hKb hDK hs2 hsD
    hsN hsC hsyl hOut
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  have hB : F4Pilot.HasBLift Kb := F4Pilot.hasBLift_of_le_center ht't' (isPerfect_iff.mp hKbP)
    hsN (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC) hC
  obtain ⟨qh, hqs, hqker, -⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  set η' : centralizerPerfectCore X →* spinGroup (quadPlus 6 F) := eK.toMonoidHom.comp qh
    with hη'
  have hη's : Function.Surjective η' := eK.surjective.comp hqs
  have hη'ker : η'.ker = qh.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have hinj := injective_of_surjective_of_le_center_spinPlus hF4 η' hη's (hη'ker ▸ hqker)
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    ⟨(MulEquiv.ofBijective η' ⟨hinj, hη's⟩).symm⟩⟩

end Core

section Torus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem nonempty_spinGroup_mulEquiv_centralizerPerfectCore_E7
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
    {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E7 K), A ≤ posJE7 K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : IsComponent Kb)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kb)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hov : OmegaOvergroup Kb (Kb.normalizerMonoidHom ⟨_, hsN⟩) 6 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (spinGroup (quadPlus 6 F) ≃* centralizerPerfectCore X) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := by
    rw [hKc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd => by
    rw [hDe] at hd
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have hsylC : (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G)) := by
    rcases hX with ⟨A, hAJ, hcyc, hA, hX⟩ | hX
    · exact ⟨(neighbour_standard_E7_nonsplit hL htC ht hK hKc hq e hAJ hA hcyc hX htX hDe).2.1,
        mem_center_of_mem_oddCore_of_commute_nonsplit_E7 hL htC ht hK hKc hq e hAJ hA hcyc hX htX⟩
    · exact ⟨(neighbour_standard_E7_highTorusLine hL htC ht hK hKc hq e hX htX hDe).2.1,
        mem_center_of_mem_oddCore_of_commute_highTorusLine_E7 hL htC ht hK hKc hq e hX htX⟩
  exact nonempty_spinGroup_mulEquiv_centralizerPerfectCore_of_omegaOvergroup ht htX hDt
    (by omega) hsylC.1 hsylC.2 hKb hDK hsN hov

theorem nonempty_perpLevi_mulEquiv_centralizerPerfectCore_E7
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
    {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E7 K), A ≤ posJE7 K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : IsComponent Kb)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kb)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hov : OmegaOvergroup Kb (Kb.normalizerMonoidHom ⟨_, hsN⟩) 6 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (EPilot.perpLevi .E7 F ≃* centralizerPerfectCore X) := by
  obtain ⟨F, _, _, _, hF, ⟨Ψ⟩⟩ := nonempty_spinGroup_mulEquiv_centralizerPerfectCore_E7 hL htC ht
    hK hf hKc e hX htX hDe hKb hDK hsN hov
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF, ⟨(spinEquivPerpLevi F).symm.trans Ψ⟩⟩

end Torus

end CFSG.SeitzReduction.E7Pilot
