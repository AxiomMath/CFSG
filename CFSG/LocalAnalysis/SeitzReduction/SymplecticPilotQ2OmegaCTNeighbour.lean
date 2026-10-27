module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldParam
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial HasBLift centerQuotientAut
  centerQuotientAut_mk)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem nsCore_omega_facts_two {m : ℕ} (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G} (hX : X = modelToG e (nsTorusSp K k))
    {D : Subgroup G} (hD : D = modelToG e (complSp K k)) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : HR8KindAtSp t m 1 X D κ)
    (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    Sp2mKindType (centralizerPerfectCore X) m 1 κ ∧
      (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ ∉
        (MulAut.conj : centralizerPerfectCore X →* MulAut (centralizerPerfectCore X)).range ∧
      LieModel (fixedSubgroup ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩))
        .PSp m 2 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK, pow_one])
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨htX, Kb, hKb, -, hcase⟩ := h
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => by
    rcases hκ with rfl | rfl <;> cases h.1
  have hSchur : OddSchurTrivial (Kb ⧸ center Kb) := oddSchurTrivial_of_sp2mKindType_omega hκ hty
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  have hinj1 : Function.Injective (QuotientGroup.mk' (center Kb)) :=
    hSchur Kb hKbP (QuotientGroup.mk' (center Kb)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']; exact hov.2.1)
  let e₁ : Kb ≃* Kb ⧸ center Kb :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center Kb)) ⟨hinj1, QuotientGroup.mk'_surjective _⟩
  have ht' : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 := Subtype.ext htt
  have hsC : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ≠ 1 :=
    fun h1 => hsK (h1 ▸ one_mem Kb)
  have hs2 : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, ht', map_one]) hs1
  have hDt : D ≤ centralizer ({t} : Set G) := by
    rw [hD]
    exact fun d hd => mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 htC d (UnitaryPilot.modelToG_le e _ hd))
  have hsD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) : Subgroup _) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nsTorusSp_of_seitzSetting hset hK hm e htC ht k
    hX htX hD
  have hOut : Group.IsSolvable (Outer Kb) := by
    have : Group.IsSolvable (Outer (Kb ⧸ center Kb)) :=
      isSolvable_outer_of_sp2mKindType_omega hκ hty
    exact solvable_of_equiv e₁.symm
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  obtain ⟨-, -, hBall⟩ := bLift_neighbour_nsTorusSp_of_seitzSetting hset hK hm e htC ht k hX
    htX hD
  have hB : HasBLift Kb := hBall Kb (isPerfect_iff.mp hKbP) hsN
    (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ centralizer (X : Set G) :=
    F4Pilot.centralizerPerfectCore_le_centralizer X
  have hmemO : ∀ y : qh.ker, (Subgroup.inclusion hle) (y : centralizerPerfectCore X) ∈
      oddCore (centralizer (X : Set G)) := by
    intro y
    have h1 := hqapp (y : centralizerPerfectCore X)
    rw [MonoidHom.mem_ker.1 y.2] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1.symm
  let φ : qh.ker →* oddCore (centralizer (X : Set G)) :=
    ((Subgroup.inclusion hle).comp qh.ker.subtype).codRestrict _ hmemO
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg
      (fun z : oddCore (centralizer (X : Set G)) => ((z : centralizer (X : Set G)) : G)) hab))
  have hkodd : Odd (Nat.card qh.ker) :=
    Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (Subgroup.card_dvd_of_injective φ hφinj)
  let η : centralizerPerfectCore X →* Kb ⧸ center Kb := e₁.toMonoidHom.comp qh
  have hηs : Function.Surjective η := e₁.surjective.comp hqs
  have hker : η.ker = qh.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have hinj := hSchur (centralizerPerfectCore X) hEperf η hηs (hker ▸ hqker) (hker ▸ hkodd)
  let ηe : centralizerPerfectCore X ≃* Kb ⧸ center Kb := MulEquiv.ofBijective η ⟨hinj, hηs⟩
  have hθ : ∀ y : centralizerPerfectCore X,
      qh ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) =
        Kb.normalizerMonoidHom ⟨_, hsN⟩ (qh y) := by
    intro y
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp]
    have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y :
        centralizerPerfectCore X) : G), hle ((centralizerPerfectCore X).normalizerMonoidHom
          ⟨t, hN⟩ y).2⟩ : centralizer (X : Set G)) =
        ⟨t, htX⟩ * ⟨(y : G), hle y.2⟩ * ⟨t, htX⟩⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [e1, map_mul, map_mul, map_inv]
  have hθη : MulAut.congr ηe ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩) =
      centerQuotientAut (Kb.normalizerMonoidHom ⟨_, hsN⟩) := by
    ext z
    obtain ⟨y, rfl⟩ := ηe.surjective z
    change ηe ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ (ηe.symm (ηe y))) =
      centerQuotientAut (Kb.normalizerMonoidHom ⟨_, hsN⟩) (ηe y)
    rw [MulEquiv.symm_apply_apply]
    change QuotientGroup.mk' (center Kb) (qh ((centralizerPerfectCore X).normalizerMonoidHom
        ⟨t, hN⟩ y)) =
      centerQuotientAut (Kb.normalizerMonoidHom ⟨_, hsN⟩) (QuotientGroup.mk' (center Kb) (qh y))
    rw [centerQuotientAut_mk, hθ]
  refine ⟨sp2mKindType_of_mulEquiv ηe.symm hty, ?_, ?_⟩
  ·
    rintro ⟨z, hz⟩
    apply hov.1
    refine ⟨qh z, MulEquiv.ext fun w => ?_⟩
    obtain ⟨y, rfl⟩ := hqs w
    rw [MulAut.conj_apply, ← hθ y, ← hz, MulAut.conj_apply, map_mul, map_mul, map_inv]
  ·
    have h1 := hov.2.2.2
    rw [← hθη] at h1
    exact LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ηe _).symm h1

theorem nsCore_inf_centralizer_eq_of_omega_two {m : ℕ} (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : NsKindSp e t k κ) :
    centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓ centralizer ({t} : Set G) =
      modelToG e (complSp K k) := by
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (nsTorusSp K k)) : Set G) :=
    UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _
  obtain ⟨-, -, hfix⟩ := nsCore_omega_facts_two hset hK hm e htC ht k rfl rfl hκ h hN
  have hq : IsQuasisimple (fixedSubgroup
      ((centralizerPerfectCore (modelToG e (nsTorusSp K k))).normalizerMonoidHom ⟨t, hN⟩)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv
      (isComponent_top_of_lieModel_PSp hfix).1.1
  have hFperf := isPerfect_iff.mp hq.1
  have hmap : (fixedSubgroup
      ((centralizerPerfectCore (modelToG e (nsTorusSp K k))).normalizerMonoidHom ⟨t, hN⟩)).map
        (centralizerPerfectCore (modelToG e (nsTorusSp K k))).subtype =
        centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓ centralizer ({t} : Set G) :=
    map_eqLocus_normalizerMonoidHom_eq hN
  have hperf : ⁅centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓ centralizer ({t} : Set G),
      centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓ centralizer ({t} : Set G)⁆ =
        centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓ centralizer ({t} : Set G) := by
    rw [← hmap, ← Subgroup.map_commutator, hFperf]
  rw [← perfectCore_centralizerPerfectCore_nsTorusSp_inf_centralizer hset hK hm e htC ht k,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]

theorem map_fixedSubgroup_eq_of_comm_two {m : ℕ} (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : NsKindSp e t k κ) {P : Type} [Group P]
    (ψ : P ≃* centralizerPerfectCore (modelToG e (nsTorusSp K k))) (α : MulAut P)
    (hψ : ∀ x, t * ((ψ x : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) * t⁻¹ =
      ((ψ (α x) : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G)) :
    ((fixedSubgroup α).map ψ.toMonoidHom).map
        (centralizerPerfectCore (modelToG e (nsTorusSp K k))).subtype =
      modelToG e (complSp K k) := by
  rw [← nsCore_inf_centralizer_eq_of_omega_two hset hK hm e htC ht k hκ h]
  ext g
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨(ψ x).2, mem_centralizer_singleton_iff.2 ?_⟩
    have hαx : α x = x := hx
    have h1 := hψ x
    rw [hαx] at h1
    change ((ψ x : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) * t =
      t * ((ψ x : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G)
    calc ((ψ x : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) * t =
          t * ((ψ x : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) * t⁻¹ * t := by
            rw [h1]
      _ = t * ((ψ x : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) := by group
  · intro hg
    obtain ⟨hgE, hgt⟩ := mem_inf.1 hg
    refine ⟨⟨g, hgE⟩, ⟨ψ.symm ⟨g, hgE⟩, ?_, MulEquiv.apply_symm_apply ψ _⟩, rfl⟩
    change α (ψ.symm ⟨g, hgE⟩) = ψ.symm ⟨g, hgE⟩
    apply ψ.injective
    apply Subtype.ext
    rw [← hψ, MulEquiv.apply_symm_apply]
    change t * g * t⁻¹ = g
    rw [mem_centralizer_singleton_iff] at hgt
    rw [← hgt, mul_inv_cancel_right]

end Lift

end CFSG.SeitzReduction.SymplecticPilot
