module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLift

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift oddCoreLift)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_surjective_neighbourCore_of_field {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {X D : Subgroup G}
    (htX : t ∈ centralizer (X : Set G)) (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    (hDq : CFSG.IsQuasisimple D)
    (hXo : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hOut : Group.IsSolvable (Outer Kc)) :
    perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) =
        Kc ∧ HasBLift Kc ∧
      ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
            ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hss : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 := Subtype.ext htt
    rw [this, map_one]
  have hsC : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    intro hc
    refine hout ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, F4Pilot.coe_normalizerMonoidHom_mk_apply Kc hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ≠ 1 :=
    fun h => hsC (h ▸ one_mem _)
  have hs2 : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDLX : D ≤ L ⊓ centralizer (X : Set G) := hD ▸ map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDLX hd).1)
  have hsD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKc hDK hs2 hsD hsN hsC hsyl hOut
  have hB : HasBLift Kc := LinearPilot.hasBLift_of_forall_odd_mem htC ht hLt htX hD hDq hXo
    (isPerfect_iff.mp hKc.1.1) hsN (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKc.1 hsN hsC)
  obtain ⟨q, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ centralizer (X : Set G) :=
    F4Pilot.centralizerPerfectCore_le_centralizer X
  have hmemO : ∀ y : q.ker, (Subgroup.inclusion hle) (y : centralizerPerfectCore X) ∈
      oddCore (centralizer (X : Set G)) := by
    intro y
    have h1 := hqapp (y : centralizerPerfectCore X)
    rw [MonoidHom.mem_ker.1 y.2] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1.symm
  set φ : q.ker →* oddCore (centralizer (X : Set G)) :=
    ((Subgroup.inclusion hle).comp q.ker.subtype).codRestrict (oddCore (centralizer (X : Set G)))
      hmemO with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg
      (fun z : oddCore (centralizer (X : Set G)) => ((z : centralizer (X : Set G)) : G)) hab))
  have hkodd : Odd (Nat.card q.ker) :=
    Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (Subgroup.card_dvd_of_injective φ hφinj)
  exact ⟨hcore, hB, q, hqs, hqker, hkodd, hqapp⟩

omit [Finite G] in
theorem exists_mem_normalizer_neighbourCore_comm {X : Subgroup G} {t : G}
    (htX : t ∈ centralizer (X : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (q : centralizerPerfectCore X →* Kc)
    (hqapp : ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩) :
    ∃ htE : t ∈ normalizer (centralizerPerfectCore X : Set G),
      ∀ y : centralizerPerfectCore X,
        q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ y) =
          Kc.normalizerMonoidHom ⟨_, hsN⟩ (q y) := by
  have htN : t ∈ normalizer (X : Set G) := centralizer_le_normalizer _ htX
  have htE : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore X htN
  refine ⟨htE, fun y => Subtype.ext ?_⟩
  have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ y :
      centralizerPerfectCore X) : G), F4Pilot.centralizerPerfectCore_le_centralizer X
        ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ y).2⟩ :
          centralizer (X : Set G)) =
      ⟨t, htX⟩ * ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ *
        ⟨t, htX⟩⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp, e1, map_mul, map_mul, map_inv]

omit [Finite G] in
theorem exists_injective_neighbourCore_restrict {X D : Subgroup G}
    (hDX : D ≤ centralizer (X : Set G)) (hDq : CFSG.IsQuasisimple D) (hZD : center D = ⊥)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (q : centralizerPerfectCore X →* Kc) (hqker : q.ker ≤ center (centralizerPerfectCore X))
    (hqapp : ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩) :
    ∃ hDE : D ≤ centralizerPerfectCore X,
      Function.Injective (q.comp (Subgroup.inclusion hDE)) ∧
        (q.comp (Subgroup.inclusion hDE)).range =
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc := by
  have hDE : D ≤ centralizerPerfectCore X :=
    F4Pilot.le_centralizerPerfectCore (isPerfect_iff.mp hDq.1) hDX
  refine ⟨hDE, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro d hd
    have hdc := hqker (MonoidHom.mem_ker.2 hd)
    have hdZ : d ∈ center D := by
      rw [mem_center_iff]
      intro d'
      have h1 := mem_center_iff.1 hdc (Subgroup.inclusion hDE d')
      exact Subgroup.inclusion_injective hDE (by simpa only [map_mul] using h1)
    rw [hZD, mem_bot] at hdZ
    exact hdZ
  · ext k
    rw [mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨d, rfl⟩
      rw [MonoidHom.comp_apply, hqapp]
      exact ⟨⟨(d : G), hDX d.2⟩, mem_subgroupOf.2 d.2, rfl⟩
    · rintro ⟨d', hd', hdk⟩
      refine ⟨⟨(d' : G), mem_subgroupOf.1 hd'⟩, Subtype.ext ?_⟩
      rw [MonoidHom.comp_apply, hqapp, ← hdk]
      rfl

theorem isSolvable_outer_of_lieModel_POmegaPlus {K : Type} [Group K] {m p e : ℕ}
    (h : LieModel K .POmegaPlus m p e) : Group.IsSolvable (Outer K) :=
  (CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier
    .POmegaPlus (Or.inr (Or.inl rfl))
    (CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel (by decide) h)).2.2

theorem neighbourCore_of_field {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {X D : Subgroup G}
    (htX : t ∈ centralizer (X : Set G)) (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    (hDq : CFSG.IsQuasisimple D) (hZD : center D = ⊥)
    (hXo : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    {m f : ℕ} {tag : StatedLieTag}
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hfield : OmegaNeighbourAlternativeField
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f tag)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc) :
    ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
        normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))),
      Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
      center Kc = ⊥ ∧ LieModel Kc .POmegaPlus m 2 (2 * f) ∧
      (∀ P : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)), IsPComponent 2 P →
        P.map (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)).subtype =
            ((D.subgroupOf (centralizer (X : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc ∧
          LieModel P tag m 2 f) ∧
      ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker = center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        (∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
            ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩) ∧
        (∃ htE : t ∈ normalizer (centralizerPerfectCore X : Set G),
          ∀ y : centralizerPerfectCore X,
            q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ y) =
              Kc.normalizerMonoidHom ⟨_, hsN⟩ (q y)) ∧
        ∃ hDE : D ≤ centralizerPerfectCore X,
          Function.Injective (q.comp (Subgroup.inclusion hDE)) ∧
            (q.comp (Subgroup.inclusion hDE)).range =
              ((D.subgroupOf (centralizer (X : Set G))).map
                (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc := by
  obtain ⟨-, ⟨-, hDK, -, hsN, hout, hZ, hmodel, hall⟩ | ⟨hKt', -⟩⟩ := hfield
  · obtain ⟨-, -, q, hqs, hqker, hkodd, hqapp⟩ := exists_surjective_neighbourCore_of_field htC ht
      hLt htX hD hDq hXo hsyl hKc hDK.le hsN hout (isSolvable_outer_of_lieModel_POmegaPlus hmodel)
    refine ⟨hsN, hout, hZ, hmodel, hall, q, hqs,
      LinearPilot.ker_eq_center_of_surjective_of_center_eq_bot hqs hqker hZ, hkodd, hqapp,
      exists_mem_normalizer_neighbourCore_comm htX hsN q hqapp, ?_⟩
    have hDX : D ≤ centralizer (X : Set G) := (hD ▸ map_subtype_le _ : D ≤ L ⊓ _).trans inf_le_right
    exact exists_injective_neighbourCore_restrict hDX hDq hZD q hqker hqapp
  · exact absurd hKt hKt'

end Generic

section Tori

@[expose] def NeighbourCoreField {G : Type} [Group G] (t : G) (X D : Subgroup G)
    (htX : t ∈ centralizer (X : Set G))
    (Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    (m f : ℕ) (tag : StatedLieTag) : Prop :=
  ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))),
    Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
    center Kc = ⊥ ∧ LieModel Kc .POmegaPlus m 2 (2 * f) ∧
    (∀ P : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)), IsPComponent 2 P →
      P.map (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)).subtype =
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc ∧
        LieModel P tag m 2 f) ∧
    ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
      q.ker = center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
      (∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
        oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
          ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩) ∧
      (∃ htE : t ∈ normalizer (centralizerPerfectCore X : Set G),
        ∀ y : centralizerPerfectCore X,
          q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ y) =
            Kc.normalizerMonoidHom ⟨_, hsN⟩ (q y)) ∧
      ∃ hDE : D ≤ centralizerPerfectCore X,
        Function.Injective (q.comp (Subgroup.inclusion hDE)) ∧
          (q.comp (Subgroup.inclusion hDE)).range =
            ((D.subgroupOf (centralizer (X : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbourCoreField_pairTorus (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKcomp : IsComponent Kc)
    (hfield : OmegaNeighbourAlternativeField
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc (n - 1) f .POmegaPlus)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc) :
    NeighbourCoreField t X D htX Kc (n - 1) f .POmegaPlus := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_pairTorus hset hKc hq hn k e htC ht hX hDe
  obtain ⟨-, -, -, -, -, -, -, -, hZ, -, -⟩ := neighbour_data_pairTorus hKc hq hn k e htC hX hDe
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting hset hKc hq hn k e htC ht hX htX hDe
  exact neighbourCore_of_field htC ht hLt htX hD hDq hZ hXo hsyl hKcomp hfield hKt

theorem neighbourCoreField_minusPairTorus (hset : SeitzSetting G L) {n f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKcomp : IsComponent Kc)
    (hfield : OmegaNeighbourAlternativeField
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc (n - 1) f .POmegaMinus)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc) :
    NeighbourCoreField t X D htX Kc (n - 1) f .POmegaMinus := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  obtain ⟨-, -, -, -, -, hD, -, hDq, hZ, -, -⟩ :=
    neighbour_data_minusPairTorus hKc hq hn hirr k e htC hX hDe
  have hXo : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓
      centralizer (D : Set G), Odd (orderOf c) → c ∈ X := fun _ hc hco =>
    mem_minusPairTorus_of_odd_of_commute hset hKc hq (by omega) hirr k e htC ht hX hDe hc hco
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq hn hirr k e htC ht hX htX hDe
  exact neighbourCore_of_field htC ht hLt htX hD hDq hZ hXo hsyl hKcomp hfield hKt

end Tori

end CFSG.SeitzReduction.OmegaPilot
