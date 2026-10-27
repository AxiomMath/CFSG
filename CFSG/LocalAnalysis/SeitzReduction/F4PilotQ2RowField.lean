module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowCat
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowSwapParam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LieType.Ree (ReeTag)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 {t : G} {f : ℕ}
    (hw : F4Work L K t f) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = Nat.card K + 1) :
    perfectCore (centralizerPerfectCore (subgroupToG e X₀) ⊓ centralizer ({t} : Set G)) =
      subgroupToG e (C3Levi K) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set D : Subgroup G := subgroupToG e (C3Levi K) with hDdef
  have hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  obtain ⟨hcen, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀
  have hDperf : ⁅D, D⁆ = D := isPerfect_iff.mp (isQuasisimple_map_C3Levi e).1
  have hDH : D ≤ centralizer (X : Set G) := map_map_symm_le_centralizer e hX₀D
  have hDE : D ≤ centralizerPerfectCore X := CFSG.Quasithin.le_perfectCore_of_perfect hDH hDperf
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  set P := perfectCore (centralizerPerfectCore X ⊓ centralizer ({t} : Set G)) with hPdef
  have hP : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect _
  have hPt : P ≤ centralizer ({t} : Set G) := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hPL : P ≤ L := std_perfect_le hw.standard (isSolvable_outer_of_mulEquiv_F4 e) htC
    hw.orderOf_eq hP hPt
  have hPX : P ≤ centralizer (X : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans
      (inf_le_left.trans (centralizerPerfectCore_le_centralizer _))
  have hPLX : P ≤ L ⊓ centralizer (X : Set G) := le_inf hPL hPX
  rw [hX, inf_centralizer_map_symm, hcen, Subgroup.map_sup, Subgroup.map_sup, ← hX, ← hDe]
    at hPLX
  have hXD : X ≤ centralizer (D : Set G) := le_centralizer_iff.mp hDH
  have hXX : X ≤ centralizer (X : Set G) :=
    map_map_symm_le_centralizer e (le_centralizer_self_of_isCyclic hcyc)
  have hXsolv : Group.IsSolvable X := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

theorem nonempty_statedSp_mulEquiv_centralizerPerfectCore_nonsplit_F4_two {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hF : TwoKindAt e t X₀ .field) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
      Nonempty (StatedSp 3 F ≃* centralizerPerfectCore (subgroupToG e X₀)) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨htX, hk⟩ := hF
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set D : Subgroup G := subgroupToG e (C3Levi K) with hDdef
  have hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, -, hcase⟩ := hk
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => by cases h.1
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDL : D ≤ L := map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nonsplit hw.standard.standard htC hw.orderOf_eq hKt
    hw.card_eq e hXJ hcyc hX₀' hX htX hDe
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := exists_mulEquiv_statedProj_of_lieModel_PSp (by norm_num) hty
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  obtain ⟨eK⟩ := nonempty_mulEquiv_statedSp_of_centerQuotient hKbP hov.2.1 eF
  have hOut : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism (eK.trans (c3LeviEquiv F))).2.mpr
      (isSolvable_outer_C3Levi hF)
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  have hlayer : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) :=
    (inSubgroup_layer_inf_centralizer_nonsplit e hXJ hcyc hX₀').symm
  obtain ⟨hcen, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀'
  have hLX : L ⊓ centralizer (X : Set G) ≤ X ⊔ D := by
    rw [hX, hDe, inf_centralizer_map_symm, hcen, Subgroup.map_sup, Subgroup.map_sup]
  have hDH : D ≤ centralizer (X : Set G) := map_map_symm_le_centralizer e hX₀D
  have hDq : CFSG.IsQuasisimple D := isQuasisimple_map_C3Levi e
  let eD : C3Levi K ≃* D :=
    ((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)
  have hZD : center D = ⊥ := center_eq_bot_congr eD center_C3Levi_eq_bot
  have hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X :=
    SeitzQ2.inf_centralizer_le_of_le_sup hLX (le_centralizer_iff.1 hDH) hZD
  have hOutL : IsPGroup 2 (Outer L) := SeitzQ2.isPGroup_outer_of_mulEquiv_F4_two hK2 e
  have ht1 : t ≠ 1 := fun h => by
    have h2 := hw.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have htL : t ∉ L := LinearPilot.not_mem_of_mem_centralizer hw.center_eq_bot htC ht1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hw.standard.standard htC hw.orderOf_eq
  have hB : HasBLift Kb := SeitzQ2.hasBLift_of_isPGroup_outer hOutL htC hw.orderOf_eq htL hCN
    hKt htX hlayer hDq hXD (isPerfect_iff.mp hKbP) hsN
    (le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ H := centralizerPerfectCore_le_centralizer X
  have hmemO : ∀ y : qh.ker, (Subgroup.inclusion hle) (y : centralizerPerfectCore X) ∈
      oddCore H := by
    intro y
    have h1 := hqapp (y : centralizerPerfectCore X)
    rw [MonoidHom.mem_ker.1 y.2] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1.symm
  set φ : qh.ker →* oddCore H :=
    ((Subgroup.inclusion hle).comp qh.ker.subtype).codRestrict (oddCore H) hmemO with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : oddCore H => ((z : H) : G)) hab))
  have hkodd : Odd (Nat.card qh.ker) :=
    Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (Subgroup.card_dvd_of_injective φ hφinj)
  set η : centralizerPerfectCore X →* StatedSp 3 F := eK.toMonoidHom.comp qh with hη
  have hηs : Function.Surjective η := eK.surjective.comp hqs
  have hker : η.ker = qh.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact MulEquiv.map_eq_one_iff eK
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore X)
  have hinj := oddSchurTrivial_statedSp 3 F (centralizerPerfectCore X) hEperf η hηs
    (hker ▸ hqker) (hker ▸ hkodd)
  exact ⟨F, inferInstance, inferInstance, inferInstance, by rw [hF]; norm_num,
    ⟨(MulEquiv.ofBijective η ⟨hinj, hηs⟩).symm⟩⟩

open CFSG.SeitzReduction.SeitzQ2 (SwapParam)

@[expose] def TwoFieldPairParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
      Nonempty (StatedSp 3 F ≃* centralizerPerfectCore (subgroupToG e X₀)) →
    ∀ (F' : Type) [Field F'] [Finite F'] [CharP F' 2], Nat.card F' = 4 →
      Nonempty (StatedSp 3 F' ≃*
        centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) →
      perfectCore (centralizerPerfectCore (subgroupToG e X₀) ⊓ centralizer ({t} : Set G)) =
        subgroupToG e (C3Levi K) →
      perfectCore (centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀) ⊓
          centralizer ({t} : Set G)) = subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K) →
      False

theorem twoFieldPairInput_of_paramInput (h : TwoFieldPairParamInput) : TwoFieldPairInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hX hY
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨F, _, _, _, hF, hiso⟩ :=
    nonempty_statedSp_mulEquiv_centralizerPerfectCore_nonsplit_F4_two hw e hXJ hcyc hX₀ hX
  obtain ⟨F', _, _, _, hF', hiso'⟩ :=
    nonempty_statedSp_mulEquiv_centralizerPerfectCore_nonsplit_F4_two hw
      (e.trans (graphAutF4 K).symm) hXJ hcyc hX₀ hY
  exact h G L K e t hw X₀ hXJ hcyc hX₀ F hF hiso F' hF' hiso'
    (perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀')
    (perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw _ hXJ hcyc hX₀')

@[expose] def TwoSwapPairParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
    ∀ P : SwapParam t (subgroupToG e (C3Levi K)), Function.Injective P.Ψ →
      P.Ψ.range = centralizerPerfectCore (subgroupToG e X₀) →
    ∀ P' : SwapParam t (subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K)),
      Function.Injective P'.Ψ →
      P'.Ψ.range = centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀) →
      False

theorem twoSwapPairInput_of_paramInput (h : TwoSwapPairParamInput) : TwoSwapPairInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hX hY
  obtain ⟨P, hinj, hrange⟩ := exists_swapParam_nonsplit_F4_two hw e hXJ hcyc hX₀ hX
  obtain ⟨P', hinj', hrange'⟩ :=
    exists_swapParam_nonsplit_F4_two hw (e.trans (graphAutF4 K).symm) hXJ hcyc hX₀ hY
  exact h G L K e t hw X₀ hXJ hcyc hX₀ P hinj hrange P' hinj' hrange'

end CFSG.SeitzReduction.F4Pilot
