module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2GlobalTables
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitLayer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowKinds
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2BLift
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LieType.Ree (ReeTag)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_surjective_centralizerPerfectCore_nonsplit_F4_two_graph {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {κ : Sp6Kind} (hκ : κ.IsGraphKind) (hk : TwoKindAt e t X₀ κ) :
    ∃ (S : Type) (_ : Group S), Sp6KindType S 1 κ ∧
      ∃ ρ : centralizerPerfectCore (subgroupToG e X₀) →* S, Function.Surjective ρ ∧
        ρ.ker ≤ center (centralizerPerfectCore (subgroupToG e X₀)) ∧ Odd (Nat.card ρ.ker) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨htX, hk⟩ := hk
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set D : Subgroup G := subgroupToG e (C3Levi K) with hDdef
  have hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, -, hcase⟩ := hk
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => hκ.2 h.1
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
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  have hOut : Group.IsSolvable (Outer Kb) :=
    isSolvable_outer_of_sp6KindType_graph hKbP hκ.1 hκ.2 hty
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
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore X)
  have hmemZ : ∀ y : centralizerPerfectCore X,
      y ∈ ((QuotientGroup.mk' (center Kb)).comp qh).ker → qh y ∈ center Kb := by
    intro y hy
    have hy2 : QuotientGroup.mk' (center Kb) (qh y) = 1 := hy
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy2
  refine ⟨Kb ⧸ center Kb, inferInstance, hty, (QuotientGroup.mk' (center Kb)).comp qh,
    (QuotientGroup.mk'_surjective _).comp hqs, fun y hy => ?_, ?_⟩
  · exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center qh hqker
      (hmemZ y hy)
  ·
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have hx' : orderOf (x : centralizerPerfectCore X) = 2 := by
      rw [Subgroup.orderOf_coe, hx]
    have hZ := hmemZ x x.2
    have h1 : orderOf (qh x) ∣ 2 := hx' ▸ orderOf_map_dvd qh _
    have h2 : orderOf (qh x) ∣ Nat.card (center Kb) := Subgroup.orderOf_dvd_natCard _ hZ
    have h3 : orderOf (qh x) = 1 := by
      have hodd := hov.2.1
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd h2 (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd))
    have hxk : (x : centralizerPerfectCore X) ∈ qh.ker := orderOf_eq_one_iff.1 h3
    have h4 := Subgroup.orderOf_dvd_natCard _ hxk
    rw [hx'] at h4
    exact absurd h4 (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hkodd))

end CFSG.SeitzReduction.F4Pilot
