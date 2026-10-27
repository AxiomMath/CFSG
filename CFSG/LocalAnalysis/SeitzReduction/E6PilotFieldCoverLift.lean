module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldCoverBLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizePSL
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.SeitzReduction.F4Pilot (F4Work HasBLift centralizerPerfectCore)

local instance e6PilotFieldCoverLiftNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Root


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem neighbourCore_high_eq_rootTorusG (e : L ≃* adjointGroup .E6 K) :
    neighbourCore e .high = centralizerPerfectCore (rootTorusG e) := by
  rw [neighbourCore_high]
  rfl

theorem modelToG_map_subtype_levi_high (e : L ≃* adjointGroup .E6 K) :
    modelToG e ((E6Neighbour.high.levi K).map (adjointGroup .E6 K).subtype) = rootLeviG e := by
  rw [modelToG, subgroupOf,
    comap_map_eq_self_of_injective (adjointGroup .E6 K).subtype_injective, E6Neighbour.levi_high]
  rfl

end Root

section Fix


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem perfectCore_neighbourCore_high_inf_centralizer {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .E6 K) :
    perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E6Neighbour.high.levi K).map (adjointGroup .E6 K).subtype) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  rw [modelToG_map_subtype_levi_high]
  set A : Subgroup (adjointGroup .E6 K) :=
    (EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K) with hA
  set X : Subgroup G := rootTorusG e with hXdef
  set D : Subgroup G := rootLeviG e with hDdef
  have hX : X = (A.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  have hDperf : ⁅D, D⁆ = D := isPerfect_iff.mp (isQuasisimple_map_a5Levi e).1
  have hDE : D ≤ neighbourCore e .high := by
    have h1 := modelToG_le_neighbourCore e (levi_le_centralizer_torus (K := K) .high)
      (by rw [modelToG_map_subtype_levi_high]; exact hDperf)
    rwa [modelToG_map_subtype_levi_high] at h1
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  set P := perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) with hPdef
  have hP : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect _
  have hPt : P ≤ centralizer ({t} : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨3, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).1⟩⟩
  have hPL : P ≤ L := std_perfect_le hw.standard hOut htC hw.orderOf_eq hP hPt
  have hPX : P ≤ centralizer (X : Set G) := by
    refine (CFSG.Quasithin.perfectCore_le _).trans (inf_le_left.trans ?_)
    rw [neighbourCore_high_eq_rootTorusG]
    exact F4Pilot.centralizerPerfectCore_le_centralizer _
  have hPLX : P ≤ L ⊓ centralizer (X : Set G) := le_inf hPL hPX
  rw [hX, F4Pilot.inf_centralizer_map_symm, centralizer_highTorusLine_eq (Or.inl rfl) hq,
    Subgroup.map_sup, Subgroup.map_sup, ← hX] at hPLX
  have hXD : X ≤ centralizer (D : Set G) := by
    rw [hX, hDe]
    exact le_centralizer_iff.mp
      (F4Pilot.map_map_symm_le_centralizer e highTorusLine_subgroupOf_le_centralizer_perpLevi)
  have hXX : X ≤ centralizer (X : Set G) := by
    rw [hX]
    exact F4Pilot.map_map_symm_le_centralizer e highTorusLine_subgroupOf_le_centralizer_self
  have hXsolv : Group.IsSolvable X := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

end Fix

section Cover


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_surjective_neighbourCore_high_of_rootFieldKind {t : G} {f : ℕ}
    (hw : F4Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E6 K) (hk : RootFieldKind e t f)
    (K₂ : Type) [Field K₂] [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) :
    ∃ p : neighbourCore e .high →* a5Levi K₂, Function.Surjective p ∧
      p.ker ≤ center (neighbourCore e .high) ∧ Odd (Nat.card p.ker) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have : CharP K₂ 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  set X : Subgroup G := rootTorusG e with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := rootLeviG e with hDdef
  obtain ⟨htX, Kb, hKb, -, -, hlt, hsK, hsN, hov, -, hmodel, -⟩ := hk
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, F4Pilot.coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hTodd : Odd (Nat.card ((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (highTorusLine_le_adjointGroup (Or.inl rfl))).toEquiv]
    exact odd_card_highTorusLine hw.one_le hw.card_eq
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_E6_of_centralizer_eq_sup hw.standard.standard htC
    hw.orderOf_eq hw.inf_eq hf hw.card_eq e (centralizer_highTorusLine_eq (Or.inl rfl) hq)
    highTorusLine_subgroupOf_le_centralizer_perpLevi highTorusLine_subgroupOf_le_centralizer_self
    hTodd (X := X) rfl htX (D := D) rfl
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := LinearPilot.exists_projectiveSL_equiv_of_lieModel_PSL hmodel
  have hOut : Group.IsSolvable (Outer Kb) :=
    LinearPilot.isSolvable_outer_of_mulEquiv (by norm_num) eF
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  have hB : HasBLift Kb := hasBLift_rootTorusG hw hf e htX (isPerfect_iff.mp hKb.1.1) hsN
    (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ H := F4Pilot.centralizerPerfectCore_le_centralizer X
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
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K₂
  have hc : Fintype.card F = Fintype.card K₂ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hK₂]
  set η : Kb ≃* a5Levi K₂ := (eF.trans (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
    (FiniteField.ringEquivOfCardEq hc))).trans (a5LeviProjEquiv K₂) with hη
  set ι : neighbourCore e .high ≃* centralizerPerfectCore X :=
    MulEquiv.subgroupCongr (neighbourCore_high_eq_rootTorusG e) with hι
  set p : neighbourCore e .high →* a5Levi K₂ :=
    (η.toMonoidHom.comp qh).comp ι.toMonoidHom with hp
  have hpker : p.ker = qh.ker.map ι.symm.toMonoidHom := by
    ext y
    rw [MonoidHom.mem_ker, hp, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker]
    constructor
    · intro hy
      exact ⟨ι y, hy, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  refine ⟨p, (η.surjective.comp hqs).comp ι.surjective, ?_, ?_⟩
  · rw [hpker]
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro y
    have h1 := mem_center_iff.1 (hqker hz) (ι y)
    apply ι.injective
    simpa using h1
  · rw [hpker, card_map_of_injective ι.symm.injective]
    exact hkodd

end Cover

end CFSG.SeitzReduction.E6Pilot
