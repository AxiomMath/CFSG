module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Model

theorem exists_mulEquiv_statedProj_of_lieModel_PSp {S : Type} [Group S] {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel S .PSp n p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (S ≃* StatedProj (StatedSp n F)) := by
  rcases h with ⟨-, -, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals exact absurd h0 hn


theorem nonempty_mulEquiv_statedSp_of_centerQuotient {Kc : Type} [Group Kc] [Finite Kc]
    (hKc : Group.IsPerfect Kc) (hodd : Odd (Nat.card (center Kc))) {F : Type} [Field F]
    [Finite F] [CharP F 2] (eF : Kc ⧸ center Kc ≃* StatedProj (StatedSp 3 F)) :
    Nonempty (Kc ≃* StatedSp 3 F) := by
  set ε : Kc ⧸ center Kc ≃* StatedSp 3 F := eF.trans (spProjEquiv 3 F).symm with hε
  set η : Kc →* StatedSp 3 F := ε.toMonoidHom.comp (QuotientGroup.mk' (center Kc)) with hη
  have hs : Function.Surjective η := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Kc := by
    ext x
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hinj := oddSchurTrivial_statedSp 3 F Kc hKc η hs hker.le (hker ▸ hodd)
  exact ⟨MulEquiv.ofBijective η ⟨hinj, hs⟩⟩

end Model

section Core


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem nonempty_statedSp_mulEquiv_neighbourCore_X {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .field) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (StatedSp 3 F ≃* neighbourCore e .X) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  set X : Subgroup G := neighbourTorusG e .X with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := neighbourLeviG e .X with hDdef
  obtain ⟨htX, Kb, hKb, -, hcase⟩ := hX
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
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_torusLineR hw.standard.standard htC hw.orderOf_eq
    hw.inf_eq hf hw.card_eq e (X := X) rfl htX (D := D) rfl
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := exists_mulEquiv_statedProj_of_lieModel_PSp (by norm_num) hty
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  obtain ⟨eK⟩ := nonempty_mulEquiv_statedSp_of_centerQuotient hKbP hov.2.1 eF
  have hOut : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism (eK.trans (c3LeviEquiv F))).2.mpr
      (isSolvable_outer_C3Levi hF)
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  have hTodd : Odd (Nat.card ((torusLineR K).subgroupOf (adjointGroup .F4 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe torusLineR_le_adjointGroup).toEquiv]
    exact odd_card_torusLineR hw.one_le hw.card_eq
  have hC := mem_center_of_mem_oddCore_of_commute_sup hw.card_eq hw.standard.standard htC
    hw.orderOf_eq hw.inf_eq e (centralizer_torusLineR_eq hq) torusLineR_subgroupOf_le_centralizer
    torusLineR_subgroupOf_le_centralizer_self hTodd le_rfl (X := X) rfl htX (D := D) rfl
  have hB : HasBLift Kb := hasBLift_of_le_center ht't' (isPerfect_iff.mp hKbP) hsN
    (le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC) hC
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
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore X)
  have hinj := oddSchurTrivial_statedSp 3 F (centralizerPerfectCore X) hEperf η hηs
    (hker ▸ hqker) (hker ▸ hkodd)
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    ⟨(MulEquiv.ofBijective η ⟨hinj, hηs⟩).symm⟩⟩

theorem nonempty_statedSp_mulEquiv_neighbourCore_Y {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) (hY : HR8Kind e t f .Y .field) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (StatedSp 3 F ≃* neighbourCore e .Y) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
  rw [neighbourCore_Y_eq_X]
  exact nonempty_statedSp_mulEquiv_neighbourCore_X hw hf _ ((hr8Kind_Y_iff_X e).1 hY)

theorem nonempty_statedSp_mulEquiv_neighbourCore {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .field) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (StatedSp 3 F ≃* neighbourCore e N) := by
  cases N
  · exact nonempty_statedSp_mulEquiv_neighbourCore_X hw hf e h
  · exact nonempty_statedSp_mulEquiv_neighbourCore_Y hw hf e h
  · exact absurd rfl hN

theorem nonempty_levi_mulEquiv_neighbourCore {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .field) (K₂ : Type) [Field K₂] [Finite K₂] [CharP K₂ 2]
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) : Nonempty (N.levi K₂ ≃* neighbourCore e N) := by
  obtain ⟨F, _, _, _, hF, ⟨ψ⟩⟩ := nonempty_statedSp_mulEquiv_neighbourCore hw hf e hN h
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K₂
  have hc : Fintype.card K₂ = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₂, hF]
  exact ⟨((neighbourLeviEquiv K₂ N).symm.trans
    (statedSpCongr (FiniteField.ringEquivOfCardEq hc) 3)).trans ψ⟩

end Core

end CFSG.SeitzReduction.F4Pilot
