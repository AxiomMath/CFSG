module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryLift
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNormal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift centerQuotientAut
  centerQuotientAut_mk)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

theorem isSolvable_outer_of_sp2mKindType_linearUnitary {S : Type} [Group S]
    (hS : Group.IsPerfect S) {m f : ℕ} (hm : 2 ≤ m) {κ : Sp2mKind} (hκ : IsLinearUnitaryKind κ)
    (h : Sp2mKindType (S ⧸ center S) m f κ) : Group.IsSolvable (Outer S) := by
  obtain ⟨τ, r, hτ, hr, hτm⟩ := exists_lieModel_of_isLinearUnitaryKind hκ h
  rcases hτ with rfl | rfl
  · exact F4Pilot.isSolvable_outer_of_lieModel_PSL_quotient hS (by omega) hτm
  · have : Group.IsSolvable (Outer (S ⧸ center S)) := UnitaryPilot.isSolvable_outer_of_lieModel hτm
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient S

theorem odd_card_ker_comp_mk_center {E Kb : Type} [Group E] [Group Kb] (q : E →* Kb)
    (hk : Odd (Nat.card q.ker)) (hZ : Odd (Nat.card (center Kb))) :
    Odd (Nat.card ((QuotientGroup.mk' (center Kb)).comp q).ker) := by
  set φ := (QuotientGroup.mk' (center Kb)).comp q with hφ
  set ψ : φ.ker →* Kb := q.comp φ.ker.subtype with hψ
  have hrange : ψ.range ≤ center Kb := by
    rintro _ ⟨z, rfl⟩
    have hz : QuotientGroup.mk' (center Kb) (q (z : E)) = 1 := z.2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
    exact hz
  have hle : q.ker ≤ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    change QuotientGroup.mk' (center Kb) (q x) = 1
    rw [hx, map_one]
  have hker : ψ.ker = q.ker.subgroupOf φ.ker := by
    ext z
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hcard : Nat.card φ.ker = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Subgroup.index_ker ψ, Subgroup.card_mul_index]
  have h1 : Nat.card ψ.ker = Nat.card q.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h2 : Odd (Nat.card ψ.range) := Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_le hrange)
  rw [hcard, h1]
  exact hk.mul h2

theorem exists_conjAut_dualAut_normalForm {r e : ℕ} (hr : 3 ≤ r)
    {F : Type} [Field F] [Finite F] (he : 1 ≤ e) (hF : Nat.card F = 2 ^ e)
    {α : MulAut (LinearFlag.projectiveSL r F)} (hα2 : α ^ 2 = 1)
    (hαE : α ∉ LinearFlag.semilinearAutGroup r F) {m f : ℕ}
    (hfix : LieModel (fixedSubgroup α) .PSp m 2 f) :
    ∃ H C : GL (Fin r) F, ((C : Matrix (Fin r) (Fin r) F) = 1 ∨
        ∃ r', r = 2 * r' ∧ (C : Matrix (Fin r) (Fin r) F) = blockSwapJ r r') ∧
      α = LinearFlag.conjAut r F H * (LinearFlag.conjAut r F C * LinearFlag.dualAut r F) *
        (LinearFlag.conjAut r F H)⁻¹ := by
  obtain ⟨A, σ, ε, hε, hα⟩ := (LinearFlag.automorphism_generation (K := F) hr).2 α
  interval_cases ε
  · exfalso
    apply hαE
    rw [hα, pow_zero, mul_one]
    exact mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup
      (LinearFlag.conjAut_mem_linearAutGroup A)) (LinearFlag.fieldAut_mem_semilinearAutGroup σ)
  · rw [pow_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα
      obtain ⟨-, ⟨H, C, -, hconj, hC⟩, -⟩ :=
        even_linear_pure_graph_involution_normal_forms he hF hr A (hα ▸ hα2)
      refine ⟨H, C, ?_, hα.trans hconj⟩
      rcases hC with ⟨hC1, -⟩ | ⟨r', hr', hCJ, -⟩
      · exact Or.inl hC1
      · exact Or.inr ⟨r', hr', hCJ⟩
    · exfalso
      have hgf := CFSG.ComponentClassification.CatalogueBLinearHigherB.congr_graphField
        (n := r) (K := F) A σ
      rw [← hα] at hgf
      have hα1 : α ≠ 1 := fun h1 => hαE (h1 ▸ one_mem _)
      have hord : orderOf (CFSG.ComponentClassification.CatalogueBGraphField.graphFieldAction
          r F A σ) = 2 := by
        rw [← hgf]
        refine orderOf_eq_prime ?_ ?_
        · rw [← map_pow, hα2, map_one]
        · intro h1
          apply hα1
          exact (MulAut.congr (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv
            r F)).injective (h1.trans (map_one _).symm)
      have hP := LinearPilot.psl_graphField_pComponents hr he hF A σ hσ hord
      let Ψ : fixedSubgroup α ≃* fixedSubgroup
          (CFSG.ComponentClassification.CatalogueBGraphField.graphFieldAction r F A σ) :=
        (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv
          (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv r F) _).trans
          (MulEquiv.subgroupCongr (congrArg fixedSubgroup hgf))
      have hfix' := LieType.CurtisTits.lieModel_of_mulEquiv Ψ hfix
      obtain ⟨hadm', hm'⟩ := hP ⊤ (isPComponent_top_of_lieModel_PSp hfix')
      exact false_of_lieModel_ne_PSp (sp2mEvenTypeDetClassical m) hfix' (Or.inl (by decide))
        (by decide) hadm' (LieType.CurtisTits.lieModel_of_mulEquiv Subgroup.topEquiv hm')

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_surjective_neighbourCore_linearUnitary {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G}
    (hX : X = modelToG e (rootTorusSp K k)) {D : Subgroup G} (hD : D = modelToG e (complSp K k))
    {κ : Sp2mKind} (hκ : IsLinearUnitaryKind κ) (h : HR8KindAtSp t m f X D κ)
    (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    ∃ (S : Type) (_ : Group S) (ρ : centralizerPerfectCore X →* S) (τ : MulAut S),
      Function.Surjective ρ ∧ ρ.ker ≤ center (centralizerPerfectCore X) ∧
        Odd (Nat.card ρ.ker) ∧ Sp2mKindType S m f κ ∧ center S = ⊥ ∧
        (∀ y, ρ ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) = τ (ρ y)) ∧
        τ * τ = 1 ∧ τ ∉ (MulAut.conj : S →* MulAut S).range ∧
        LieModel (fixedSubgroup τ) .PSp m 2 f := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨htX, Kb, hKb, -, hcase⟩ := h
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => by
    rcases hκ with rfl | rfl | rfl | rfl <;> cases h.1
  have hKbP : Group.IsPerfect Kb := hKb.1.1
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
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_rootTorusSp_of_seitzSetting hset hKc hq hm e htC ht k
    hX htX hD
  have hOut : Group.IsSolvable (Outer Kb) :=
    isSolvable_outer_of_sp2mKindType_linearUnitary hKbP hm hκ hty
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  obtain ⟨-, -, hBall⟩ := bLift_neighbour_rootTorusSp_of_seitzSetting hset hKc hq hm e htC ht k hX
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
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
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
  set τK := Kb.normalizerMonoidHom ⟨_, hsN⟩ with hτK
  have hτK2 : τK * τK = 1 := by
    rw [hτK, ← map_mul]
    convert map_one Kb.normalizerMonoidHom
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← hs2, pow_orderOf_eq_one]; rfl)
  refine ⟨Kb ⧸ center Kb, inferInstance, (QuotientGroup.mk' (center Kb)).comp qh,
    centerQuotientAut τK, (QuotientGroup.mk'_surjective _).comp hqs, fun x hx => ?_,
    odd_card_ker_comp_mk_center qh hkodd hov.2.1, hty,
    CFSG.ComponentClassification.UnbalancedGS.SemidihedralKernel.center_quotient_center_eq_bot,
    fun y => ?_, ?_, fun hin => ?_, hov.2.2.2⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center qh hqker hx
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hθ, centerQuotientAut_mk]
  · rw [← F4Pilot.centerQuotientAut_mul, hτK2, F4Pilot.centerQuotientAut_one]
  · exact hov.1 (F4Pilot.mem_range_conj_of_centerQuotientAut (MonoidHom.id Kb)
      Function.surjective_id (fun g => rfl) hin)

end Lift

end CFSG.SeitzReduction.SymplecticPilot
