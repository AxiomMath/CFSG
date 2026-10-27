module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Neighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RootSL2
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

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

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_surjective_neighbourCore_linearUnitary_two {m : ℕ} (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G}
    (hX : X = modelToG e (nsTorusSp K k)) {D : Subgroup G} (hD : D = modelToG e (complSp K k))
    {κ : Sp2mKind} (hκ : IsLinearUnitaryKind κ) (h : HR8KindAtSp t m 1 X D κ)
    (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    ∃ (S : Type) (_ : Group S) (ρ : centralizerPerfectCore X →* S) (τ : MulAut S),
      Function.Surjective ρ ∧ ρ.ker ≤ center (centralizerPerfectCore X) ∧
        Odd (Nat.card ρ.ker) ∧ Sp2mKindType S m 1 κ ∧ center S = ⊥ ∧
        (∀ y, ρ ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) = τ (ρ y)) ∧
        τ * τ = 1 ∧ τ ∉ (MulAut.conj : S →* MulAut S).range ∧
        LieModel (fixedSubgroup τ) .PSp m 2 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK, pow_one])
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
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nsTorusSp_of_seitzSetting hset hK hm e htC ht k
    hX htX hD
  have hOut : Group.IsSolvable (Outer Kb) :=
    isSolvable_outer_of_sp2mKindType_linearUnitary hKbP (by omega) hκ hty
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

theorem exists_mulEquiv_neighbourCore_linear_two {m : ℕ} (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G}
    (hX : X = modelToG e (nsTorusSp K k)) {D : Subgroup G} (hD : D = modelToG e (complSp K k))
    {κ : Sp2mKind} (hκ : κ = .linearEven ∨ κ = .linearOdd) (h : HR8KindAtSp t m 1 X D κ)
    (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    ∃ (r : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ((κ = .linearEven ∧ r = 2 * m) ∨ (κ = .linearOdd ∧ r = 2 * m + 1)) ∧
      ∃ ε : centralizerPerfectCore X ≃* LinearFlag.projectiveSL r F,
        MulAut.congr ε ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩) *
            MulAut.congr ε ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩) = 1 ∧
          MulAut.congr ε ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩) ∉
            (MulAut.conj : LinearFlag.projectiveSL r F →* MulAut _).range ∧
          LieModel (fixedSubgroup (MulAut.congr ε
            ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩))) .PSp m 2 1 := by
  have hκ' : IsLinearUnitaryKind κ := by
    rcases hκ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨S, _, ρ, τ, hρ, hker, -, hty, -, hρθ, hττ, hout, hfix⟩ :=
    exists_surjective_neighbourCore_linearUnitary_two hset hK hm e htC ht k hX hD hκ' h hN
  obtain ⟨r, hS, hr⟩ : ∃ r, LieModel S .PSL r 2 1 ∧
      ((κ = .linearEven ∧ r = 2 * m) ∨ (κ = .linearOdd ∧ r = 2 * m + 1)) := by
    rcases hκ with rfl | rfl
    · exact ⟨_, hty, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, hty, Or.inr ⟨rfl, rfl⟩⟩
  have hr5 : 5 ≤ r := by rcases hr with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨F', _, _, hF', Φ, hΦ, hΦk⟩ :=
    F4Pilot.exists_sl_cover_of_surjective hEperf (by omega) hS ρ hρ hker
  have hF'2 : Nat.card F' = 2 := by rw [hF', pow_one]
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    exact LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hF'2 (hΦk hz)
  have hZ : center (centralizerPerfectCore X) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨w, hw⟩ : (z : G) ∈ Φ.range := by rw [hΦ]; exact z.2
    have hwc : w ∈ center (Matrix.SpecialLinearGroup (Fin (r' + 1)) F') := by
      rw [mem_center_iff]
      intro v
      apply hΦinj
      have hv : Φ v ∈ centralizerPerfectCore X := by rw [← hΦ]; exact ⟨v, rfl⟩
      have := congrArg Subtype.val (mem_center_iff.1 hz ⟨Φ v, hv⟩)
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_mul, hw]
      exact this
    have h1 := LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hF'2 hwc
    rw [h1, map_one] at hw
    exact mem_bot.2 (Subtype.ext hw.symm)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hadm : StatedLieAdmissible .PSL (r' + 1) 2 1 := F4Pilot.statedLieAdmissible_of_lieModel hS
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hS
  set εS : S ≃* LinearFlag.projectiveSL (r' + 1) F :=
    eJ.trans (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv (r' + 1) F).symm
    with hεS
  set ρe : centralizerPerfectCore X ≃* S := MulEquiv.ofBijective ρ ⟨hρinj, hρ⟩ with hρe
  have hcongr : MulAut.congr ρe ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩) = τ := by
    ext z
    obtain ⟨y, rfl⟩ := hρ z
    change ρ ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ (ρe.symm (ρ y))) = τ (ρ y)
    have : ρe.symm (ρ y) = y := ρe.symm_apply_apply y
    rw [this, hρθ]
  refine ⟨r' + 1, F, inferInstance, inferInstance, by rw [hF, pow_one], hr, ρe.trans εS, ?_, ?_, ?_⟩
  · have h1 : MulAut.congr (ρe.trans εS) ((centralizerPerfectCore X).normalizerMonoidHom
        ⟨t, hN⟩) = MulAut.congr εS τ := by
      rw [← hcongr]
      ext z
      rfl
    rw [h1, ← map_mul, hττ, map_one]
  · intro hin
    have h1 : MulAut.congr (ρe.trans εS) ((centralizerPerfectCore X).normalizerMonoidHom
        ⟨t, hN⟩) = MulAut.congr εS τ := by
      rw [← hcongr]
      ext z
      rfl
    rw [h1] at hin
    exact hout ((FixedFourGroup.congr_mem_inner_iff εS τ).1 hin)
  · have h1 : MulAut.congr (ρe.trans εS) ((centralizerPerfectCore X).normalizerMonoidHom
        ⟨t, hN⟩) = MulAut.congr εS τ := by
      rw [← hcongr]
      ext z
      rfl
    rw [h1]
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv εS τ) hfix

end Lift

end CFSG.SeitzReduction.SymplecticPilot
