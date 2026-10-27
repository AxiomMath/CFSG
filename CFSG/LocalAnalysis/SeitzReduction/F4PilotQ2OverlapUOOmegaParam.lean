module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOOmega
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_graphLift_aut_odd_nonsplit_F4_two {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {κ : Sp6Kind} (hκ : κ.IsGraphKind) (hk : TwoKindAt e t X₀ κ)
    (hN : t ∈ normalizer (centralizerPerfectCore (subgroupToG e X₀) : Set G)) :
    ∃ (S : Type) (_ : Group S) (ρ : centralizerPerfectCore (subgroupToG e X₀) →* S)
      (τ : MulAut S), Function.Surjective ρ ∧
        ρ.ker ≤ center (centralizerPerfectCore (subgroupToG e X₀)) ∧ Sp6KindType S 1 κ ∧
        (∀ y, ρ ((centralizerPerfectCore (subgroupToG e X₀)).normalizerMonoidHom ⟨t, hN⟩ y) =
          τ (ρ y)) ∧
        τ * τ = 1 ∧ τ ∉ (MulAut.conj : S →* MulAut S).range ∧
        LieModel (fixedSubgroup τ) .PSp 3 2 1 ∧ Odd (Nat.card ρ.ker) := by
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
  have hθ : ∀ y : centralizerPerfectCore X,
      qh ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) =
        Kb.normalizerMonoidHom ⟨_, hsN⟩ (qh y) := by
    intro y
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp]
    have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y :
        centralizerPerfectCore X) : G), hle ((centralizerPerfectCore X).normalizerMonoidHom
          ⟨t, hN⟩ y).2⟩ : H) = t' * ⟨(y : G), hle y.2⟩ * t'⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [e1, map_mul, map_mul, map_inv]
  set τK := Kb.normalizerMonoidHom ⟨_, hsN⟩ with hτK
  have hτK2 : τK * τK = 1 := by
    rw [hτK, ← map_mul]
    convert map_one Kb.normalizerMonoidHom
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← hs2, pow_orderOf_eq_one]; rfl)
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore X)
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
  have hmemZ : ∀ y : centralizerPerfectCore X,
      y ∈ ((QuotientGroup.mk' (center Kb)).comp qh).ker → qh y ∈ center Kb := by
    intro y hy
    have hy2 : QuotientGroup.mk' (center Kb) (qh y) = 1 := hy
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy2
  have hodd : Odd (Nat.card ((QuotientGroup.mk' (center Kb)).comp qh).ker) := by
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
      have hoddZ := hov.2.1
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd h2 (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hoddZ))
    have hxk : (x : centralizerPerfectCore X) ∈ qh.ker := orderOf_eq_one_iff.1 h3
    have h4 := Subgroup.orderOf_dvd_natCard _ hxk
    rw [hx'] at h4
    exact absurd h4 (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hkodd))
  refine ⟨Kb ⧸ center Kb, inferInstance, (QuotientGroup.mk' (center Kb)).comp qh,
    centerQuotientAut τK, (QuotientGroup.mk'_surjective _).comp hqs, fun x hx => ?_, hty,
    fun y => ?_, ?_, fun hin => ?_, hov.2.2.2, hodd⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center qh hqker hx
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hθ, centerQuotientAut_mk]
  · rw [← centerQuotientAut_mul, hτK2, centerQuotientAut_one]
  · exact hov.1 (mem_range_conj_of_centerQuotientAut (MonoidHom.id Kb)
      Function.surjective_id (fun g => rfl) hin)


section Param

open CFSG.SeitzReduction.SymplecticPilot (q2OmIota q2OmIota_injective range_q2OmIota kOmegaBetaC
  kOmega_matrixDerivedScalars_eq_bot kOmega_hconj kOmega_reindexQuadraticForm_vec
  exists_mulEquiv_comm_symmetryAut q2RingEquiv_eq_one q2OmMIota q2OmMIota_injective
  range_q2OmMIota kOmMBetaC kOmM_nonempty_mulEquiv_of_lieModel kOmM_matrixDerivedScalars_eq_bot
  kOmM_hconj kOmM_reindexQuadraticForm_vec)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (plusIndexEquiv
  regular_coordinateQuadPlus commutator_coordinateQuadPlus minusIndexEquiv
  regular_coordinateQuadMinus commutator_coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus)

theorem exists_twoOmegaPlusParam [Finite K] [CharP K 2] (hK : Nat.card K = 2) {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .omegaPlus8) :
    ∃ Φ : CFSG.Assembly.LowTwoRank.StatedOmega
      (CFSG.Assembly.LowTwoRank.StatedQuadPlus (3 + 1) K) ≃*
        centralizerPerfectCore (subgroupToG e X₀),
      IsTwoGraphParam e X₀ (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl) Φ := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK]
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hXL : subgroupToG e X₀ ≤ L := map_subtype_le _
  set E := centralizerPerfectCore (subgroupToG e X₀) with hEdef
  have hN : t ∈ normalizer (E : Set G) :=
    normalizer_le_normalizer_centralizerPerfectCore _
      (centralizer_le_normalizer _ (centralizer_le hXL hw.mem_centralizer))
  obtain ⟨S, _, ρ, τ, hρ, hker, hty, hρθ, hττ, hout, hfix, hodd⟩ :=
    exists_graphLift_aut_odd_nonsplit_F4_two hw e hXJ hcyc hX₀ (by decide) hk hN
  have hEperf : Group.IsPerfect E := isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  have hρinj : Function.Injective ρ :=
    SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hty E hEperf ρ hρ hker hodd
  set ρe : E ≃* S := MulEquiv.ofBijective ρ ⟨hρinj, hρ⟩ with hρe
  set θ := E.normalizerMonoidHom ⟨t, hN⟩ with hθ
  have hcongr : MulAut.congr ρe θ = τ := by
    ext z
    obtain ⟨y, rfl⟩ := hρ z
    change ρ (θ (ρe.symm (ρ y))) = τ (ρ y)
    have : ρe.symm (ρ y) = y := ρe.symm_apply_apply y
    rw [this, hρθ]
  have hθθ : θ * θ = 1 := (MulAut.congr ρe).injective (by rw [map_mul, hcongr, hττ, map_one])
  have hθo : θ ∉ (MulAut.conj : E →* MulAut E).range := fun h =>
    hout (by rw [← hcongr]; exact (FixedFourGroup.congr_mem_inner_iff ρe θ).2 h)
  have hθfix : LieModel (fixedSubgroup θ) .PSp 3 2 1 := by
    rw [← hcongr] at hfix
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv ρe θ).symm hfix
  have hty' : LieModel E .POmegaPlus (3 + 1) 2 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv ρe.symm hty
  obtain ⟨ε₀⟩ := OmegaPilot.nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hty' K hKc
  set π := F4Pilot.omegaProjEquiv (plusIndexEquiv (3 + 1)) (quadPlus (3 + 1) K)
    (coe_quadPlus (3 + 1) K) (kOmega_matrixDerivedScalars_eq_bot K 3) with hπ
  have hreg := regular_coordinateQuadPlus (K := K) (n := 3 + 1) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K) (n := 3 + 1) (by omega)
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hθo hθfix (le_refl 1) hKc
    (by omega : 4 ≤ 3 + 1) hreg.1 hreg.2 hE (kOmega_hconj K (by omega) le_rfl hKc)
    (kOmega_reindexQuadraticForm_vec K 3) (ε₀.trans π)
  set Φ₀ : CFSG.Assembly.LowTwoRank.StatedOmega
      (CFSG.Assembly.LowTwoRank.StatedQuadPlus (3 + 1) K) ≃* E := π.trans ψ with hΦ₀
  have hΦ₀t : ∀ g, t * ((Φ₀ g : E) : G) * t⁻¹ = ((Φ₀ (kOmegaBetaC K 3 g) : E) : G) := by
    intro g
    have h12 : θ (ψ (π g)) = ψ (π (kOmegaBetaC K 3 g)) :=
      (hψ (π g)).trans (congrArg ψ (F4Pilot.omegaProjEquiv_omegaSymmetryAut _ _ _ _ _ g).symm)
    change t * ((ψ (π g) : E) : G) * t⁻¹ = ((ψ (π (kOmegaBetaC K 3 g)) : E) : G)
    rw [← h12, hθ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hfixE : (fixedSubgroup (kOmegaBetaC K 3)).map (E.subtype.comp Φ₀.toMonoidHom) =
      E ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨(Φ₀ g).2, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := hΦ₀t g
      have hg' : kOmegaBetaC K 3 g = g := hg
      rw [hg'] at h1
      change ((Φ₀ g : E) : G) * t = t * ((Φ₀ g : E) : G)
      calc ((Φ₀ g : E) : G) * t = (t * ((Φ₀ g : E) : G) * t⁻¹) * t := by rw [h1]
        _ = t * ((Φ₀ g : E) : G) := by group
    · rintro ⟨hxE, hxt⟩
      refine ⟨Φ₀.symm ⟨x, hxE⟩, ?_, by simp⟩
      change kOmegaBetaC K 3 (Φ₀.symm ⟨x, hxE⟩) = Φ₀.symm ⟨x, hxE⟩
      apply Φ₀.injective
      apply Subtype.ext
      rw [← hΦ₀t, MulEquiv.apply_symm_apply]
      have hxt' : x * t = t * x := mem_centralizer_singleton_iff.1 hxt
      change t * x * t⁻¹ = x
      rw [← hxt']
      group
  have hperf : ⁅fixedSubgroup (kOmegaBetaC K 3), fixedSubgroup (kOmegaBetaC K 3)⁆ =
      fixedSubgroup (kOmegaBetaC K 3) := by
    rw [← range_q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl, MonoidHom.range_eq_map,
      ← map_commutator, commutator_top_statedSp_three]
  have hfixmap : (fixedSubgroup (kOmegaBetaC K 3)).map (E.subtype.comp Φ₀.toMonoidHom) =
      subgroupToG e (C3Levi K) := by
    have hp : ⁅E ⊓ centralizer ({t} : Set G), E ⊓ centralizer ({t} : Set G)⁆ =
        E ⊓ centralizer ({t} : Set G) := by
      rw [← hfixE, ← map_commutator, hperf]
    rw [hfixE, ← CFSG.Quasithin.perfectCore_eq_self_of_perfect hp]
    exact perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀'
  set ι := q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl with hιdef
  set κ : CFSG.Assembly.LowTwoRank.StatedSp 3 K →* G := E.subtype.comp (Φ₀.toMonoidHom.comp ι)
    with hκdef
  have hκinj : Function.Injective κ :=
    E.subtype_injective.comp (Φ₀.injective.comp (q2OmIota_injective _ hK le_rfl))
  have hκr : κ.range = subgroupToG e (C3Levi K) := by
    rw [hκdef, ← MonoidHom.comp_assoc, MonoidHom.range_comp, hιdef, range_q2OmIota, hfixmap]
  set lam : CFSG.Assembly.LowTwoRank.StatedSp 3 K →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp (c3LeviHom K))
    with hlamdef
  have hlaminj : Function.Injective lam :=
    L.subtype_injective.comp (e.symm.injective.comp c3LeviHom_injective)
  have hlamr : lam.range = subgroupToG e (C3Levi K) := by
    rw [hlamdef, MonoidHom.range_comp, MonoidHom.range_comp, range_c3LeviHom]
    rfl
  set δ : MulAut (CFSG.Assembly.LowTwoRank.StatedSp 3 K) := ((MonoidHom.ofInjective hlaminj).trans
    (MulEquiv.subgroupCongr (hlamr.trans hκr.symm))).trans (MonoidHom.ofInjective hκinj).symm
    with hδdef
  have hκδ : ∀ g, κ (δ g) = lam g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκinj).apply_symm_apply
      (MulEquiv.subgroupCongr (hlamr.trans hκr.symm) (MonoidHom.ofInjective hlaminj g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, σ₀, hsσ⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_eq_conj_mul_fieldSp
    (r := 3) le_rfl δ
  rw [q2RingEquiv_eq_one hK σ₀, map_one, mul_one] at hsσ
  refine ⟨(MulAut.conj (ι s)).trans Φ₀, fun x => ?_⟩
  have h1 := hκδ x
  rw [hsσ, MulAut.conj_apply] at h1
  change ((Φ₀ (ι s * ι x * (ι s)⁻¹) : E) : G) = _
  rw [← map_inv, ← map_mul, ← map_mul]
  exact h1

theorem twoOmegaPlusParamInput_holds : TwoOmegaPlusParamInput := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  exact exists_twoOmegaPlusParam hK hw e hXJ hcyc hX₀ hk

theorem exists_twoOmegaMinusParam [Finite K] [CharP K 2] (hK : Nat.card K = 2) {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .omegaMinus8) :
    ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (Φ : CFSG.Assembly.LowTwoRank.StatedOmega
        (CFSG.Assembly.LowTwoRank.StatedQuadMinus (3 + 1) K b c) ≃*
          centralizerPerfectCore (subgroupToG e X₀)),
      IsTwoGraphParam e X₀ (q2OmMIota (k := K) (r := 3) le_rfl hirr hK) Φ := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK]
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hXL : subgroupToG e X₀ ≤ L := map_subtype_le _
  set E := centralizerPerfectCore (subgroupToG e X₀) with hEdef
  have hN : t ∈ normalizer (E : Set G) :=
    normalizer_le_normalizer_centralizerPerfectCore _
      (centralizer_le_normalizer _ (centralizer_le hXL hw.mem_centralizer))
  obtain ⟨S, _, ρ, τ, hρ, hker, hty, hρθ, hττ, hout, hfix, hodd⟩ :=
    exists_graphLift_aut_odd_nonsplit_F4_two hw e hXJ hcyc hX₀ (by decide) hk hN
  have hEperf : Group.IsPerfect E := isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  have hρinj : Function.Injective ρ :=
    SeitzQ2.oddSchurTrivial_of_lieModel_POmegaMinus hty E hEperf ρ hρ hker hodd
  set ρe : E ≃* S := MulEquiv.ofBijective ρ ⟨hρinj, hρ⟩ with hρe
  set θ := E.normalizerMonoidHom ⟨t, hN⟩ with hθ
  have hcongr : MulAut.congr ρe θ = τ := by
    ext z
    obtain ⟨y, rfl⟩ := hρ z
    change ρ (θ (ρe.symm (ρ y))) = τ (ρ y)
    have : ρe.symm (ρ y) = y := ρe.symm_apply_apply y
    rw [this, hρθ]
  have hθθ : θ * θ = 1 := (MulAut.congr ρe).injective (by rw [map_mul, hcongr, hττ, map_one])
  have hθo : θ ∉ (MulAut.conj : E →* MulAut E).range := fun h =>
    hout (by rw [← hcongr]; exact (FixedFourGroup.congr_mem_inner_iff ρe θ).2 h)
  have hθfix : LieModel (fixedSubgroup θ) .PSp 3 2 1 := by
    rw [← hcongr] at hfix
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv ρe θ).symm hfix
  have hty' : LieModel E .POmegaMinus (3 + 1) 2 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv ρe.symm hty
  obtain ⟨b, c, hirr, ⟨ε₀⟩⟩ := kOmM_nonempty_mulEquiv_of_lieModel (by omega) hty' K hKc
  set π := F4Pilot.omegaProjEquiv (minusIndexEquiv (3 + 1) (by omega)) (quadMinus (3 + 1) K b c)
    (coe_quadMinus (3 + 1) K b c) (kOmM_matrixDerivedScalars_eq_bot K 3 b c) with hπ
  have hreg := regular_coordinateQuadMinus (3 + 1) K b c (by omega) hirr
  have hE := commutator_coordinateQuadMinus (3 + 1) K b c (by omega) hirr
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hθo hθfix (le_refl 1) hKc
    (by omega : 4 ≤ 3 + 1) hreg.1 hreg.2 hE (kOmM_hconj K (by omega) le_rfl hKc hirr)
    (kOmM_reindexQuadraticForm_vec K 3) (ε₀.trans π)
  set Φ₀ : CFSG.Assembly.LowTwoRank.StatedOmega
      (CFSG.Assembly.LowTwoRank.StatedQuadMinus (3 + 1) K b c) ≃* E := π.trans ψ with hΦ₀
  have hΦ₀t : ∀ g, t * ((Φ₀ g : E) : G) * t⁻¹ = ((Φ₀ (kOmMBetaC K 3 b c g) : E) : G) := by
    intro g
    have h12 : θ (ψ (π g)) = ψ (π (kOmMBetaC K 3 b c g)) :=
      (hψ (π g)).trans (congrArg ψ (F4Pilot.omegaProjEquiv_omegaSymmetryAut _ _ _ _ _ g).symm)
    change t * ((ψ (π g) : E) : G) * t⁻¹ = ((ψ (π (kOmMBetaC K 3 b c g)) : E) : G)
    rw [← h12, hθ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hfixE : (fixedSubgroup (kOmMBetaC K 3 b c)).map (E.subtype.comp Φ₀.toMonoidHom) =
      E ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨(Φ₀ g).2, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := hΦ₀t g
      have hg' : kOmMBetaC K 3 b c g = g := hg
      rw [hg'] at h1
      change ((Φ₀ g : E) : G) * t = t * ((Φ₀ g : E) : G)
      calc ((Φ₀ g : E) : G) * t = (t * ((Φ₀ g : E) : G) * t⁻¹) * t := by rw [h1]
        _ = t * ((Φ₀ g : E) : G) := by group
    · rintro ⟨hxE, hxt⟩
      refine ⟨Φ₀.symm ⟨x, hxE⟩, ?_, by simp⟩
      change kOmMBetaC K 3 b c (Φ₀.symm ⟨x, hxE⟩) = Φ₀.symm ⟨x, hxE⟩
      apply Φ₀.injective
      apply Subtype.ext
      rw [← hΦ₀t, MulEquiv.apply_symm_apply]
      have hxt' : x * t = t * x := mem_centralizer_singleton_iff.1 hxt
      change t * x * t⁻¹ = x
      rw [← hxt']
      group
  have hperf : ⁅fixedSubgroup (kOmMBetaC K 3 b c), fixedSubgroup (kOmMBetaC K 3 b c)⁆ =
      fixedSubgroup (kOmMBetaC K 3 b c) := by
    rw [← range_q2OmMIota (k := K) (r := 3) le_rfl hirr hK, MonoidHom.range_eq_map,
      ← map_commutator, commutator_top_statedSp_three]
  have hfixmap : (fixedSubgroup (kOmMBetaC K 3 b c)).map (E.subtype.comp Φ₀.toMonoidHom) =
      subgroupToG e (C3Levi K) := by
    have hp : ⁅E ⊓ centralizer ({t} : Set G), E ⊓ centralizer ({t} : Set G)⁆ =
        E ⊓ centralizer ({t} : Set G) := by
      rw [← hfixE, ← map_commutator, hperf]
    rw [hfixE, ← CFSG.Quasithin.perfectCore_eq_self_of_perfect hp]
    exact perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀'
  set ι := q2OmMIota (k := K) (r := 3) le_rfl hirr hK with hιdef
  set κ : CFSG.Assembly.LowTwoRank.StatedSp 3 K →* G := E.subtype.comp (Φ₀.toMonoidHom.comp ι)
    with hκdef
  have hκinj : Function.Injective κ :=
    E.subtype_injective.comp (Φ₀.injective.comp (q2OmMIota_injective le_rfl hirr hK))
  have hκr : κ.range = subgroupToG e (C3Levi K) := by
    rw [hκdef, ← MonoidHom.comp_assoc, MonoidHom.range_comp, hιdef, range_q2OmMIota, hfixmap]
  set lam : CFSG.Assembly.LowTwoRank.StatedSp 3 K →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp (c3LeviHom K))
    with hlamdef
  have hlaminj : Function.Injective lam :=
    L.subtype_injective.comp (e.symm.injective.comp c3LeviHom_injective)
  have hlamr : lam.range = subgroupToG e (C3Levi K) := by
    rw [hlamdef, MonoidHom.range_comp, MonoidHom.range_comp, range_c3LeviHom]
    rfl
  set δ : MulAut (CFSG.Assembly.LowTwoRank.StatedSp 3 K) := ((MonoidHom.ofInjective hlaminj).trans
    (MulEquiv.subgroupCongr (hlamr.trans hκr.symm))).trans (MonoidHom.ofInjective hκinj).symm
    with hδdef
  have hκδ : ∀ g, κ (δ g) = lam g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκinj).apply_symm_apply
      (MulEquiv.subgroupCongr (hlamr.trans hκr.symm) (MonoidHom.ofInjective hlaminj g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, σ₀, hsσ⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_eq_conj_mul_fieldSp
    (r := 3) le_rfl δ
  rw [q2RingEquiv_eq_one hK σ₀, map_one, mul_one] at hsσ
  refine ⟨b, c, hirr, (MulAut.conj (ι s)).trans Φ₀, fun x => ?_⟩
  have h1 := hκδ x
  rw [hsσ, MulAut.conj_apply] at h1
  change ((Φ₀ (ι s * ι x * (ι s)⁻¹) : E) : G) = _
  rw [← map_inv, ← map_mul, ← map_mul]
  exact h1

theorem twoOmegaMinusParamInput_holds : TwoOmegaMinusParamInput := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  exact exists_twoOmegaMinusParam hK hw e hXJ hcyc hX₀ hk

end Param

end CFSG.SeitzReduction.F4Pilot
