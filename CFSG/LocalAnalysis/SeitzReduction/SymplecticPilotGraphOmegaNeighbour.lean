module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
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

section Kinds

theorem oddSchurTrivial_of_sp2mKindType_omega
    {S : Type} [Group S] {m f : ℕ}
    {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : Sp2mKindType S m f κ) :
    OddSchurTrivial S := by
  rcases hκ with rfl | rfl
  · exact SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus h
  · exact SeitzQ2.oddSchurTrivial_of_lieModel_POmegaMinus h

theorem isSolvable_outer_of_sp2mKindType_omega {S : Type} [Group S] {m f : ℕ} {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : Sp2mKindType S m f κ) :
    Group.IsSolvable (Outer S) := by
  rcases hκ with rfl | rfl
  · exact (CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier
      .POmegaPlus (Or.inr (Or.inl rfl))
      (CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel (by decide) h)).2.2
  · exact (CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier
      .POmegaMinus (Or.inr (Or.inr rfl))
      (CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel (by decide) h)).2.2

end Kinds

section Lift


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem neighbourCore_omega_facts {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G}
    (hX : X = modelToG e (rootTorusSp K k)) {D : Subgroup G} (hD : D = modelToG e (complSp K k))
    {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : HR8KindAtSp t m f X D κ)
    (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    Sp2mKindType (centralizerPerfectCore X) m f κ ∧
      (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ ∉
        (MulAut.conj : centralizerPerfectCore X →* MulAut (centralizerPerfectCore X)).range ∧
      LieModel (fixedSubgroup ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩))
        .PSp m 2 f := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
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
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_rootTorusSp_of_seitzSetting hset hKc hq hm e htC ht k
    hX htX hD
  have hOut : Group.IsSolvable (Outer Kb) := by
    have : Group.IsSolvable (Outer (Kb ⧸ center Kb)) :=
      isSolvable_outer_of_sp2mKindType_omega hκ hty
    exact solvable_of_equiv e₁.symm
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

end Lift

section NormalForm

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher


theorem exists_mulEquiv_comm_symmetryAut {E : Type} [Group E] {θ : MulAut E} (hθθ : θ * θ = 1)
    (hout : θ ∉ (MulAut.conj : E →* MulAut E).range) {m f' : ℕ}
    (hfix : LieModel (fixedSubgroup θ) .PSp m 2 f') {K' : Type} [Field K'] [Finite K'] {f n : ℕ}
    (hf : 1 ≤ f) (hK' : Nat.card K' = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K' (Fin (2 * n) → K')} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * n) → K'), Module.finrank K' T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    {v : Fin (2 * n) → K'} (hv : Q v = 1) (ε : E ≃* matrixProjectiveDerived Q) :
    ∃ ψ : matrixProjectiveDerived Q ≃* E, ∀ x, θ (ψ x) = ψ (symmetryAut Q v x) := by
  set α := MulAut.congr ε θ with hαdef
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, hθθ, map_one]
  have hαo : α ∉ inner (matrixProjectiveDerived Q) := by
    rw [hαdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hαfix : LieModel (fixedSubgroup α) .PSp m 2 f' :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  obtain ⟨Ψ, hΨ⟩ :=
    exists_conj_eq_symmetryAut_of_lieModel_PSp hf hK' hn hQ hT hE hconj hv α hαα hαo hαfix
  refine ⟨Ψ.trans ε.symm, fun x => ?_⟩
  apply ε.injective
  have h1 : α (Ψ x) = ε (θ (ε.symm (Ψ x))) := rfl
  have h2 : α (Ψ x) = Ψ (symmetryAut Q v x) := by
    rw [hΨ]
    change Ψ (symmetryAut Q v (Ψ.symm (Ψ x))) = _
    rw [MulEquiv.symm_apply_apply]
  change ε (θ (ε.symm (Ψ x))) = ε (ε.symm (Ψ (symmetryAut Q v x)))
  rw [← h1, h2, MulEquiv.apply_symm_apply]


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_mulEquiv_neighbourCore_plus {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (h : RootKindSp e t f k .omegaPlus) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ f ∧
      ∃ (ψ : matrixProjectiveDerived (coordinateQuadPlus (m + 1) K') ≃* neighbourCore e k)
        (v : Fin (2 * (m + 1)) → K'), coordinateQuadPlus (m + 1) K' v = 1 ∧
        ∀ x, t * ((ψ x : neighbourCore e k) : G) * t⁻¹ =
          ((ψ (symmetryAut (coordinateQuadPlus (m + 1) K') v x) : neighbourCore e k) : G) := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hN : t ∈ normalizer (neighbourCore e k : Set G) := le_normalizer_neighbourCore e htC k
  obtain ⟨hty, hout, hfix⟩ := neighbourCore_omega_facts hset hKc hf hm e htC ht k rfl rfl
    (Or.inl rfl) h hN
  have hty' : LieModel (neighbourCore e k) .POmegaPlus (m + 1) 2 f := hty
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty'
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image (neighbourCore e k)
    .POmegaPlus (Or.inl rfl) (m + 1) f hC).1
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ m + 1 := hn4'
  have hconj := (hI K' hK' eE).1
  have hreg := regular_coordinateQuadPlus (K := K') (n := m + 1) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K') (n := m + 1) (by omega)
  have hhyp := OmegaPilot.isHypCoord_coordinateQuadPlus (K := K') (n := m + 1) ⟨0, by omega⟩
  have hv : coordinateQuadPlus (m + 1) K'
      ((1 : K') • Pi.single (plusIndexEquiv (m + 1) (.inl ⟨0, by omega⟩)) 1 +
        (1 : K') • Pi.single (plusIndexEquiv (m + 1) (.inr ⟨0, by omega⟩)) 1 + 0) = 1 := by
    rw [hhyp.map_add_smul 1 1 rfl rfl, QuadraticMap.map_zero, mul_one, add_zero]
  have hθθ : (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ *
      (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (neighbourCore e k : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hout hfix hf1 hK' hn4 hreg.1 hreg.2 hE
    hconj hv (coordinatePlusWitnessEquiv K' eE)
  refine ⟨K', inferInstance, inferInstance, hK', ψ, _, hv, fun x => ?_⟩
  rw [← hψ x, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem exists_mulEquiv_neighbourCore_minus {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (h : RootKindSp e t f k .omegaMinus) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ f ∧
      ∃ (b c : K') (_ : ∀ s : K', s ^ 2 + b * s + c ≠ 0)
        (ψ : matrixProjectiveDerived (coordinateQuadMinus (m + 1) K' (by omega) b c) ≃*
          neighbourCore e k)
        (v : Fin (2 * (m + 1)) → K'), coordinateQuadMinus (m + 1) K' (by omega) b c v = 1 ∧
        ∀ x, t * ((ψ x : neighbourCore e k) : G) * t⁻¹ =
          ((ψ (symmetryAut (coordinateQuadMinus (m + 1) K' (by omega) b c) v x) :
            neighbourCore e k) : G) := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hN : t ∈ normalizer (neighbourCore e k : Set G) := le_normalizer_neighbourCore e htC k
  obtain ⟨hty, hout, hfix⟩ := neighbourCore_omega_facts hset hKc hf hm e htC ht k rfl rfl
    (Or.inr rfl) h hN
  have hty' : LieModel (neighbourCore e k) .POmegaMinus (m + 1) 2 f := hty
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty'
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image (neighbourCore e k)
    .POmegaMinus (Or.inr rfl) (m + 1) f hC).1
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', b, c, hirr, ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ m + 1 := hn4'
  have hconj := hI (by omega) K' hK' b c hirr eE
  have hreg := regular_coordinateQuadMinus (m + 1) K' b c hn4 hirr
  have hE := commutator_coordinateQuadMinus (m + 1) K' b c hn4 hirr
  have hhyp := OmegaPilot.isHypCoord_coordinateQuadMinus (K := K') (n := m + 1) (by omega) b c
    ⟨0, by omega⟩
  have hv : coordinateQuadMinus (m + 1) K' (by omega) b c
      ((1 : K') • Pi.single (minusIndexEquiv (m + 1) (by omega) (.inl ⟨0, by omega⟩)) 1 +
        (1 : K') • Pi.single (minusIndexEquiv (m + 1) (by omega) (.inr (.inl ⟨0, by omega⟩))) 1 +
          0) = 1 := by
    rw [hhyp.map_add_smul 1 1 rfl rfl, QuadraticMap.map_zero, mul_one, add_zero]
  have hθθ : (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ *
      (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (neighbourCore e k : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hout hfix hf1 hK' hn4 hreg.1 hreg.2 hE
    hconj hv (coordinateMinusWitnessEquiv K' (by omega) b c eE)
  refine ⟨K', inferInstance, inferInstance, hK', b, c, hirr, ψ, _, hv, fun x => ?_⟩
  rw [← hψ x, Subgroup.normalizerMonoidHom_apply_apply_coe]

end NormalForm

end CFSG.SeitzReduction.SymplecticPilot
