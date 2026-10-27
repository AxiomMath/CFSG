module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Unique
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Graph
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveNodes
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRoot
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_injective fieldAutT
  subfieldDerivedImage)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam planeTorusParam)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus
  coordinateQuadMinus_fieldMap_of_fixed autExtensionComm_incl_minus)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.Quasithin (perfectCore)

section Generation

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem range_le_of_comp_incl_minus_of_three_le {r f : ℕ} (hr : 3 ≤ r) (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))
    (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hC : ∀ k, MinusFieldCover e ι k) {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, minusNode (hC 0) j)
    {Φ : matrixProjectiveDerived (coordinateQuadMinus (r + 2) F (by omega)
      ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F)) →* G}
    (hΦ : ∀ x, Φ (incl ι.fieldRange (isExtension_coordinateQuadMinus ι.fieldRange (by omega)
      (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c))
        (minusCongr ι.rangeRestrictFieldEquiv (n := r + 2) (by omega) b c x)) =
      ((e.symm x : L) : G)) :
    Φ.range ≤ G₀ := by
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf1 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hφb : ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) = ι b :=
    RingHom.rangeRestrictFieldEquiv_apply_coe ι b
  have hφc : ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) = ι c :=
    RingHom.rangeRestrictFieldEquiv_apply_coe ι c
  have hβσ : σ ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) =
      ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) := by
    rw [hφb]
    exact (hfix _).2 ⟨b, rfl⟩
  have hγσ : σ ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) =
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) := by
    rw [hφc]
    exact (hfix _).2 ⟨c, rfl⟩
  have hirrF : ∀ s : F, σ s = s → s ^ 2 + ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) * s +
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) ≠ 0 := by
    intro s hs h0
    rw [hφb, hφc] at h0
    obtain ⟨s', rfl⟩ := (hfix s).1 hs
    apply hirr s'
    apply ι.injective
    rw [map_zero, ← h0, map_add, map_add, map_mul, map_pow]
  obtain ⟨α, hα, -, hβ0⟩ := exists_root_frob_of_irreducible hσ hβσ hγσ hirrF
  have hαα := root_ne_other_of_ne_zero (α := α) hβ0
  set B := minusPlusProjEquiv (r := r + 1) (by omega) hα hαα with hB
  have hfr : ∀ t : Fin (r + 1) → Kˣ,
      Φ (B.symm ((isHypFrame_plus F (r + 2)).frameHom (snocOneParam F (r + 1) (liftParam ι t)))) =
        ((e.symm ((isHypFrame_minus K (n := r + 2) (by omega) b c).frameHom t) : L) : G) := by
    intro t
    rw [← hΦ, minusCongr_frameHom, incl_frameHom_minus]
    congr 1
    rw [MulEquiv.symm_apply_eq, hB, minusPlusProjEquiv_frameHom]
    have hw : liftParam ι.fieldRange.subtype
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom t) = liftParam ι t := by
      funext l
      apply Units.ext
      simp [liftParam]
    rw [hw]
  have hrange : Φ.range = (Φ.comp B.symm.toMonoidHom).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (show Function.Surjective
      B.symm.toMonoidHom from B.symm.surjective), ← MonoidHom.range_eq_map]
  obtain ⟨-, -, -, -, -, hD, -⟩ := exists_weakCT_minus_of_covers_of_three_le hr hKc hq hF hC hG₀
    (one_mem (centralizer (L : Set G)))
  rw [hrange, MonoidHom.range_eq_map, ← iSup_rationalNode (K := F) (n := r + 2) (by omega) hF hF4,
    Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  have hperf : ⁅(rationalNode (K := F) (by omega : 1 ≤ r + 2) j).map (Φ.comp B.symm.toMonoidHom),
      (rationalNode (K := F) (by omega : 1 ≤ r + 2) j).map (Φ.comp B.symm.toMonoidHom)⁆ =
      (rationalNode (K := F) (by omega : 1 ≤ r + 2) j).map (Φ.comp B.symm.toMonoidHom) := by
    rw [← Subgroup.map_commutator, commutator_rationalNode (by omega) hF4 j]
  have hcomm : ∀ (P : Subgroup (Fin (r + 1) → Kˣ)),
      (∀ s ∈ P, snocOneParam F (r + 1) (liftParam ι s) ∈
        signedLevelParam (plusNodeSet (r + 2) j) (plusNodeFlip (r + 2) j)) →
      (rationalNode (K := F) (by omega : 1 ≤ r + 2) j).map (Φ.comp B.symm.toMonoidHom) ≤
        centralizer (modelToG e (minusFrameTorus (K := K) (n := r + 2) (by omega) b c P) :
          Set G) := by
    intro P hP
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hz
    rw [minusFrameTorus, (isHypFrame_minus K _ b c).frameTorusOf_eq_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [← hfr s]
    have hmem : (isHypFrame_plus F (r + 2)).frameHom (snocOneParam F (r + 1) (liftParam ι s)) ∈
        plusSignedLevelTorus F (plusNodeSet (r + 2) j) (plusNodeFlip (r + 2) j) :=
      (isHypFrame_plus F (r + 2)).frameHom_mem_frameTorusOf (hP s hs)
    have hc := mem_centralizer_iff.1 (rationalNode_le_centralizer _ j ha) _ hmem
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hc]
  by_cases hj : j.val + 1 ≤ r
  ·
    have hle : (rationalNode (K := F) (by omega : 1 ≤ r + 2) j).map
        (Φ.comp B.symm.toMonoidHom) ≤ minusLevelCore e (consecutiveBlock (r + 1) j.val 2) :=
      F4Pilot.le_centralizerPerfectCore hperf (hcomm _ fun s hs =>
        snocOneParam_liftParam_mem_signedLevelParam_of_le ι hj hs)
    calc _ ≤ minusNode (hC 0) j := by rw [minusNode_of_le _ hj]; exact hle
      _ ≤ G₀ := hG₀ ▸ le_iSup (minusNode (hC 0)) j
  ·
    have hle : (rationalNode (K := F) (by omega : 1 ≤ r + 2) j).map
        (Φ.comp B.symm.toMonoidHom) ≤ minusPieceCore e {Fin.last r} :=
      F4Pilot.le_centralizerPerfectCore hperf (hcomm _ fun s hs =>
        snocOneParam_liftParam_mem_signedLevelParam_of_fork ι hj hs)
    exact hle.trans hD

end Generation

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem conjugate_eq_of_omegaMinusFieldRow_of_three_le {r f : ℕ}
    (hI : OmegaMinusInvolutionCentralizerInput (r + 2))
    (hset : SeitzSetting G L) (hr : 3 ≤ r) (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hC : ∀ k, MinusFieldCover e ι k) {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, minusNode (hC 0) j)
    (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) F (by omega)
      ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F)))
    (h : G) (htM : t ∈ normalizer (CFSG.conjugate G₀ h : Set G)) : CFSG.conjugate G₀ h = G₀ := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hf1 : 1 ≤ f := LinearPilot.one_le_of_card_eq_two_pow hKc
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_mulEquiv_minus (by omega) hf1 hKc hirr e
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  have hirr₀ : ∀ s : ι.fieldRange, s ^ 2 + ι.rangeRestrictFieldEquiv b * s +
      ι.rangeRestrictFieldEquiv c ≠ 0 := by
    intro s hs
    apply hirr (ι.rangeRestrictFieldEquiv.symm s)
    apply ι.rangeRestrictFieldEquiv.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  have hirrF : ∀ s : F, σ s = s → s ^ 2 + ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) * s +
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) ≠ 0 := by
    intro s hs h0
    apply hirr₀ ⟨s, (hσk s).2 hs⟩
    apply Subtype.ext
    simpa using h0
  set Ψ := (MulAut.conj h⁻¹).toMonoidHom.comp (G₀.subtype.comp ψ₀.symm.toMonoidHom) with hΨ
  have hinj : Function.Injective Ψ :=
    (MulAut.conj h⁻¹).injective.comp (G₀.subtype_injective.comp ψ₀.symm.injective)
  have hrange : Ψ.range = CFSG.conjugate G₀ h := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      ψ₀.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  obtain ⟨β, hβ⟩ := SymplecticPilot.exists_mulAut_of_mem_normalizer_range hinj (hrange ▸ htM)
  have hββ := SymplecticPilot.mul_self_eq_one_of_conj_eq hinj htt hβ
  by_cases hc : ∃ ψ' : MulAut (matrixProjectiveDerived (coordinateQuadMinus (r + 2) F _
      ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F))),
      ψ' * β * ψ'⁻¹ = fieldAutT _ σ (coordinateQuadMinus_fieldMap_of_fixed (by omega)
        ((hσk (ι.rangeRestrictFieldEquiv b)).1 (ι.rangeRestrictFieldEquiv b).2)
        ((hσk (ι.rangeRestrictFieldEquiv c)).1 (ι.rangeRestrictFieldEquiv c).2))
  ·
    obtain ⟨ψ', hψ'⟩ := hc
    obtain ⟨Φ, hΦr, hΦ⟩ := exists_comp_incl_minus_eq hset.standardSetting hOut
      (by omega : 5 ≤ r + 2) hσk (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c) hirr₀
      (e.trans (minusCongr ι.rangeRestrictFieldEquiv (n := r + 2) (by omega) b c)) htC ht hinj hβ
      hψ'
    have hle : CFSG.conjugate G₀ h ≤ G₀ := by
      rw [← hrange, ← hΦr]
      refine range_le_of_comp_incl_minus_of_three_le hr hKc hq hirr e ι hσ hfix hC hG₀ (fun x => ?_)
      have h1 := hΦ (e.symm x)
      rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
      exact h1
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge
  ·
    exfalso
    simp only [not_exists] at hc
    apply hI (by omega) K F σ hσ hFK b c hirr _ _
      ((hσk (ι.rangeRestrictFieldEquiv b)).1 (ι.rangeRestrictFieldEquiv b).2)
      ((hσk (ι.rangeRestrictFieldEquiv c)).1 (ι.rangeRestrictFieldEquiv c).2) hirrF β hββ hc
    have hC' := SymplecticPilot.range_inf_centralizer_eq_map hinj hβ
    have hdvd := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer
      hset.standardSetting.standard e ht hKt (X := Ψ.range ⊓ centralizer ({t} : Set G)) inf_le_right
    rwa [hC', Subgroup.card_map_of_injective hinj] at hdvd

theorem unique_of_omegaMinusFieldRow_of_three_le {r f : ℕ}
    (hI : OmegaMinusInvolutionCentralizerInput (r + 2))
    (hset : SeitzSetting G L) (hr : 3 ≤ r) (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hC : ∀ k, MinusFieldCover e ι k) {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, minusNode (hC 0) j)
    (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) F (by omega)
      ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F))) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) :=
  F4Pilot.unique_of_forall_conjugate_eq fun h htM =>
    conjugate_eq_of_omegaMinusFieldRow_of_three_le hI hset hr hKc hq hirr e ht hKt ι hσ hfix hC hG₀
      ψ₀ h htM

end Unique

end CFSG.SeitzReduction.OmegaPilot
